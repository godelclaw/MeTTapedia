import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnTransversal

/-!
# The complementary cycle of a residual return

A return chord has two carrier arcs between its endpoints.  The existing
separator closes the return along the linearly displayed interval.  This file
constructs the other closure intrinsically: rotate the carrier to the left
endpoint and retain the part after the right endpoint.  The construction is
independent of a drawing and will provide the opposite-side cycle for a
strictly nested return separator.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnComplementaryCycle

open AlternatingSiteGeometry
open GoertzelV24ResidualReturnArc
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open MatchingParity
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every cyclic coordinate names a vertex of the full carrier cycle, not
only of its tail representation. -/
theorem cycleVertexOrder_mem_cycle_support
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingComponentWitness G sigma first second)
    (position : CyclePosition sigma site) :
    (cycleVertexOrder sigma site position).1 ∈ site.cycle.support := by
  have htail : (cycleVertexOrder sigma site position).1 ∈
      site.cycle.tail.support :=
    (mem_cycle_tail_support_iff sigma site).2
      (cycleVertexOrder sigma site position).2
  have hsupport : first :: site.cycle.tail.support =
      site.cycle.support :=
    site.cycle.cons_support_tail site.cycle_isCycle.not_nil
  rw [← hsupport]
  exact List.mem_cons_of_mem _ htail

/-- Membership in the linearly displayed carrier interval is exactly
membership at a cyclic coordinate between its ordered endpoints.  This
coordinate form is the arithmetic interface used by strict nesting. -/
theorem mem_residualCycleInterval_support_iff
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingComponentWitness G sigma first second)
    {pairing : Pairing (CyclePosition sigma site)}
    (chord : OrderedReturnChord pairing) (vertex : V) :
    vertex ∈ (residualCycleInterval sigma site chord).support ↔
      ∃ position : CyclePosition sigma site,
        chord.left ≤ position ∧ position ≤ chord.right ∧
          vertex = (cycleVertexOrder sigma site position).1 := by
  constructor
  · intro hvertex
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hvertex with
      ⟨offset, hvalue, hoffset⟩
    have hoffset' : offset ≤ chord.right.val - chord.left.val := by
      rwa [residualCycleInterval_length sigma site chord] at hoffset
    let position : CyclePosition sigma site :=
      ⟨chord.left.val + offset, by
        have hright := chord.right.isLt
        omega⟩
    refine ⟨position, ?_, ?_, ?_⟩
    · change chord.left.val ≤ chord.left.val + offset
      omega
    · change chord.left.val + offset ≤ chord.right.val
      calc
        chord.left.val + offset ≤
            chord.left.val + (chord.right.val - chord.left.val) :=
          Nat.add_le_add_left hoffset' _
        _ = chord.right.val :=
          Nat.add_sub_of_le (Fin.mk_le_mk.mp chord.left_lt_right.le)
    · rw [cycleVertexOrder_val_eq_getVert]
      change vertex = site.cycle.tail.getVert (chord.left.val + offset)
      rw [← residualCycleInterval_getVert sigma site chord offset hoffset',
        hvalue]
  · rintro ⟨position, hleft, hright, rfl⟩
    let offset := position.val - chord.left.val
    have hoffset : offset ≤ chord.right.val - chord.left.val := by
      dsimp only [offset]
      exact Nat.sub_le_sub_right (Fin.mk_le_mk.mp hright) chord.left.val
    apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
    refine ⟨offset, ?_, ?_⟩
    · rw [residualCycleInterval_getVert sigma site chord offset hoffset,
        cycleVertexOrder_val_eq_getVert]
      congr
      dsimp only [offset]
      exact Nat.add_sub_of_le (Fin.mk_le_mk.mp hleft)
    · rwa [residualCycleInterval_length sigma site chord]

/-- A nonfinal cyclic coordinate is not the base vertex of the displayed
closed walk. -/
theorem cycleVertexOrder_ne_cycle_base_of_lt_tail_length
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingComponentWitness G sigma first second)
    (position : CyclePosition sigma site)
    (hposition : position.val < site.cycle.tail.length) :
    (cycleVertexOrder sigma site position).1 ≠ first := by
  intro heq
  have hget : site.cycle.tail.getVert position.val =
      site.cycle.tail.getVert site.cycle.tail.length := by
    rw [SimpleGraph.Walk.getVert_length]
    simpa only [cycleVertexOrder_val_eq_getVert] using heq
  have hindex := site.cycle_isCycle.isPath_tail.getVert_injOn
    (by simp only [Set.mem_setOf_eq]; omega)
    (by simp only [Set.mem_setOf_eq]; exact le_rfl) hget
  omega

/-- Before the final coordinate, the vertex's first occurrence in the full
closed-walk support is one position after its tail coordinate. -/
theorem cycle_support_idxOf_cycleVertexOrder
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingComponentWitness G sigma first second)
    (position : CyclePosition sigma site)
    (hposition : position.val < site.cycle.tail.length) :
    site.cycle.support.idxOf
        (cycleVertexOrder sigma site position).1 = position.val + 1 := by
  have hsupport : site.cycle.support = first :: site.cycle.tail.support :=
    (site.cycle.cons_support_tail site.cycle_isCycle.not_nil).symm
  rw [hsupport, List.idxOf_cons_ne _
    (cycleVertexOrder_ne_cycle_base_of_lt_tail_length
      sigma site position hposition).symm]
  change (site.cycle.tail.support.idxOf
    (site.cycle.tail.support.get position)).succ = position.val + 1
  rw [List.get_idxOf site.cycle_isCycle.isPath_tail.support_nodup position]

/-- The carrier arc complementary to the displayed interval of a return
chord.  It is oriented from the chord's right endpoint back to its left
endpoint, so it can close the ambient return path directly. -/
def complementaryCycleInterval
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingComponentWitness G sigma first second)
    {pairing : Pairing (CyclePosition sigma site)}
    (chord : OrderedReturnChord pairing) :
    G.Walk (cycleVertexOrder sigma site chord.right).1
      (cycleVertexOrder sigma site chord.left).1 := by
  let left := (cycleVertexOrder sigma site chord.left).1
  let right := (cycleVertexOrder sigma site chord.right).1
  have hleft : left ∈ site.cycle.support := by
    exact cycleVertexOrder_mem_cycle_support sigma site chord.left
  let rotated := site.cycle.rotate left hleft
  have hright : right ∈ rotated.support := by
    dsimp only [rotated]
    rw [SimpleGraph.Walk.mem_support_rotate_iff]
    simpa only [right] using
      cycleVertexOrder_mem_cycle_support sigma site chord.right
  exact rotated.dropUntil right hright

/-- The complementary carrier arc is literally the suffix beginning at the
right endpoint followed by the prefix ending at the left endpoint. -/
theorem complementaryCycleInterval_support
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingComponentWitness G sigma first second)
    {pairing : Pairing (CyclePosition sigma site)}
    (chord : OrderedReturnChord pairing) :
    (complementaryCycleInterval sigma site chord).support =
      site.cycle.tail.support.drop chord.right.val ++
        site.cycle.tail.support.take (chord.left.val + 1) := by
  have hsupportLength : site.cycle.tail.support.length =
      site.cycle.tail.length + 1 := site.cycle.tail.length_support
  have hleftTail : chord.left.val < site.cycle.tail.length := by
    have hright : chord.right.val < site.cycle.tail.length + 1 := by
      calc
        chord.right.val < site.cycle.tail.support.length := chord.right.isLt
        _ = site.cycle.tail.length + 1 := hsupportLength
    exact lt_of_lt_of_le (Fin.mk_lt_mk.mp chord.left_lt_right)
      (Nat.lt_succ_iff.mp hright)
  have hleft : (cycleVertexOrder sigma site chord.left).1 ∈
      site.cycle.support :=
    cycleVertexOrder_mem_cycle_support sigma site chord.left
  have hright : (cycleVertexOrder sigma site chord.right).1 ∈
      site.cycle.support :=
    cycleVertexOrder_mem_cycle_support sigma site chord.right
  have hcycleLength : site.cycle.length =
      site.cycle.tail.support.length := by
    rw [hsupportLength]
    exact (site.cycle.length_tail_add_one site.cycle_isCycle.not_nil).symm
  have hdropLeft :
      (site.cycle.dropUntil
        (cycleVertexOrder sigma site chord.left).1 hleft).support =
        site.cycle.tail.support.drop chord.left.val := by
    rw [SimpleGraph.Walk.dropUntil_eq_drop,
      SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.drop_support_eq_support_drop_min,
      cycle_support_idxOf_cycleVertexOrder sigma site chord.left hleftTail,
      Nat.min_eq_left]
    · rw [← site.cycle.cons_support_tail site.cycle_isCycle.not_nil]
      simp
    · rw [hcycleLength]
      have hleftBound := chord.left.isLt
      omega
  have htakeLeft :
      (site.cycle.takeUntil
        (cycleVertexOrder sigma site chord.left).1 hleft).support.tail =
        site.cycle.tail.support.take (chord.left.val + 1) := by
    rw [SimpleGraph.Walk.takeUntil_eq_take,
      SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_take,
      cycle_support_idxOf_cycleVertexOrder sigma site chord.left hleftTail,
      ← site.cycle.cons_support_tail site.cycle_isCycle.not_nil]
    simp
  let leftPart := site.cycle.tail.support.drop chord.left.val
  let leftOffset : Fin leftPart.length :=
    ⟨chord.right.val - chord.left.val, by
      dsimp only [leftPart]
      rw [List.length_drop]
      have hrightBound := chord.right.isLt
      omega⟩
  have hrightGet : leftPart.get leftOffset =
      (cycleVertexOrder sigma site chord.right).1 := by
    rw [cycleVertexOrder_apply_val]
    dsimp only [leftPart, leftOffset]
    simp only [List.get_eq_getElem, List.getElem_drop]
    congr
    exact Nat.add_sub_of_le (Fin.mk_le_mk.mp chord.left_lt_right.le)
  have hrightMemLeftPart :
      (cycleVertexOrder sigma site chord.right).1 ∈ leftPart := by
    rw [← hrightGet]
    exact List.get_mem _ _
  have hidxLeftPart : leftPart.idxOf
      (cycleVertexOrder sigma site chord.right).1 =
        chord.right.val - chord.left.val := by
    rw [← hrightGet,
      List.get_idxOf
        (site.cycle_isCycle.isPath_tail.support_nodup.drop
          (i := chord.left.val)) leftOffset]
  let rotated := site.cycle.rotate
    (cycleVertexOrder sigma site chord.left).1 hleft
  have hrotatedSupport : rotated.support = leftPart ++
      site.cycle.tail.support.take (chord.left.val + 1) := by
    dsimp only [rotated]
    rw [SimpleGraph.Walk.rotate, SimpleGraph.Walk.support_append,
      hdropLeft, htakeLeft]
  have hidxRotated : rotated.support.idxOf
      (cycleVertexOrder sigma site chord.right).1 =
        chord.right.val - chord.left.val := by
    rw [hrotatedSupport, List.idxOf_append_of_mem hrightMemLeftPart,
      hidxLeftPart]
  have hrightRotated : (cycleVertexOrder sigma site chord.right).1 ∈
      rotated.support := by
    rw [hrotatedSupport]
    exact List.mem_append_left _ hrightMemLeftPart
  unfold complementaryCycleInterval
  dsimp only
  rw [SimpleGraph.Walk.dropUntil_eq_drop,
    SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.drop_support_eq_support_drop_min,
    hidxRotated, Nat.min_eq_left, hrotatedSupport,
    List.drop_append_of_le_length]
  · dsimp only [leftPart]
    rw [List.drop_drop, Nat.add_sub_of_le
      (Fin.mk_le_mk.mp chord.left_lt_right.le)]
  · dsimp only [leftPart]
    rw [List.length_drop]
    exact Nat.sub_le_sub_right
      (Nat.le_of_lt chord.right.isLt) chord.left.val
  · rw [SimpleGraph.Walk.length_rotate, hcycleLength]
    have hrightBound := chord.right.isLt
    omega

/-- A carrier position strictly between a return's ordered endpoints lies on
the displayed interval and therefore not on its complementary interval. -/
theorem cycleVertexOrder_not_mem_complementaryCycleInterval_support
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingComponentWitness G sigma first second)
    {pairing : Pairing (CyclePosition sigma site)}
    (chord : OrderedReturnChord pairing)
    (position : CyclePosition sigma site)
    (hleft : chord.left < position) (hright : position < chord.right) :
    (cycleVertexOrder sigma site position).1 ∉
      (complementaryCycleInterval sigma site chord).support := by
  have hmem : (cycleVertexOrder sigma site position).1 ∈
      site.cycle.tail.support := by
    rw [cycleVertexOrder_apply_val]
    exact List.get_mem _ _
  have hidx : site.cycle.tail.support.idxOf
      (cycleVertexOrder sigma site position).1 = position.val := by
    rw [cycleVertexOrder_apply_val,
      List.get_idxOf site.cycle_isCycle.isPath_tail.support_nodup position]
  rw [complementaryCycleInterval_support]
  intro hin
  rcases List.mem_append.mp hin with hinSuffix | hinPrefix
  · have hinBeforeRight : (cycleVertexOrder sigma site position).1 ∈
        site.cycle.tail.support.take chord.right.val :=
      (List.mem_take_iff_idxOf_lt hmem).2 (hidx.trans_lt hright)
    exact (List.Pairwise.rel_of_mem_take_of_mem_drop
      site.cycle_isCycle.isPath_tail.support_nodup
      hinBeforeRight hinSuffix) rfl
  · have hinAfterLeft : (cycleVertexOrder sigma site position).1 ∈
        site.cycle.tail.support.drop (chord.left.val + 1) := by
      rw [List.mem_drop_iff_getElem]
      let offset := position.val - (chord.left.val + 1)
      have hsum : chord.left.val + 1 + offset = position.val := by
        dsimp only [offset]
        omega
      refine ⟨offset, ?_, ?_⟩
      · have hposition := position.isLt
        omega
      · exact (getElem_congr_idx hsum).trans
          (cycleVertexOrder_apply_val sigma site position).symm
    exact (List.Pairwise.rel_of_mem_take_of_mem_drop
      site.cycle_isCycle.isPath_tail.support_nodup hinPrefix hinAfterLeft) rfl

/-- The complementary carrier interval is a simple path. -/
theorem complementaryCycleInterval_isPath
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingComponentWitness G sigma first second)
    {pairing : Pairing (CyclePosition sigma site)}
    (chord : OrderedReturnChord pairing) :
    (complementaryCycleInterval sigma site chord).IsPath := by
  unfold complementaryCycleInterval
  dsimp only
  let rotated := site.cycle.rotate
    (cycleVertexOrder sigma site chord.left).1
    (cycleVertexOrder_mem_cycle_support sigma site chord.left)
  have hright : (cycleVertexOrder sigma site chord.right).1 ∈
      rotated.support := by
    dsimp only [rotated]
    rw [SimpleGraph.Walk.mem_support_rotate_iff]
    exact cycleVertexOrder_mem_cycle_support sigma site chord.right
  have hsplit : rotated.IsCycle := by
    simpa only [rotated] using site.cycle_isCycle.rotate
      (cycleVertexOrder_mem_cycle_support sigma site chord.left)
  rw [← rotated.take_spec hright] at hsplit
  apply hsplit.isPath_of_append_right
  apply SimpleGraph.Walk.not_nil_of_ne
  intro heq
  apply ne_of_lt chord.left_lt_right
  apply (cycleVertexOrder sigma site).injective
  exact Subtype.ext heq

/-- Every vertex of the complementary interval remains on the carrier. -/
theorem mem_carrier_of_mem_complementaryCycleInterval_support
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingComponentWitness G sigma first second)
    {pairing : Pairing (CyclePosition sigma site)}
    (chord : OrderedReturnChord pairing) {vertex : V}
    (hvertex : vertex ∈ (complementaryCycleInterval sigma site chord).support) :
    vertex ∈ site.carrier := by
  unfold complementaryCycleInterval at hvertex
  dsimp only at hvertex
  have hinRotated : vertex ∈
      (site.cycle.rotate
        (cycleVertexOrder sigma site chord.left).1
        (cycleVertexOrder_mem_cycle_support sigma site chord.left)).support := by
    apply SimpleGraph.Walk.support_dropUntil_subset_support _ _ hvertex
  have hinCycle : vertex ∈ site.cycle.support := by
    simpa only [SimpleGraph.Walk.mem_support_rotate_iff] using hinRotated
  have hinCycleFinset : vertex ∈ site.cycle.support.toFinset :=
    List.mem_toFinset.2 hinCycle
  rw [site.cycle_support_eq] at hinCycleFinset
  exact hinCycleFinset

/-- Every edge of the complementary carrier interval is an edge of the full
carrier cycle. -/
theorem mem_cycle_edges_of_mem_complementaryCycleInterval_edges
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingComponentWitness G sigma first second)
    {pairing : Pairing (CyclePosition sigma site)}
    (chord : OrderedReturnChord pairing) {edge : Sym2 V}
    (hedge : edge ∈ (complementaryCycleInterval sigma site chord).edges) :
    edge ∈ site.cycle.edges := by
  unfold complementaryCycleInterval at hedge
  dsimp only at hedge
  let left := (cycleVertexOrder sigma site chord.left).1
  have hleft : left ∈ site.cycle.support :=
    cycleVertexOrder_mem_cycle_support sigma site chord.left
  let rotated := site.cycle.rotate left hleft
  have hrotated : edge ∈ rotated.edges := by
    exact rotated.edges_dropUntil_subset_edges _ hedge
  exact (site.cycle.rotate_edges left hleft).mem_iff.mp hrotated

/-- Close a physical return along the complementary carrier arc. -/
def complementaryReturnCycle
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingComponentWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site)) :
    G.Walk (cycleVertexOrder sigma site chord.left).1
      (cycleVertexOrder sigma site chord.left).1 :=
  (orderedChordAmbientPath hG sigma hSigma site chord).append
    (complementaryCycleInterval sigma site chord)

/-- The complementary closure's nondegeneracy condition is automatic in a
simple graph.  If both constituent paths had one edge, they would be the
same edge between the same endpoints; but the physical return lies in the
residual graph while the complementary interval lies on the carrier. -/
theorem complementaryReturnCycle_length_alternative
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingComponentWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site)) :
    1 < (orderedChordAmbientPath hG sigma hSigma site chord).length ∨
      1 < (complementaryCycleInterval sigma site chord).length := by
  let physical := orderedChordAmbientPath hG sigma hSigma site chord
  let carrier := complementaryCycleInterval sigma site chord
  have hphysicalNotNil : ¬physical.Nil := by
    simpa only [physical] using
      orderedChordAmbientPath_not_nil hG sigma hSigma site chord
  have hcarrierNotNil : ¬carrier.Nil := by
    dsimp only [carrier]
    apply SimpleGraph.Walk.not_nil_of_ne
    intro heq
    apply ne_of_lt chord.left_lt_right
    apply (cycleVertexOrder sigma site).injective
    exact Subtype.ext heq.symm
  by_contra hlong
  simp only [not_or, not_lt] at hlong
  have hphysicalLength : physical.length = 1 := by
    have hpositive := SimpleGraph.Walk.not_nil_iff_lt_length.mp hphysicalNotNil
    have hle : physical.length ≤ 1 := by
      simpa only [physical] using hlong.1
    omega
  have hcarrierLength : carrier.length = 1 := by
    have hpositive := SimpleGraph.Walk.not_nil_iff_lt_length.mp hcarrierNotNil
    have hle : carrier.length ≤ 1 := by
      simpa only [carrier] using hlong.2
    omega
  have heq : physical = carrier.reverse :=
    SimpleGraph.Walk.eq_of_length_le_one hlong.1 (by
      rw [SimpleGraph.Walk.length_reverse, hcarrierLength])
  let edge := (physical.firstDart hphysicalNotNil).edge
  have hedgePhysical : edge ∈ physical.edges := by
    simpa only [edge, physical.edge_firstDart] using
      physical.mk_start_snd_mem_edges hphysicalNotNil
  have hedgeCarrier : edge ∈ carrier.edges := by
    rw [heq, SimpleGraph.Walk.edges_reverse, List.mem_reverse] at hedgePhysical
    exact hedgePhysical
  have hedgeCycle : edge ∈ site.cycle.edges := by
    exact mem_cycle_edges_of_mem_complementaryCycleInterval_edges
      sigma site chord hedgeCarrier
  have hedgeReturn : edge ∈
      (orderedReturnPath hG sigma hSigma site chord.left).edges := by
    simpa only [physical, orderedChordAmbientPath, orderedAmbientReturnPath,
      SimpleGraph.Walk.edges_copy,
      SimpleGraph.Walk.edges_mapLe_eq_edges] using hedgePhysical
  exact (orderedReturnPath_edge_not_cycle hG sigma hSigma site
    chord.left hedgeReturn) hedgeCycle

/-- The complementary closure is a simple cycle whenever one of its two
constituent paths has more than one edge.  The disjointness proof uses only
that a residual return meets the carrier at its two endpoints. -/
theorem complementaryReturnCycle_isCycle
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingComponentWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (hlong :
      1 < (orderedChordAmbientPath hG sigma hSigma site chord).length ∨
        1 < (complementaryCycleInterval sigma site chord).length) :
    (complementaryReturnCycle hG sigma hSigma site chord).IsCycle := by
  have hreturn := orderedChordAmbientPath_isPath
    hG sigma hSigma site chord
  have hcomplement := complementaryCycleInterval_isPath sigma site chord
  unfold complementaryReturnCycle
  apply hreturn.isCycle_append hcomplement
  · rw [List.disjoint_left]
    intro vertex hreturnTail hcomplementTail
    have hreturnSupport : vertex ∈
        (orderedChordAmbientPath hG sigma hSigma site chord).support :=
      List.mem_of_mem_tail hreturnTail
    have hcarrier : vertex ∈ site.carrier :=
      mem_carrier_of_mem_complementaryCycleInterval_support
        sigma site chord (List.mem_of_mem_tail hcomplementTail)
    rcases
        eq_left_or_eq_right_of_mem_orderedChordAmbientPath_support_of_mem_carrier
          hG sigma hSigma site chord hreturnSupport hcarrier with
      hleft | hright
    · have hleftNot :
          (cycleVertexOrder sigma site chord.left).1 ∉
            (orderedChordAmbientPath hG sigma hSigma site chord).support.tail := by
        have hnodup := hreturn.support_nodup
        rw [← (orderedChordAmbientPath hG sigma hSigma site chord).cons_tail_support]
          at hnodup
        exact (List.nodup_cons.mp hnodup).1
      exact hleftNot (hleft ▸ hreturnTail)
    · have hrightNot :
          (cycleVertexOrder sigma site chord.right).1 ∉
            (complementaryCycleInterval sigma site chord).support.tail := by
        have hnodup := hcomplement.support_nodup
        rw [← (complementaryCycleInterval sigma site chord).cons_tail_support]
          at hnodup
        exact (List.nodup_cons.mp hnodup).1
      exact hrightNot (hright ▸ hcomplementTail)
  · exact hlong

/-- Strictly nested returns give the two disjoint cycles needed for a cyclic
cut: the outer return is closed along the complementary carrier arc, while
the inner return is closed along its displayed carrier interval. -/
theorem complementaryReturnCycle_support_disjoint_orderedReturnSeparator
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingComponentWitness G sigma first second)
    (outer inner : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (hleft : outer.left < inner.left)
    (hright : inner.right < outer.right) :
    (complementaryReturnCycle hG sigma hSigma site outer).support.Disjoint
      (orderedReturnSeparator hG sigma hSigma site inner).support := by
  have hne : outer ≠ inner := by
    intro heq
    subst inner
    exact (lt_irrefl outer.left) hleft
  have hpathDisjoint := orderedChordAmbientPath_support_disjoint_of_ne
    hG sigma hSigma site outer inner hne
  rw [List.disjoint_left] at hpathDisjoint ⊢
  intro vertex houter hinner
  unfold complementaryReturnCycle at houter
  unfold orderedReturnSeparator at hinner
  rw [SimpleGraph.Walk.support_append] at houter hinner
  rcases List.mem_append.mp houter with houterPath | houterComplement
  · rcases List.mem_append.mp hinner with hinnerPath | hinnerInterval
    · exact hpathDisjoint houterPath hinnerPath
    · have hinnerInterval' : vertex ∈
          (residualCycleInterval sigma site inner).support := by
        have : vertex ∈
            (residualCycleInterval sigma site inner).reverse.support :=
          List.mem_of_mem_tail hinnerInterval
        simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using this
      have hcarrier := mem_carrier_of_mem_residualCycleInterval_support
        sigma site inner hinnerInterval'
      rcases
          eq_left_or_eq_right_of_mem_orderedChordAmbientPath_support_of_mem_carrier
            hG sigma hSigma site outer houterPath hcarrier with
        houterEndpoint | houterEndpoint
      · rcases (mem_residualCycleInterval_support_iff
            sigma site inner vertex).1 hinnerInterval' with
          ⟨position, hinnerLeft, _hinnerRight, hposition⟩
        have heq : outer.left = position :=
          (cycleVertexOrder sigma site).injective
            (Subtype.ext (houterEndpoint.symm.trans hposition))
        subst position
        exact (not_le_of_gt hleft) hinnerLeft
      · rcases (mem_residualCycleInterval_support_iff
            sigma site inner vertex).1 hinnerInterval' with
          ⟨position, _hinnerLeft, hinnerRight, hposition⟩
        have heq : outer.right = position :=
          (cycleVertexOrder sigma site).injective
            (Subtype.ext (houterEndpoint.symm.trans hposition))
        subst position
        exact (not_le_of_gt hright) hinnerRight
  · have houterComplement' : vertex ∈
        (complementaryCycleInterval sigma site outer).support :=
      List.mem_of_mem_tail houterComplement
    rcases List.mem_append.mp hinner with hinnerPath | hinnerInterval
    · have hcarrier : vertex ∈ site.carrier :=
        mem_carrier_of_mem_complementaryCycleInterval_support
          sigma site outer houterComplement'
      rcases
          eq_left_or_eq_right_of_mem_orderedChordAmbientPath_support_of_mem_carrier
            hG sigma hSigma site inner hinnerPath hcarrier with
        hinnerEndpoint | hinnerEndpoint
      · have hnot :=
          cycleVertexOrder_not_mem_complementaryCycleInterval_support
            sigma site outer inner.left hleft
              (lt_trans inner.left_lt_right hright)
        exact hnot (hinnerEndpoint ▸ houterComplement')
      · have hnot :=
          cycleVertexOrder_not_mem_complementaryCycleInterval_support
            sigma site outer inner.right
              (lt_trans hleft inner.left_lt_right) hright
        exact hnot (hinnerEndpoint ▸ houterComplement')
    · have hinnerInterval' : vertex ∈
          (residualCycleInterval sigma site inner).support := by
        have : vertex ∈
            (residualCycleInterval sigma site inner).reverse.support :=
          List.mem_of_mem_tail hinnerInterval
        simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using this
      rcases (mem_residualCycleInterval_support_iff
          sigma site inner vertex).1 hinnerInterval' with
        ⟨position, hinnerLeft, hinnerRight, hposition⟩
      have hnot :=
        cycleVertexOrder_not_mem_complementaryCycleInterval_support
          sigma site outer position
            (lt_of_lt_of_le hleft hinnerLeft)
            (lt_of_le_of_lt hinnerRight hright)
      exact hnot (hposition ▸ houterComplement')

end

end Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnComplementaryCycle
