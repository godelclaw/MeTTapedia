import Mettapedia.GraphTheory.FourColor.GoertzelV24LineGraphTrimmedPrimalLift

namespace SimpleGraph.Walk

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Delete only the first cap edge from a capped primal lift. The result
starts at the first line-graph junction and retains the terminal cap edge. -/
noncomputable def cappedPrimalTailLift
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent)
    (startVertex endVertex : V)
    (hstartMem : startVertex ∈ (first.1 : Sym2 V))
    (hendMem : endVertex ∈ (last.1 : Sym2 V))
    (hstartNe : startVertex ≠
      walk.lineGraphJunctionAt ⟨0, hpositive⟩)
    (hendNe : walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠ endVertex) :
    G.Walk (walk.lineGraphJunctionAt ⟨0, hpositive⟩) endVertex :=
  let lift := walk.cappedPrimalLift hpositive hcoherent
    startVertex endVertex hstartMem hendMem hstartNe hendNe
  lift.tail.copy
    (walk.cappedPrimalLift_snd hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe)
    rfl

@[simp] theorem cappedPrimalTailLift_length
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent)
    (startVertex endVertex : V)
    (hstartMem : startVertex ∈ (first.1 : Sym2 V))
    (hendMem : endVertex ∈ (last.1 : Sym2 V))
    (hstartNe : startVertex ≠
      walk.lineGraphJunctionAt ⟨0, hpositive⟩)
    (hendNe : walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠ endVertex) :
    (walk.cappedPrimalTailLift hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe).length =
      walk.length := by
  simp only [cappedPrimalTailLift, length_copy, tail, drop_length,
    walk.cappedPrimalLift_length hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe]
  omega

/-- A positive line-graph interval remains nonempty after deleting only
its first cap edge. -/
theorem cappedPrimalTailLift_not_nil
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent)
    (startVertex endVertex : V)
    (hstartMem : startVertex ∈ (first.1 : Sym2 V))
    (hendMem : endVertex ∈ (last.1 : Sym2 V))
    (hstartNe : startVertex ≠
      walk.lineGraphJunctionAt ⟨0, hpositive⟩)
    (hendNe : walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠ endVertex) :
    ¬(walk.cappedPrimalTailLift hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe).Nil := by
  apply not_nil_iff_lt_length.mpr
  rw [walk.cappedPrimalTailLift_length hpositive hcoherent
    startVertex endVertex hstartMem hendMem hstartNe hendNe]
  exact hpositive

/-- Removing one cap from the lift of a line-graph path preserves
edge-simple trailhood. -/
theorem cappedPrimalTailLift_isTrail_of_isPath
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent)
    (hpath : walk.IsPath)
    (startVertex endVertex : V)
    (hstartMem : startVertex ∈ (first.1 : Sym2 V))
    (hendMem : endVertex ∈ (last.1 : Sym2 V))
    (hstartNe : startVertex ≠
      walk.lineGraphJunctionAt ⟨0, hpositive⟩)
    (hendNe : walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠ endVertex) :
    (walk.cappedPrimalTailLift hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe).IsTrail := by
  rw [cappedPrimalTailLift, isTrail_copy]
  let lift := walk.cappedPrimalLift hpositive hcoherent
    startVertex endVertex hstartMem hendMem hstartNe hendNe
  exact isTrail_of_isSubwalk lift.isSubwalk_rfl.tail
    (walk.cappedPrimalLift_isTrail_of_isPath hpositive hcoherent hpath
      startVertex endVertex hstartMem hendMem hstartNe hendNe)

/-- The one-sided lift traverses exactly the represented support after
the first cap vertex. -/
theorem cappedPrimalTailLift_edges_eq_map_support_tail
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent)
    (startVertex endVertex : V)
    (hstartMem : startVertex ∈ (first.1 : Sym2 V))
    (hendMem : endVertex ∈ (last.1 : Sym2 V))
    (hstartNe : startVertex ≠
      walk.lineGraphJunctionAt ⟨0, hpositive⟩)
    (hendNe : walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠ endVertex) :
    (walk.cappedPrimalTailLift hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe).edges =
      walk.support.tail.map Subtype.val := by
  simp only [cappedPrimalTailLift, edges_copy, tail, edges_drop,
    walk.cappedPrimalLift_edges_eq_map_support hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe,
    List.drop_one, List.map_tail]

/-- The first edge left after deleting the initial cap is the second
represented line-graph vertex. -/
theorem cappedPrimalTailLift_firstDart_edge
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent)
    (startVertex endVertex : V)
    (hstartMem : startVertex ∈ (first.1 : Sym2 V))
    (hendMem : endVertex ∈ (last.1 : Sym2 V))
    (hstartNe : startVertex ≠
      walk.lineGraphJunctionAt ⟨0, hpositive⟩)
    (hendNe : walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠ endVertex)
    (hnil : ¬(walk.cappedPrimalTailLift hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe).Nil) :
    ((walk.cappedPrimalTailLift hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe).firstDart
        hnil).edge = (walk.getVert 1).1 := by
  let lifted := walk.cappedPrimalTailLift hpositive hcoherent
    startVertex endVertex hstartMem hendMem hstartNe hendNe
  have htailLength : walk.support.tail.length = walk.length := by
    have hsupportLength := congrArg List.length walk.cons_tail_support
    rw [walk.length_support] at hsupportLength
    simp only [List.length_cons] at hsupportLength
    omega
  have htailNonempty : walk.support.tail ≠ [] := by
    intro hnilSupport
    have := congrArg List.length hnilSupport
    rw [htailLength] at this
    simp only [List.length_nil] at this
    omega
  have hmapNonempty : walk.support.tail.map Subtype.val ≠ [] := by
    intro hmap
    exact htailNonempty (List.map_eq_nil_iff.mp hmap)
  calc
    (lifted.firstDart hnil).edge =
        lifted.edges.head (edges_eq_nil.not.mpr hnil) :=
      (lifted.edge_firstDart hnil).trans
        (lifted.mk_start_snd_eq_head_edges hnil)
    _ = (walk.support.tail.map Subtype.val).head (by
        exact hmapNonempty) := by
      dsimp only [lifted]
      simp only [walk.cappedPrimalTailLift_edges_eq_map_support_tail
        hpositive hcoherent startVertex endVertex hstartMem hendMem
        hstartNe hendNe]
    _ = (walk.support.tail.head htailNonempty).1 :=
      List.head_map _
    _ = (walk.getVert 1).1 := by
      rw [List.head_eq_getElem_zero htailNonempty]
      simpa only [List.getElem_tail] using
        congrArg Subtype.val
          (walk.getVert_eq_support_getElem (n := 1) (by omega)).symm

/-- The retained terminal cap is the last represented line-graph vertex. -/
theorem cappedPrimalTailLift_lastDart_edge
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent)
    (startVertex endVertex : V)
    (hstartMem : startVertex ∈ (first.1 : Sym2 V))
    (hendMem : endVertex ∈ (last.1 : Sym2 V))
    (hstartNe : startVertex ≠
      walk.lineGraphJunctionAt ⟨0, hpositive⟩)
    (hendNe : walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠ endVertex)
    (hnil : ¬(walk.cappedPrimalTailLift hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe).Nil) :
    ((walk.cappedPrimalTailLift hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe).lastDart
        hnil).edge = last.1 := by
  let lifted := walk.cappedPrimalTailLift hpositive hcoherent
    startVertex endVertex hstartMem hendMem hstartNe hendNe
  have htailNonempty : walk.support.tail ≠ [] := by
    intro hnilSupport
    have htailLength : walk.support.tail.length = walk.length := by
      have hsupportLength := congrArg List.length walk.cons_tail_support
      rw [walk.length_support] at hsupportLength
      simp only [List.length_cons] at hsupportLength
      omega
    have := congrArg List.length hnilSupport
    rw [htailLength] at this
    simp only [List.length_nil] at this
    omega
  have hmapNonempty : walk.support.tail.map Subtype.val ≠ [] := by
    intro hmap
    exact htailNonempty (List.map_eq_nil_iff.mp hmap)
  calc
    (lifted.lastDart hnil).edge =
        lifted.edges.getLast (edges_eq_nil.not.mpr hnil) :=
      (lifted.edge_lastDart hnil).trans
        (lifted.mk_penultimate_end_eq_getLast_edges hnil)
    _ = (walk.support.tail.map Subtype.val).getLast (by
        exact hmapNonempty) := by
      dsimp only [lifted]
      simp only [walk.cappedPrimalTailLift_edges_eq_map_support_tail
        hpositive hcoherent startVertex endVertex hstartMem hendMem
        hstartNe hendNe]
    _ = (walk.support.tail.getLast htailNonempty).1 :=
      List.getLast_map _
    _ = (walk.support.getLast walk.support_ne_nil).1 := by
      rw [List.getLast_tail htailNonempty]
    _ = last.1 := by
      rw [walk.getLast_support]

/-- Copying the endpoint indices of a line-graph walk does not change any
primal junction. -/
theorem lineGraphJunctionAt_copy
    {first last first' last' : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hfirst : first = first') (hlast : last = last')
    (position : Fin walk.length) :
    (walk.copy hfirst hlast).lineGraphJunctionAt
        ⟨position, by simpa only [length_copy] using position.isLt⟩ =
      walk.lineGraphJunctionAt position := by
  unfold lineGraphJunctionAt
  congr 1
  <;> simp only [getVert_copy]

/-- Dropping an initial interval from a line-graph walk does not change
its final primal junction, provided a step remains. -/
theorem lineGraphJunctionAt_drop_last
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last) (steps : Nat)
    (hremain : steps < walk.length) :
    (walk.drop steps).lineGraphJunctionAt
        ⟨(walk.drop steps).length - 1,
          Nat.sub_lt (by
            simp only [drop_length]
            omega) Nat.zero_lt_one⟩ =
      walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt (by omega) Nat.zero_lt_one⟩ := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · have hmem := walk.lineGraphJunctionAt_mem_left
      ⟨walk.length - 1, Nat.sub_lt (by omega) Nat.zero_lt_one⟩
    have hindex : steps + (walk.length - steps - 1) =
        walk.length - 1 := by omega
    simpa only [drop_length, drop_getVert, hindex] using hmem
  · have hmem := walk.lineGraphJunctionAt_mem_right
      ⟨walk.length - 1, Nat.sub_lt (by omega) Nat.zero_lt_one⟩
    have hindex : steps + (walk.length - steps - 1 + 1) =
        walk.length := by omega
    have hlast : walk.length - 1 + 1 = walk.length := by omega
    simpa only [drop_length, drop_getVert, hindex, hlast] using hmem

end SimpleGraph.Walk
