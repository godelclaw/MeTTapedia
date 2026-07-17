import Mettapedia.GraphTheory.FourColor.GoertzelV24LineGraphOpenPrimalLift

namespace SimpleGraph.Walk

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Every internal junction of a capped primal lift occurs one position
after the corresponding vertex of the line-graph walk. -/
theorem cappedPrimalLift_getVert_succ
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
    (position : Fin walk.length) :
    (walk.cappedPrimalLift hpositive hcoherent startVertex endVertex
      hstartMem hendMem hstartNe hendNe).getVert (position.val + 1) =
      walk.lineGraphJunctionAt position := by
  let lift := walk.cappedPrimalLift hpositive hcoherent
    startVertex endVertex hstartMem hendMem hstartNe hendNe
  have hbound : position.val + 1 ≤ lift.length := by
    dsimp only [lift]
    rw [walk.cappedPrimalLift_length hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe]
    omega
  calc
    lift.getVert (position.val + 1) =
        lift.support[position.val + 1]'(by
          rw [lift.length_support]
          omega) :=
      lift.getVert_eq_support_getElem hbound
    _ = walk.lineGraphJunctionAt position := by
      simpa only [lift,
        walk.cappedPrimalLift_support hpositive hcoherent
          startVertex endVertex hstartMem hendMem hstartNe hendNe] using
        walk.cappedPrimalJunctionSupport_getElem_succ
          startVertex endVertex position

/-- The second vertex of a capped primal lift is its first line-graph
junction. -/
theorem cappedPrimalLift_snd
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
    (walk.cappedPrimalLift hpositive hcoherent startVertex endVertex
      hstartMem hendMem hstartNe hendNe).snd =
      walk.lineGraphJunctionAt ⟨0, hpositive⟩ := by
  simpa only [Nat.zero_add] using
    walk.cappedPrimalLift_getVert_succ hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe
      ⟨0, hpositive⟩

/-- The penultimate vertex of a capped primal lift is its last line-graph
junction. -/
theorem cappedPrimalLift_penultimate
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
    (walk.cappedPrimalLift hpositive hcoherent startVertex endVertex
      hstartMem hendMem hstartNe hendNe).penultimate =
      walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ := by
  have hlast := walk.cappedPrimalLift_getVert_succ
    hpositive hcoherent startVertex endVertex hstartMem hendMem
      hstartNe hendNe
      ⟨walk.length - 1,
        Nat.sub_lt hpositive Nat.zero_lt_one⟩
  change (walk.cappedPrimalLift hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe).getVert
        ((walk.cappedPrimalLift hpositive hcoherent
          startVertex endVertex hstartMem hendMem hstartNe hendNe).length - 1) = _
  rw [walk.cappedPrimalLift_length hpositive hcoherent
    startVertex endVertex hstartMem hendMem hstartNe hendNe]
  rw [show walk.length + 1 - 1 = walk.length by omega]
  have hlastIndex : walk.length - 1 + 1 = walk.length := by omega
  simpa only [hlastIndex] using hlast

/-- Removing the first edge of a walk of length at least two does not
change its penultimate vertex. -/
theorem tail_penultimate_eq_of_two_le {start finish : V}
    (walk : G.Walk start finish) (htwo : 2 ≤ walk.length) :
    walk.tail.penultimate = walk.penultimate := by
  cases walk with
  | nil => simp at htwo
  | cons first rest =>
      cases rest with
      | nil => simp at htwo
      | cons second rest => rfl

/-- Delete the two cap edges from a capped primal lift. The resulting
walk runs exactly between the first and last internal junctions. -/
noncomputable def cappedPrimalMiddleLift
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
    G.Walk
      (walk.lineGraphJunctionAt ⟨0, hpositive⟩)
      (walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩) :=
  let lift := walk.cappedPrimalLift hpositive hcoherent
    startVertex endVertex hstartMem hendMem hstartNe hendNe
  (lift.tail.dropLast).copy
    (walk.cappedPrimalLift_snd hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe)
    ((tail_penultimate_eq_of_two_le lift (by
        dsimp only [lift]
        rw [walk.cappedPrimalLift_length hpositive hcoherent
          startVertex endVertex hstartMem hendMem hstartNe hendNe]
        omega)).trans
      (walk.cappedPrimalLift_penultimate hpositive hcoherent
        startVertex endVertex hstartMem hendMem hstartNe hendNe))

@[simp] theorem cappedPrimalMiddleLift_length
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
    (walk.cappedPrimalMiddleLift hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe).length =
      walk.length - 1 := by
  simp only [cappedPrimalMiddleLift, length_copy, length_dropLast,
    tail, drop_length,
    walk.cappedPrimalLift_length hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe]
  omega

/-- The vertices of the trimmed lift are exactly the ordered junctions of
the original line-graph walk. -/
theorem cappedPrimalMiddleLift_getVert
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
    (position : Fin walk.length) :
    (walk.cappedPrimalMiddleLift hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe).getVert
        position.val = walk.lineGraphJunctionAt position := by
  let lift := walk.cappedPrimalLift hpositive hcoherent
    startVertex endVertex hstartMem hendMem hstartNe hendNe
  have htailLength : lift.tail.length = walk.length := by
    dsimp only [lift]
    simp only [tail, drop_length,
      walk.cappedPrimalLift_length hpositive hcoherent
        startVertex endVertex hstartMem hendMem hstartNe hendNe]
    omega
  simp only [cappedPrimalMiddleLift, getVert_copy, dropLast,
    take_getVert]
  rw [Nat.min_eq_right (by rw [htailLength]; omega)]
  rw [getVert_tail]
  exact walk.cappedPrimalLift_getVert_succ hpositive hcoherent
    startVertex endVertex hstartMem hendMem hstartNe hendNe position

/-- A line-graph interval of length at least two leaves a nonempty primal
middle segment after deleting the cap edges. -/
theorem cappedPrimalMiddleLift_not_nil
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (htwo : 2 ≤ walk.length)
    (hcoherent : walk.IsPrimalCoherent)
    (startVertex endVertex : V)
    (hstartMem : startVertex ∈ (first.1 : Sym2 V))
    (hendMem : endVertex ∈ (last.1 : Sym2 V))
    (hstartNe : startVertex ≠
      walk.lineGraphJunctionAt ⟨0, hpositive⟩)
    (hendNe : walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠ endVertex) :
    ¬(walk.cappedPrimalMiddleLift hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe).Nil := by
  apply not_nil_iff_lt_length.mpr
  rw [walk.cappedPrimalMiddleLift_length hpositive hcoherent
    startVertex endVertex hstartMem hendMem hstartNe hendNe]
  omega

/-- The first edge of the trimmed lift is the second represented
line-graph vertex. -/
theorem cappedPrimalMiddleLift_firstDart_edge
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (htwo : 2 ≤ walk.length)
    (hcoherent : walk.IsPrimalCoherent)
    (startVertex endVertex : V)
    (hstartMem : startVertex ∈ (first.1 : Sym2 V))
    (hendMem : endVertex ∈ (last.1 : Sym2 V))
    (hstartNe : startVertex ≠
      walk.lineGraphJunctionAt ⟨0, hpositive⟩)
    (hendNe : walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠ endVertex)
    (hnil : ¬(walk.cappedPrimalMiddleLift hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe).Nil) :
    ((walk.cappedPrimalMiddleLift hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe).firstDart
        hnil).edge = (walk.getVert 1).1 := by
  let middle := walk.cappedPrimalMiddleLift hpositive hcoherent
    startVertex endVertex hstartMem hendMem hstartNe hendNe
  have hsnd : middle.snd =
      walk.lineGraphJunctionAt ⟨1, by omega⟩ := by
    exact walk.cappedPrimalMiddleLift_getVert hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe
        ⟨1, by omega⟩
  calc
    (middle.firstDart hnil).edge =
        s(walk.lineGraphJunctionAt ⟨0, hpositive⟩, middle.snd) :=
      middle.edge_firstDart hnil
    _ = s(walk.lineGraphJunctionAt ⟨0, hpositive⟩,
          walk.lineGraphJunctionAt ⟨1, by omega⟩) := by
      rw [hsnd]
    _ = (walk.getVert 1).1 :=
      walk.pair_lineGraphJunctionAt_succ_eq_getVert_open
        0 (by omega) hcoherent

/-- The last edge of the trimmed lift is the penultimate represented
line-graph vertex. -/
theorem cappedPrimalMiddleLift_lastDart_edge
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (htwo : 2 ≤ walk.length)
    (hcoherent : walk.IsPrimalCoherent)
    (startVertex endVertex : V)
    (hstartMem : startVertex ∈ (first.1 : Sym2 V))
    (hendMem : endVertex ∈ (last.1 : Sym2 V))
    (hstartNe : startVertex ≠
      walk.lineGraphJunctionAt ⟨0, hpositive⟩)
    (hendNe : walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠ endVertex)
    (hnil : ¬(walk.cappedPrimalMiddleLift hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe).Nil) :
    ((walk.cappedPrimalMiddleLift hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe).lastDart
        hnil).edge = (walk.getVert (walk.length - 1)).1 := by
  let middle := walk.cappedPrimalMiddleLift hpositive hcoherent
    startVertex endVertex hstartMem hendMem hstartNe hendNe
  have hpenultimate : middle.penultimate =
      walk.lineGraphJunctionAt ⟨walk.length - 2, by omega⟩ := by
    change middle.getVert (middle.length - 1) = _
    have hlength : middle.length = walk.length - 1 := by
      exact walk.cappedPrimalMiddleLift_length hpositive hcoherent
        startVertex endVertex hstartMem hendMem hstartNe hendNe
    have hindex : middle.length - 1 = walk.length - 2 := by omega
    rw [hindex]
    exact walk.cappedPrimalMiddleLift_getVert hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe
        ⟨walk.length - 2, by omega⟩
  have hjunctionLast :
      (walk.lineGraphJunctionAt
        ⟨walk.length - 2 + 1, by omega⟩) =
      walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ := by
    apply congrArg walk.lineGraphJunctionAt
    apply Fin.ext
    dsimp only
    omega
  calc
    (middle.lastDart hnil).edge =
        s(middle.penultimate,
          walk.lineGraphJunctionAt
            ⟨walk.length - 1,
              Nat.sub_lt hpositive Nat.zero_lt_one⟩) :=
      middle.edge_lastDart hnil
    _ = s(walk.lineGraphJunctionAt ⟨walk.length - 2, by omega⟩,
          walk.lineGraphJunctionAt
            ⟨walk.length - 2 + 1, by omega⟩) := by
      rw [hpenultimate, hjunctionLast]
    _ = (walk.getVert (walk.length - 2 + 1)).1 :=
      walk.pair_lineGraphJunctionAt_succ_eq_getVert_open
        (walk.length - 2) (by omega) hcoherent
    _ = (walk.getVert (walk.length - 1)).1 := by
      congr 2
      omega

/-- Trimming cap edges preserves trailhood of a lifted line-graph path. -/
theorem cappedPrimalMiddleLift_isTrail_of_isPath
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
    (walk.cappedPrimalMiddleLift hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe).IsTrail := by
  rw [cappedPrimalMiddleLift, isTrail_copy]
  let lift := walk.cappedPrimalLift hpositive hcoherent
    startVertex endVertex hstartMem hendMem hstartNe hendNe
  exact isTrail_of_isSubwalk
    (lift.isSubwalk_rfl.tail.dropLast)
    (walk.cappedPrimalLift_isTrail_of_isPath hpositive hcoherent hpath
      startVertex endVertex hstartMem hendMem hstartNe hendNe)

/-- The trimmed lift traverses precisely the internal line-graph vertices,
with the two cap vertices removed from the represented support. -/
theorem cappedPrimalMiddleLift_edges_eq_map_support_tail_dropLast
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
    (walk.cappedPrimalMiddleLift hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe).edges =
      walk.support.tail.dropLast.map Subtype.val := by
  have htailLength : walk.support.tail.length = walk.length := by
    have hsupportLength := congrArg List.length walk.cons_tail_support
    rw [walk.length_support] at hsupportLength
    simp only [List.length_cons] at hsupportLength
    omega
  simp only [cappedPrimalMiddleLift, edges_copy, dropLast, edges_take,
    tail, edges_drop,
    walk.cappedPrimalLift_edges_eq_map_support hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe,
    drop_length,
    walk.cappedPrimalLift_length hpositive hcoherent
      startVertex endVertex hstartMem hendMem hstartNe hendNe,
    List.drop_one, List.dropLast_eq_take]
  rw [List.map_take]
  rw [List.map_tail]
  congr 1
  rw [htailLength]
  omega

end SimpleGraph.Walk
