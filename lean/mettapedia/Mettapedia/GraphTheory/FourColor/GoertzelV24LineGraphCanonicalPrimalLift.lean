import Mettapedia.GraphTheory.FourColor.GoertzelV24LineGraphOneSidedPrimalLift

namespace SimpleGraph.Walk

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The endpoint of the last represented graph edge opposite the final
primal junction of a positive line-graph walk. -/
noncomputable def oppositeLastJunctionVertex
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length) : V :=
  Sym2.Mem.other (show walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ∈
      (last.1 : Sym2 V) by
    have member := walk.lineGraphJunctionAt_mem_right
      ⟨walk.length - 1,
        Nat.sub_lt hpositive Nat.zero_lt_one⟩
    have last_index : walk.length - 1 + 1 = walk.length := by omega
    simpa only [last_index, walk.getVert_length] using member)

/-- The opposite final-junction vertex lies on the last represented edge. -/
theorem oppositeLastJunctionVertex_mem
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length) :
    walk.oppositeLastJunctionVertex hpositive ∈ (last.1 : Sym2 V) := by
  unfold oppositeLastJunctionVertex
  exact Sym2.other_mem _

/-- Simplicity of graph edges separates the final junction from its
opposite cap endpoint. -/
theorem lineGraphJunctionAt_ne_oppositeLastJunctionVertex
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length) :
    walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠
      walk.oppositeLastJunctionVertex hpositive := by
  unfold oppositeLastJunctionVertex
  apply Ne.symm
  apply G.edge_other_ne last.2

/-- Canonical full primal lift: cap both ends by the endpoint opposite the
corresponding line-graph junction. -/
noncomputable def canonicalCappedPrimalLift
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent) :
    G.Walk (walk.oppositeFirstJunctionVertex hpositive)
      (walk.oppositeLastJunctionVertex hpositive) :=
  walk.cappedPrimalLift hpositive hcoherent
    (walk.oppositeFirstJunctionVertex hpositive)
    (walk.oppositeLastJunctionVertex hpositive)
    (walk.oppositeFirstJunctionVertex_mem hpositive)
    (walk.oppositeLastJunctionVertex_mem hpositive)
    (walk.oppositeFirstJunctionVertex_ne hpositive)
    (walk.lineGraphJunctionAt_ne_oppositeLastJunctionVertex hpositive)

@[simp] theorem canonicalCappedPrimalLift_length
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent) :
    (walk.canonicalCappedPrimalLift hpositive hcoherent).length =
      walk.length + 1 := by
  exact walk.cappedPrimalLift_length hpositive hcoherent
    (walk.oppositeFirstJunctionVertex hpositive)
    (walk.oppositeLastJunctionVertex hpositive)
    (walk.oppositeFirstJunctionVertex_mem hpositive)
    (walk.oppositeLastJunctionVertex_mem hpositive)
    (walk.oppositeFirstJunctionVertex_ne hpositive)
    (walk.lineGraphJunctionAt_ne_oppositeLastJunctionVertex hpositive)

/-- The canonical full lift traverses exactly the represented primal
edges, in line-path order. -/
theorem canonicalCappedPrimalLift_edges_eq_map_support
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent) :
    (walk.canonicalCappedPrimalLift hpositive hcoherent).edges =
      walk.support.map Subtype.val := by
  exact walk.cappedPrimalLift_edges_eq_map_support hpositive hcoherent
    (walk.oppositeFirstJunctionVertex hpositive)
    (walk.oppositeLastJunctionVertex hpositive)
    (walk.oppositeFirstJunctionVertex_mem hpositive)
    (walk.oppositeLastJunctionVertex_mem hpositive)
    (walk.oppositeFirstJunctionVertex_ne hpositive)
    (walk.lineGraphJunctionAt_ne_oppositeLastJunctionVertex hpositive)

/-- A canonical full lift of a positive simple coherent line path is a
nonempty primal trail. -/
theorem canonicalCappedPrimalLift_isTrail_of_isPath
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent)
    (hpath : walk.IsPath) :
    (walk.canonicalCappedPrimalLift hpositive hcoherent).IsTrail := by
  exact walk.cappedPrimalLift_isTrail_of_isPath hpositive hcoherent hpath
    (walk.oppositeFirstJunctionVertex hpositive)
    (walk.oppositeLastJunctionVertex hpositive)
    (walk.oppositeFirstJunctionVertex_mem hpositive)
    (walk.oppositeLastJunctionVertex_mem hpositive)
    (walk.oppositeFirstJunctionVertex_ne hpositive)
    (walk.lineGraphJunctionAt_ne_oppositeLastJunctionVertex hpositive)

theorem canonicalCappedPrimalLift_length_pos
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent) :
    0 < (walk.canonicalCappedPrimalLift hpositive hcoherent).length := by
  rw [walk.canonicalCappedPrimalLift_length hpositive hcoherent]
  omega

end SimpleGraph.Walk
