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

/-- The canonical full lift has a first and a last dart. -/
theorem canonicalCappedPrimalLift_not_nil
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent) :
    ¬(walk.canonicalCappedPrimalLift hpositive hcoherent).Nil := by
  exact SimpleGraph.Walk.not_nil_iff_lt_length.mpr
    (walk.canonicalCappedPrimalLift_length_pos hpositive hcoherent)

/-- The first dart of the canonical full lift represents the first
line-graph vertex. -/
theorem canonicalCappedPrimalLift_firstDart_edge
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent)
    (hnil : ¬(walk.canonicalCappedPrimalLift
      hpositive hcoherent).Nil) :
    ((walk.canonicalCappedPrimalLift hpositive hcoherent).firstDart
      hnil).edge = first.1 := by
  let lifted := walk.canonicalCappedPrimalLift hpositive hcoherent
  have hmapNonempty : walk.support.map Subtype.val ≠ [] := by
    intro hnil
    exact walk.support_ne_nil (List.map_eq_nil_iff.mp hnil)
  calc
    (lifted.firstDart hnil).edge =
        lifted.edges.head (edges_eq_nil.not.mpr hnil) :=
      (lifted.edge_firstDart hnil).trans
        (lifted.mk_start_snd_eq_head_edges hnil)
    _ = (walk.support.map Subtype.val).head hmapNonempty := by
      dsimp only [lifted]
      simp only [walk.canonicalCappedPrimalLift_edges_eq_map_support
        hpositive hcoherent]
    _ = (walk.support.head walk.support_ne_nil).1 := List.head_map _
    _ = first.1 := by
      rw [List.head_eq_getElem_zero walk.support_ne_nil]
      exact congrArg Subtype.val walk.support_getElem_zero

/-- The last dart of the canonical full lift represents the final
line-graph vertex. -/
theorem canonicalCappedPrimalLift_lastDart_edge
    {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last)
    (hpositive : 0 < walk.length)
    (hcoherent : walk.IsPrimalCoherent)
    (hnil : ¬(walk.canonicalCappedPrimalLift
      hpositive hcoherent).Nil) :
    ((walk.canonicalCappedPrimalLift hpositive hcoherent).lastDart
      hnil).edge = last.1 := by
  let lifted := walk.canonicalCappedPrimalLift hpositive hcoherent
  have hmapNonempty : walk.support.map Subtype.val ≠ [] := by
    intro hnil
    exact walk.support_ne_nil (List.map_eq_nil_iff.mp hnil)
  calc
    (lifted.lastDart hnil).edge =
        lifted.edges.getLast (edges_eq_nil.not.mpr hnil) :=
      (lifted.edge_lastDart hnil).trans
        (lifted.mk_penultimate_end_eq_getLast_edges hnil)
    _ = (walk.support.map Subtype.val).getLast hmapNonempty := by
      dsimp only [lifted]
      simp only [walk.canonicalCappedPrimalLift_edges_eq_map_support
        hpositive hcoherent]
    _ = (walk.support.getLast walk.support_ne_nil).1 := List.getLast_map _
    _ = last.1 := by rw [walk.getLast_support]

end SimpleGraph.Walk
