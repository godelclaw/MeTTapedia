import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapDeletedBoundaryCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoPentagonCapOpeningBoundary

/-!
# Facial cap cycles under a simultaneous two-cap deletion

C-2 computes the capped deleted-side face cycle of one facial pentagon.  The
literal annular opening deletes two remote pentagon supports at once.  This
module proves the local stability needed for that simultaneous carrier: any
larger deleted set which contains the cap but avoids its five outward spoke
endpoints has the same two-step deleted-face calculation at that cap.

The final specialization applies this to both members of a
`FacialPentagonCapBoundaryWalkPair`.  It proves two five-port cycles in the
literal union carrier.  It does not assert that the cycles are distinct or
construct the source corridor's remote facial separation; those are separate
C-3/C-4 obligations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FacialPentagonCapPairDeletedCycle

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24FacialPentagonCap
open GoertzelV24FacialPentagonCapDeletedBoundaryCycle
open GoertzelV24FaceDualConnectedness
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24PentagonCapOpening
open GoertzelV24TwoPentagonCapOpening

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

namespace FacialPentagonCapBoundaryWalk

variable {data : Data G}

private abbrev capOf (walk : FacialPentagonCapBoundaryWalk data) : PentagonCap G :=
  walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap

/-- A named cap-side spoke, regarded as an exposed dart after deleting the cap
and one additional vertex set. -/
def extendedCapDeletedBoundaryDart
    (walk : FacialPentagonCapBoundaryWalk data)
    (deleted : Finset V)
    (hcap : (capOf walk).vertexSupport ⊆ deleted)
    (hspoke : ∀ step : Fin 5, (capOf walk).spokeOuter step ∉ deleted)
    (step : Fin 5) :
    DeletedBoundaryHalfDart data.toRotationSystem deleted where
  val :=
    ⟨(capDeletedBoundaryDart data (capOf walk) step).1.1,
      hcap (capDeletedBoundaryDart data (capOf walk) step).1.2⟩
  property := by
    change (capDeletedBoundaryDart data (capOf walk) step).1.1.snd ∉ deleted
    rw [capDeletedBoundaryDart_snd]
    exact hspoke step

@[simp] theorem extendedCapDeletedBoundaryDart_val
    (walk : FacialPentagonCapBoundaryWalk data)
    (deleted : Finset V)
    (hcap : (capOf walk).vertexSupport ⊆ deleted)
    (hspoke : ∀ step : Fin 5, (capOf walk).spokeOuter step ∉ deleted)
    (step : Fin 5) :
    (extendedCapDeletedBoundaryDart walk deleted hcap hspoke step).1.1 =
      (capDeletedBoundaryDart data (capOf walk) step).1.1 :=
  rfl

/-- The cap-internal dart remains based in the enlarged deleted carrier. -/
def extendedCapInternalFaceDart
    (walk : FacialPentagonCapBoundaryWalk data)
    (deleted : Finset V)
    (hcap : (capOf walk).vertexSupport ⊆ deleted)
    (step : Fin 5) :
    DeletedBasedDart data.toRotationSystem deleted where
  val := (capInternalFaceDart walk step).1
  property := hcap (capInternalFaceDart walk step).2

@[simp] theorem extendedCapInternalFaceDart_val
    (walk : FacialPentagonCapBoundaryWalk data)
    (deleted : Finset V)
    (hcap : (capOf walk).vertexSupport ⊆ deleted)
    (step : Fin 5) :
    (extendedCapInternalFaceDart walk deleted hcap step).1 =
      (capInternalFaceDart walk step).1 :=
  rfl

/-- The opposite endpoint of the internal cap dart remains in the enlarged
deleted carrier. -/
theorem extendedCapInternalFaceDart_alpha_mem
    (walk : FacialPentagonCapBoundaryWalk data)
    (deleted : Finset V)
    (hcap : (capOf walk).vertexSupport ⊆ deleted)
    (step : Fin 5) :
    data.toRotationSystem.vertOf
        (data.toRotationSystem.alpha
          (extendedCapInternalFaceDart walk deleted hcap step).1) ∈ deleted :=
  hcap (capInternalFaceDart_alpha_mem_vertexSupport walk step)

/-- The first deleted-face step is unchanged by the remote deletion. -/
theorem deletedFacePerm_extendedBoundary_eq_internal
    (walk : FacialPentagonCapBoundaryWalk data)
    (deleted : Finset V)
    (hcap : (capOf walk).vertexSupport ⊆ deleted)
    (hspoke : ∀ step : Fin 5, (capOf walk).spokeOuter step ∉ deleted)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (step : Fin 5) :
    deletedFacePerm data.toRotationSystem deleted
        (extendedCapDeletedBoundaryDart walk deleted hcap hspoke step).1 =
      extendedCapInternalFaceDart walk deleted hcap step := by
  apply Subtype.ext
  rw [deletedFacePerm, Equiv.Perm.mul_apply, deletedRho_val,
    deletedAlpha_apply_boundary data.toRotationSystem
      deleted
      (extendedCapDeletedBoundaryDart walk deleted hcap hspoke step).1
      (extendedCapDeletedBoundaryDart walk deleted hcap hspoke step).2]
  exact rho_capDeletedBoundaryDart_eq_alpha_boundaryPred
    walk (fun capStep : Fin 5 => hcubic ((capOf walk).vertex capStep))
      hrotation step

/-- The second deleted-face step exits through the preceding named spoke also
in the simultaneous carrier. -/
theorem deletedFacePerm_extendedInternal_eq_previousBoundary
    (walk : FacialPentagonCapBoundaryWalk data)
    (deleted : Finset V)
    (hcap : (capOf walk).vertexSupport ⊆ deleted)
    (hspoke : ∀ step : Fin 5, (capOf walk).spokeOuter step ∉ deleted)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (step : Fin 5) :
    deletedFacePerm data.toRotationSystem deleted
        (extendedCapInternalFaceDart walk deleted hcap step) =
      (extendedCapDeletedBoundaryDart walk deleted hcap hspoke (step - 1)).1 := by
  apply Subtype.ext
  rw [deletedFacePerm, Equiv.Perm.mul_apply, deletedRho_val,
    deletedAlpha_apply_internal data.toRotationSystem
      deleted
      (extendedCapInternalFaceDart walk deleted hcap step)
      (extendedCapInternalFaceDart_alpha_mem walk deleted hcap step),
    extendedCapInternalFaceDart_val,
    capInternalFaceDart_val, data.toRotationSystem.alpha_involutive]
  exact rho_boundaryDart_eq_capDeletedBoundaryDart
    walk (fun capStep : Fin 5 => hcubic ((capOf walk).vertex capStep)) hrotation
      (step - 1)

/-- Two simultaneous deleted-face steps advance once around the cap. -/
theorem deletedFacePerm_sq_extendedBoundary_eq_previous
    (walk : FacialPentagonCapBoundaryWalk data)
    (deleted : Finset V)
    (hcap : (capOf walk).vertexSupport ⊆ deleted)
    (hspoke : ∀ step : Fin 5, (capOf walk).spokeOuter step ∉ deleted)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (step : Fin 5) :
    (deletedFacePerm data.toRotationSystem
      deleted ^ 2)
        (extendedCapDeletedBoundaryDart walk deleted hcap hspoke step).1 =
      (extendedCapDeletedBoundaryDart walk deleted hcap hspoke (step - 1)).1 := by
  rw [pow_two, Equiv.Perm.mul_apply,
    deletedFacePerm_extendedBoundary_eq_internal
      walk deleted hcap hspoke hcubic hrotation step,
    deletedFacePerm_extendedInternal_eq_previousBoundary
      walk deleted hcap hspoke hcubic hrotation step]

/-- All five cap ports remain one actual deleted-face cycle after adjoining a
remote deletion. -/
theorem extendedCapDeletedBoundaryDart_sameCycle
    (walk : FacialPentagonCapBoundaryWalk data)
    (deleted : Finset V)
    (hcap : (capOf walk).vertexSupport ⊆ deleted)
    (hspoke : ∀ step : Fin 5, (capOf walk).spokeOuter step ∉ deleted)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (first second : Fin 5) :
    (deletedFacePerm data.toRotationSystem
      deleted).SameCycle
        (extendedCapDeletedBoundaryDart walk deleted hcap hspoke first).1
        (extendedCapDeletedBoundaryDart walk deleted hcap hspoke second).1 := by
  let f := deletedFacePerm data.toRotationSystem
    deleted
  have previous (step : Fin 5) : f.SameCycle
      (extendedCapDeletedBoundaryDart walk deleted hcap hspoke step).1
      (extendedCapDeletedBoundaryDart walk deleted hcap hspoke (step - 1)).1 := by
    have hsq := deletedFacePerm_sq_extendedBoundary_eq_previous
      walk deleted hcap hspoke hcubic hrotation step
    change (f ^ 2) _ = _ at hsq
    have hp : (f ^ 2).SameCycle
        ((f ^ 2) (extendedCapDeletedBoundaryDart walk deleted hcap hspoke step).1)
        (extendedCapDeletedBoundaryDart walk deleted hcap hspoke (step - 1)).1 :=
      hsq.sameCycle (f ^ 2)
    exact Equiv.Perm.sameCycle_pow_left.mp (Equiv.Perm.SameCycle.of_pow hp)
  have fromZero (step : Fin 5) : f.SameCycle
      (extendedCapDeletedBoundaryDart walk deleted hcap hspoke 0).1
      (extendedCapDeletedBoundaryDart walk deleted hcap hspoke step).1 := by
    fin_cases step
    · exact Equiv.Perm.SameCycle.rfl
    · exact (previous 1).symm
    · exact (previous 0).trans ((previous 4).trans (previous 3))
    · exact (previous 0).trans (previous 4)
    · exact previous 0
  exact (fromZero first).symm.trans (fromZero second)

end FacialPentagonCapBoundaryWalk

namespace FacialPentagonCapBoundaryWalkPair

variable {data : Data G}

private theorem innerSupport_subset_deleted
    (caps : FacialPentagonCapBoundaryWalkPair data) :
    caps.inner.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport ⊆
      caps.toPentagonCapPair.deletedVertexSupport := by
  intro vertex hvertex
  exact Finset.mem_union_left _ hvertex

private theorem outerSupport_subset_deleted
    (caps : FacialPentagonCapBoundaryWalkPair data) :
    caps.outer.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport ⊆
      caps.toPentagonCapPair.deletedVertexSupport := by
  intro vertex hvertex
  exact Finset.mem_union_right _ hvertex

private theorem innerSpoke_not_mem_deleted
    (caps : FacialPentagonCapBoundaryWalkPair data) (step : Fin 5) :
    caps.inner.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.spokeOuter step ∉
      caps.toPentagonCapPair.deletedVertexSupport := by
  rw [PentagonCapPair.deletedVertexSupport, Finset.mem_union, not_or]
  exact ⟨caps.inner.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.spokeOuter_not_mem_vertexSupport step,
    caps.inner_spokeOuter_not_mem_outerSupport step⟩

private theorem outerSpoke_not_mem_deleted
    (caps : FacialPentagonCapBoundaryWalkPair data) (step : Fin 5) :
    caps.outer.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.spokeOuter step ∉
      caps.toPentagonCapPair.deletedVertexSupport := by
  rw [PentagonCapPair.deletedVertexSupport, Finset.mem_union, not_or]
  exact ⟨caps.outer_spokeOuter_not_mem_innerSupport step,
    caps.outer.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.spokeOuter_not_mem_vertexSupport step⟩

/-- The graph-level separation fields prohibit even an ambient edge directly
joining an inner cap vertex to an outer cap vertex. -/
theorem not_adj_inner_outerVertices
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (innerStep outerStep : Fin 5) :
    ¬ G.Adj
      (caps.toPentagonCapPair.inner.vertex innerStep)
      (caps.toPentagonCapPair.outer.vertex outerStep) := by
  intro hadj
  let edge : G.edgeSet :=
    ⟨s(caps.toPentagonCapPair.inner.vertex innerStep,
       caps.toPentagonCapPair.outer.vertex outerStep), by simpa using hadj⟩
  have hnotRemoved : edge.1 ∉
      edgeFinsetValueSet caps.toPentagonCapPair.cycleSupport := by
    intro hremoved
    rcases (mem_edgeFinsetValueSet_iff
      caps.toPentagonCapPair.cycleSupport edge.1).mp hremoved with
      ⟨removed, hsupport, hvalue⟩
    rw [PentagonCapPair.cycleSupport, Finset.mem_union] at hsupport
    rcases hsupport with hinner | houter
    · rcases Finset.mem_map.mp hinner with ⟨step, -, hstep⟩
      have heq : (caps.toPentagonCapPair.inner.cycleEdge step).1 = edge.1 := by
        calc
          _ = removed.1 := congrArg Subtype.val hstep
          _ = edge.1 := hvalue
      have hendpoint : caps.toPentagonCapPair.outer.vertex outerStep ∈
          (caps.toPentagonCapPair.inner.cycleEdge step).1 := by
        rw [heq]
        simp [edge]
      rcases caps.toPentagonCapPair.inner.cycleEdge_endpoint_eq_vertex
          step _ hendpoint with ⟨capStep, hcapStep⟩
      exact caps.toPentagonCapPair.outer_vertex_not_mem_innerSupport outerStep
        ((caps.toPentagonCapPair.inner.mem_vertexSupport_iff _).mpr
          ⟨capStep, hcapStep⟩)
    · rcases Finset.mem_map.mp houter with ⟨step, -, hstep⟩
      have heq : (caps.toPentagonCapPair.outer.cycleEdge step).1 = edge.1 := by
        calc
          _ = removed.1 := congrArg Subtype.val hstep
          _ = edge.1 := hvalue
      have hendpoint : caps.toPentagonCapPair.inner.vertex innerStep ∈
          (caps.toPentagonCapPair.outer.cycleEdge step).1 := by
        rw [heq]
        simp [edge]
      rcases caps.toPentagonCapPair.outer.cycleEdge_endpoint_eq_vertex
          step _ hendpoint with ⟨capStep, hcapStep⟩
      exact caps.toPentagonCapPair.inner_vertex_not_mem_outerSupport innerStep
        ((caps.toPentagonCapPair.outer.mem_vertexSupport_iff _).mpr
          ⟨capStep, hcapStep⟩)
  have hopen : caps.toPentagonCapPair.openGraph.Adj
      (caps.toPentagonCapPair.inner.vertex innerStep)
      (caps.toPentagonCapPair.outer.vertex outerStep) := by
    change (G.deleteEdges
      (edgeFinsetValueSet caps.toPentagonCapPair.cycleSupport)).Adj _ _
    exact (SimpleGraph.deleteEdges_adj).2 ⟨hadj, hnotRemoved⟩
  exact caps.toPentagonCapPair.not_openGraph_adj_inner_outerVertices
    innerStep outerStep hopen

/-- The simultaneous capped deleted-face permutation preserves the inner cap
component. -/
theorem deletedFacePerm_preserves_innerSupport
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (dart : DeletedBasedDart data.toRotationSystem
      caps.toPentagonCapPair.deletedVertexSupport)
    (hinner : data.toRotationSystem.vertOf dart.1 ∈
      caps.toPentagonCapPair.inner.vertexSupport) :
    data.toRotationSystem.vertOf
        (deletedFacePerm data.toRotationSystem
          caps.toPentagonCapPair.deletedVertexSupport dart).1 ∈
      caps.toPentagonCapPair.inner.vertexSupport := by
  rw [deletedFacePerm, Equiv.Perm.mul_apply, deletedRho_val,
    data.toRotationSystem.vert_rho]
  by_cases hopposite : data.toRotationSystem.vertOf
      (data.toRotationSystem.alpha dart.1) ∈
        caps.toPentagonCapPair.deletedVertexSupport
  · rw [deletedAlpha_apply_internal data.toRotationSystem
      caps.toPentagonCapPair.deletedVertexSupport dart hopposite]
    change data.toRotationSystem.vertOf
      (data.toRotationSystem.alpha dart.1) ∈
        caps.toPentagonCapPair.inner.vertexSupport ∪
          caps.toPentagonCapPair.outer.vertexSupport at hopposite
    rw [Finset.mem_union] at hopposite
    rcases hopposite with hinnerOpposite | houterOpposite
    · exact hinnerOpposite
    · rcases (caps.toPentagonCapPair.inner.mem_vertexSupport_iff _).mp hinner with
        ⟨innerStep, hinnerStep⟩
      rcases (caps.toPentagonCapPair.outer.mem_vertexSupport_iff _).mp
          houterOpposite with ⟨outerStep, houterStep⟩
      exfalso
      apply not_adj_inner_outerVertices caps innerStep outerStep
      have hadj : G.Adj dart.1.fst dart.1.snd := dart.1.edge_mem
      simpa [SimpleGraphDartRotation.Data.toRotationSystem_vertOf,
        SimpleGraphDartRotation.Data.toRotationSystem_alpha,
        hinnerStep, houterStep] using hadj
  · rw [deletedAlpha_apply_boundary data.toRotationSystem
      caps.toPentagonCapPair.deletedVertexSupport dart hopposite]
    exact hinner

/-- Every finite number of simultaneous deleted-face steps preserves the
inner cap component. -/
theorem deletedFacePerm_pow_preserves_innerSupport
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (dart : DeletedBasedDart data.toRotationSystem
      caps.toPentagonCapPair.deletedVertexSupport)
    (hinner : data.toRotationSystem.vertOf dart.1 ∈
      caps.toPentagonCapPair.inner.vertexSupport)
    (power : Nat) :
    data.toRotationSystem.vertOf
        ((deletedFacePerm data.toRotationSystem
          caps.toPentagonCapPair.deletedVertexSupport ^ power) dart).1 ∈
      caps.toPentagonCapPair.inner.vertexSupport := by
  induction power with
  | zero => simpa using hinner
  | succ power ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact deletedFacePerm_preserves_innerSupport caps _ ih

/-- The two named cap boundaries lie in distinct cycles of the simultaneous
deleted-face permutation.  This is an algebraic consequence of the invariant
cap components, not an assumed planar picture. -/
theorem inner_outerDeletedBoundary_not_sameCycle
    (caps : FacialPentagonCapBoundaryWalkPair data) :
    ¬ (deletedFacePerm data.toRotationSystem
      caps.toPentagonCapPair.deletedVertexSupport).SameCycle
        (FacialPentagonCapBoundaryWalk.extendedCapDeletedBoundaryDart
          caps.inner caps.toPentagonCapPair.deletedVertexSupport
          (innerSupport_subset_deleted caps) (innerSpoke_not_mem_deleted caps) 0).1
        (FacialPentagonCapBoundaryWalk.extendedCapDeletedBoundaryDart
          caps.outer caps.toPentagonCapPair.deletedVertexSupport
          (outerSupport_subset_deleted caps) (outerSpoke_not_mem_deleted caps) 0).1 := by
  intro hsame
  rcases hsame.exists_nat_pow_eq with ⟨power, hpower⟩
  have hinner : data.toRotationSystem.vertOf
      (FacialPentagonCapBoundaryWalk.extendedCapDeletedBoundaryDart
        caps.inner caps.toPentagonCapPair.deletedVertexSupport
        (innerSupport_subset_deleted caps) (innerSpoke_not_mem_deleted caps) 0).1.1 ∈
      caps.toPentagonCapPair.inner.vertexSupport := by
    apply (caps.toPentagonCapPair.inner.mem_vertexSupport_iff _).2
    refine ⟨0, ?_⟩
    rfl
  have hpreserved := deletedFacePerm_pow_preserves_innerSupport caps _ hinner power
  rw [hpower] at hpreserved
  have houter : data.toRotationSystem.vertOf
      (FacialPentagonCapBoundaryWalk.extendedCapDeletedBoundaryDart
        caps.outer caps.toPentagonCapPair.deletedVertexSupport
        (outerSupport_subset_deleted caps) (outerSpoke_not_mem_deleted caps) 0).1.1 ∈
      caps.toPentagonCapPair.outer.vertexSupport := by
    apply (caps.toPentagonCapPair.outer.mem_vertexSupport_iff _).2
    refine ⟨0, ?_⟩
    rfl
  exact (Finset.disjoint_left.mp caps.toPentagonCapPair.vertexSupport_disjoint)
    hpreserved houter

/-- The inner five ports form one deleted-face cycle in the literal two-cap
carrier. -/
theorem innerDeletedBoundary_sameCycle
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (first second : Fin 5) :
    (deletedFacePerm data.toRotationSystem
      caps.toPentagonCapPair.deletedVertexSupport).SameCycle
      (FacialPentagonCapBoundaryWalk.extendedCapDeletedBoundaryDart
        caps.inner caps.toPentagonCapPair.deletedVertexSupport
        (innerSupport_subset_deleted caps) (innerSpoke_not_mem_deleted caps) first).1
      (FacialPentagonCapBoundaryWalk.extendedCapDeletedBoundaryDart
        caps.inner caps.toPentagonCapPair.deletedVertexSupport
        (innerSupport_subset_deleted caps) (innerSpoke_not_mem_deleted caps) second).1 := by
  exact FacialPentagonCapBoundaryWalk.extendedCapDeletedBoundaryDart_sameCycle
    caps.inner caps.toPentagonCapPair.deletedVertexSupport
    (innerSupport_subset_deleted caps) (innerSpoke_not_mem_deleted caps)
    hcubic hrotation first second

/-- The outer five ports form one deleted-face cycle in the literal two-cap
carrier. -/
theorem outerDeletedBoundary_sameCycle
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (first second : Fin 5) :
    (deletedFacePerm data.toRotationSystem
      caps.toPentagonCapPair.deletedVertexSupport).SameCycle
      (FacialPentagonCapBoundaryWalk.extendedCapDeletedBoundaryDart
        caps.outer caps.toPentagonCapPair.deletedVertexSupport
        (outerSupport_subset_deleted caps) (outerSpoke_not_mem_deleted caps) first).1
      (FacialPentagonCapBoundaryWalk.extendedCapDeletedBoundaryDart
        caps.outer caps.toPentagonCapPair.deletedVertexSupport
        (outerSupport_subset_deleted caps) (outerSpoke_not_mem_deleted caps) second).1 := by
  exact FacialPentagonCapBoundaryWalk.extendedCapDeletedBoundaryDart_sameCycle
    caps.outer caps.toPentagonCapPair.deletedVertexSupport
    (outerSupport_subset_deleted caps) (outerSpoke_not_mem_deleted caps)
    hcubic hrotation first second

end FacialPentagonCapBoundaryWalkPair

end

end GoertzelV24FacialPentagonCapPairDeletedCycle

end Mettapedia.GraphTheory.FourColor
