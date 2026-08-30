import Mettapedia.GraphTheory.EdgeColoringEmbedding
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairBoundary

/-!
# Reversing an adjacent-pair deletion

The same physical adjacent pair may be traversed in opposite directions by
two neighbouring mesh cells.  This file reverses its ordered four-port data
and transports a proper deletion colouring across the canonical isomorphism
between the two swapped induced graphs.

No planarity or wall statement is involved.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AdjacentPairReversal

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Exchange the two two-port blocks.  It is its own inverse. -/
def reversePortFun (port : Fin 4) : Fin 4 :=
  if port = 0 then 2
  else if port = 1 then 3
  else if port = 2 then 0
  else 1

def reversePort : Fin 4 ≃ Fin 4 where
  toFun := reversePortFun
  invFun := reversePortFun
  left_inv port := by fin_cases port <;> simp [reversePortFun]
  right_inv port := by fin_cases port <;> simp [reversePortFun]

@[simp] theorem reversePort_zero : reversePort 0 = 2 := by
  simp [reversePort, reversePortFun]
@[simp] theorem reversePort_one : reversePort 1 = 3 := by
  simp [reversePort, reversePortFun]
@[simp] theorem reversePort_two : reversePort 2 = 0 := by
  simp [reversePort, reversePortFun]
@[simp] theorem reversePort_three : reversePort 3 = 1 := by
  simp [reversePort, reversePortFun]

/-- Reverse the directed central pair and exchange its two port blocks. -/
def reverse (data : AdjacentPairData G) : AdjacentPairData G where
  firstVertex := data.secondVertex
  secondVertex := data.firstVertex
  portVertex port := data.portVertex (reversePort port)
  centralAdjacent := data.centralAdjacent.symm
  portInjective := data.portInjective.comp reversePort.injective
  portNeFirst port := data.portNeSecond (reversePort port)
  portNeSecond port := data.portNeFirst (reversePort port)
  firstNeighbors := by
    simpa [reversePort, reversePortFun] using data.secondNeighbors
  secondNeighbors := by
    simpa [reversePort, reversePortFun] using data.firstNeighbors

@[simp] theorem reverse_firstVertex (data : AdjacentPairData G) :
    (reverse data).firstVertex = data.secondVertex := rfl

@[simp] theorem reverse_secondVertex (data : AdjacentPairData G) :
    (reverse data).secondVertex = data.firstVertex := rfl

@[simp] theorem reverse_portVertex (data : AdjacentPairData G) (port : Fin 4) :
    (reverse data).portVertex port = data.portVertex (reversePort port) := rfl

/-- Swap the two inequalities in the retained-vertex subtype. -/
def retainedVertexSwapEquiv (first second : V) :
    retainedVertexSet first second ≃ retainedVertexSet second first where
  toFun vertex := ⟨vertex.1, vertex.2.2, vertex.2.1⟩
  invFun vertex := ⟨vertex.1, vertex.2.2, vertex.2.1⟩
  left_inv vertex := by ext; rfl
  right_inv vertex := by ext; rfl

@[simp] theorem retainedVertexSwapEquiv_apply_val
    (first second : V) (vertex : retainedVertexSet first second) :
    (retainedVertexSwapEquiv first second vertex).1 = vertex.1 := rfl

@[simp] theorem retainedVertexSwapEquiv_symm_apply_val
    (first second : V) (vertex : retainedVertexSet second first) :
    ((retainedVertexSwapEquiv first second).symm vertex).1 = vertex.1 := rfl

/-- The two orders of deleting the same pair induce canonically isomorphic
graphs. -/
def deletedAdjacentPairSwapIso (first second : V) :
    DeletedAdjacentPairGraph G first second ≃g
      DeletedAdjacentPairGraph G second first where
  toEquiv := retainedVertexSwapEquiv first second
  map_rel_iff' := Iff.rfl

/-- Transport a deletion colouring to the reversed endpoint order. -/
def reverseColoring (data : AdjacentPairData G)
    (coloring : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color) :
    (DeletedAdjacentPairGraph G (reverse data).firstVertex
      (reverse data).secondVertex).EdgeColoring Color :=
  coloring.pullbackEmbedding
    (deletedAdjacentPairSwapIso data.firstVertex data.secondVertex).symm.toEmbedding

@[simp] theorem reverseColoring_apply
    (data : AdjacentPairData G)
    (coloring : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (edge : (DeletedAdjacentPairGraph G (reverse data).firstVertex
      (reverse data).secondVertex).edgeSet) :
    reverseColoring data coloring edge =
      coloring
        ((deletedAdjacentPairSwapIso data.firstVertex
          data.secondVertex).symm.mapEdgeSet edge) := rfl

/-- Reversing the endpoint order preserves the nonzero Tait condition. -/
theorem isTaitEdgeColoring_reverseColoring
    (data : AdjacentPairData G)
    (coloring : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hcoloring : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
      coloring) :
    IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G (reverse data).firstVertex
        (reverse data).secondVertex)
      (reverseColoring data coloring) := by
  intro edge
  exact hcoloring
    ((deletedAdjacentPairSwapIso data.firstVertex
      data.secondVertex).symm.mapEdgeSet edge)

end

end GoertzelV24AdjacentPairReversal

end Mettapedia.GraphTheory.FourColor
