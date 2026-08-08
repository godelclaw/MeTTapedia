import Mettapedia.GraphTheory.FourColor.ColorAlgebra
import Mettapedia.GraphTheory.FourColor.IncidentEdgeFinset

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- The unoriented `𝔽₂²` Kirchhoff sum of a chain at a vertex.  Over
`𝔽₂`, orientations are irrelevant. -/
def vertexKirchhoffSum (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → Color) (v : V) : Color :=
  Finset.sum (incidentEdgeFinset G v) fun e => x e

/-- One scalar coordinate of the unoriented vertex boundary operator. -/
def scalarVertexKirchhoffSum (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → F2) (v : V) : F2 :=
  Finset.sum (incidentEdgeFinset G v) fun e => x e

theorem scalarVertexKirchhoffSum_fst
    (G : SimpleGraph V) [Fintype G.edgeSet] (z : G.edgeSet → Color) (v : V) :
    scalarVertexKirchhoffSum G (fun e => (z e).1) v =
      (vertexKirchhoffSum G z v).1 := by
  unfold scalarVertexKirchhoffSum vertexKirchhoffSum
  induction incidentEdgeFinset G v using Finset.induction_on with
  | empty => simp
  | insert e edges heNot ih =>
      rw [Finset.sum_insert heNot, Finset.sum_insert heNot, ih]
      rfl

theorem scalarVertexKirchhoffSum_snd
    (G : SimpleGraph V) [Fintype G.edgeSet] (z : G.edgeSet → Color) (v : V) :
    scalarVertexKirchhoffSum G (fun e => (z e).2) v =
      (vertexKirchhoffSum G z v).2 := by
  unfold scalarVertexKirchhoffSum vertexKirchhoffSum
  induction incidentEdgeFinset G v using Finset.induction_on with
  | empty => simp
  | insert e edges heNot ih =>
      rw [Finset.sum_insert heNot, Finset.sum_insert heNot, ih]
      rfl

end Mettapedia.GraphTheory.FourColor
