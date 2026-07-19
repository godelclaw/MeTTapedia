import Mathlib.Data.Finset.Sym
import Mettapedia.GraphTheory.FourColor.CDLFlow
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCycleSpaceEquality

/-! Zero extension of color chains from induced subgraphs and its ambient
cycle-space interpretation. -/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InducedChainExtension

open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCycleSpaceEquality
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PrimalCycleSpace
open SimpleGraph
open SimpleGraphDartRotation
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The carrier selected by an induced-side predicate. -/
abbrev SideVertex (side : V → Prop) :=
  ↑({vertex | side vertex} : Set V)

/-- Inclusion of the induced graph's edge carrier into the ambient graph. -/
def inducedEdgeEmbedding (G : SimpleGraph V) (side : V → Prop) :
    (G.induce {vertex | side vertex}).edgeSet ↪ G.edgeSet :=
  (SimpleGraph.Embedding.induce
    (G := G) {vertex | side vertex}).mapEdgeSet

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem inducedEdgeEmbedding_val
    (G : SimpleGraph V) (side : V → Prop)
    (edge : (G.induce {vertex | side vertex}).edgeSet) :
    ((inducedEdgeEmbedding G side edge).1 : Sym2 V) =
      Sym2.map Subtype.val edge.1 :=
  rfl

omit [Fintype V] [DecidableEq V] in
/-- Endpoint incidence is preserved exactly by induced-edge inclusion. -/
theorem mem_inducedEdgeEmbedding_iff
    (G : SimpleGraph V) (side : V → Prop)
    (vertex : SideVertex side)
    (edge : (G.induce {vertex | side vertex}).edgeSet) :
    vertex.1 ∈ ((inducedEdgeEmbedding G side edge).1 : Sym2 V) ↔
      vertex ∈ (edge.1 : Sym2 (SideVertex side)) := by
  rw [inducedEdgeEmbedding_val]
  induction edge.1 using Sym2.inductionOn with
  | _ left right =>
      rw [Sym2.map_mk, Sym2.mem_iff, Sym2.mem_iff]
      constructor
      · rintro (heq | heq)
        · exact Or.inl (Subtype.ext heq)
        · exact Or.inr (Subtype.ext heq)
      · rintro (heq | heq)
        · exact Or.inl (congrArg Subtype.val heq)
        · exact Or.inr (congrArg Subtype.val heq)

omit [Fintype V] [DecidableEq V] in
/-- Every endpoint of an included induced edge satisfies the side
predicate. -/
theorem side_of_mem_inducedEdgeEmbedding
    (G : SimpleGraph V) (side : V → Prop) (vertex : V)
    (edge : (G.induce {vertex | side vertex}).edgeSet)
    (hvertex : vertex ∈
      ((inducedEdgeEmbedding G side edge).1 : Sym2 V)) :
    side vertex := by
  rw [inducedEdgeEmbedding_val] at hvertex
  rcases Sym2.mem_map.mp hvertex with
    ⟨sourceVertex, _hsourceVertex, hsourceValue⟩
  rw [← hsourceValue]
  exact sourceVertex.2

/-- The finite ambient image of all induced edges. -/
def inducedEdgeImageFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (side : V → Prop)
    [Fintype ↑({vertex | side vertex} : Set V)]
    [DecidableEq ↑({vertex | side vertex} : Set V)] : Finset G.edgeSet :=
  Finset.univ.map (inducedEdgeEmbedding G side)

/-- Included induced edges preserve membership in the local incident-edge
finset. -/
theorem inducedEdgeEmbedding_mem_incidentEdgeFinset_iff
    (G : SimpleGraph V) [DecidableRel G.Adj] (side : V → Prop)
    [Fintype ↑({vertex | side vertex} : Set V)]
    [DecidableEq ↑({vertex | side vertex} : Set V)]
    (vertex : SideVertex side)
    (edge : (G.induce {vertex | side vertex}).edgeSet) :
    inducedEdgeEmbedding G side edge ∈ incidentEdgeFinset G vertex.1 ↔
      edge ∈ incidentEdgeFinset
        (G.induce {vertex | side vertex}) vertex := by
  simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact mem_inducedEdgeEmbedding_iff G side vertex edge

/-- Mapping the induced incident edges gives exactly those ambient incident
edges lying in the induced-edge image. -/
theorem map_incidentEdgeFinset_inducedEdgeEmbedding
    (G : SimpleGraph V) [DecidableRel G.Adj] (side : V → Prop)
    [Fintype ↑({vertex | side vertex} : Set V)]
    [DecidableEq ↑({vertex | side vertex} : Set V)]
    (vertex : SideVertex side) :
    (incidentEdgeFinset (G.induce {vertex | side vertex}) vertex).map
        (inducedEdgeEmbedding G side) =
      (incidentEdgeFinset G vertex.1).filter fun edge =>
        edge ∈ inducedEdgeImageFinset G side := by
  classical
  ext ambientEdge
  constructor
  · intro himage
    rcases Finset.mem_map.mp himage with
      ⟨inducedEdge, hincident, heq⟩
    subst ambientEdge
    apply Finset.mem_filter.mpr
    exact ⟨(inducedEdgeEmbedding_mem_incidentEdgeFinset_iff
        G side vertex inducedEdge).2 hincident,
      Finset.mem_map.mpr ⟨inducedEdge, Finset.mem_univ _, rfl⟩⟩
  · intro hfiltered
    rcases Finset.mem_filter.mp hfiltered with
      ⟨hincident, himage⟩
    rcases Finset.mem_map.mp himage with
      ⟨inducedEdge, _huniv, heq⟩
    subst ambientEdge
    exact Finset.mem_map.mpr
      ⟨inducedEdge,
        (inducedEdgeEmbedding_mem_incidentEdgeFinset_iff
          G side vertex inducedEdge).1 hincident, rfl⟩

/-- Extend an edge chain from an induced subgraph by zero on every ambient
edge outside its image. -/
def inducedEdgeChainExtendZero
    {A : Type*} [Zero A]
    (G : SimpleGraph V) (side : V → Prop)
    (chain : (G.induce {vertex | side vertex}).edgeSet → A) :
    G.edgeSet → A :=
  Function.extend (inducedEdgeEmbedding G side) chain 0

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem inducedEdgeChainExtendZero_apply_inducedEdgeEmbedding
    {A : Type*} [Zero A]
    (G : SimpleGraph V) (side : V → Prop)
    (chain : (G.induce {vertex | side vertex}).edgeSet → A)
    (edge : (G.induce {vertex | side vertex}).edgeSet) :
    inducedEdgeChainExtendZero G side chain
        (inducedEdgeEmbedding G side edge) = chain edge :=
  (inducedEdgeEmbedding G side).injective.extend_apply chain 0 edge

omit [Fintype V] [DecidableEq V] in
/-- The zero extension vanishes away from the induced-edge image. -/
theorem inducedEdgeChainExtendZero_eq_zero_of_not_exists
    {A : Type*} [Zero A]
    (G : SimpleGraph V) (side : V → Prop)
    (chain : (G.induce {vertex | side vertex}).edgeSet → A)
    (edge : G.edgeSet)
    (houtside : ¬ ∃ inducedEdge,
      inducedEdgeEmbedding G side inducedEdge = edge) :
    inducedEdgeChainExtendZero G side chain edge = 0 := by
  exact Function.extend_apply' chain (0 : G.edgeSet → A) edge houtside

/-- At a retained vertex, the ambient Kirchhoff sum of the zero extension is
the original induced-graph Kirchhoff sum. -/
theorem vertexKirchhoffSum_inducedEdgeChainExtendZero
    (G : SimpleGraph V) [DecidableRel G.Adj] (side : V → Prop)
    [Fintype ↑({vertex | side vertex} : Set V)]
    [DecidableEq ↑({vertex | side vertex} : Set V)]
    (chain : (G.induce {vertex | side vertex}).edgeSet → Color)
    (vertex : SideVertex side) :
    vertexKirchhoffSum G
        (inducedEdgeChainExtendZero G side chain) vertex.1 =
      vertexKirchhoffSum (G.induce {vertex | side vertex}) chain vertex := by
  classical
  unfold vertexKirchhoffSum
  calc
    (∑ edge ∈ incidentEdgeFinset G vertex.1,
        inducedEdgeChainExtendZero G side chain edge) =
        ∑ edge ∈ (incidentEdgeFinset G vertex.1).filter
          (fun edge => edge ∈ inducedEdgeImageFinset G side),
            inducedEdgeChainExtendZero G side chain edge := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro edge hincident hnotFiltered
      apply inducedEdgeChainExtendZero_eq_zero_of_not_exists
      rintro ⟨inducedEdge, heq⟩
      apply hnotFiltered
      exact Finset.mem_filter.mpr
        ⟨hincident, Finset.mem_map.mpr
          ⟨inducedEdge, Finset.mem_univ _, heq⟩⟩
    _ = ∑ edge ∈
          (incidentEdgeFinset
            (G.induce {vertex | side vertex}) vertex).map
              (inducedEdgeEmbedding G side),
          inducedEdgeChainExtendZero G side chain edge := by
      rw [map_incidentEdgeFinset_inducedEdgeEmbedding G side vertex]
    _ = ∑ edge ∈ incidentEdgeFinset
          (G.induce {vertex | side vertex}) vertex,
        inducedEdgeChainExtendZero G side chain
          (inducedEdgeEmbedding G side edge) := by
      rw [Finset.sum_map]
    _ = ∑ edge ∈ incidentEdgeFinset
          (G.induce {vertex | side vertex}) vertex, chain edge := by
      apply Finset.sum_congr rfl
      intro edge _hedge
      exact inducedEdgeChainExtendZero_apply_inducedEdgeEmbedding
        G side chain edge

/-- At a deleted vertex, every included induced edge is nonincident, so the
ambient Kirchhoff sum of the zero extension is zero. -/
theorem vertexKirchhoffSum_inducedEdgeChainExtendZero_eq_zero_of_not_side
    (G : SimpleGraph V) [DecidableRel G.Adj] (side : V → Prop)
    [Fintype ↑({vertex | side vertex} : Set V)]
    [DecidableEq ↑({vertex | side vertex} : Set V)]
    (chain : (G.induce {vertex | side vertex}).edgeSet → Color)
    (vertex : V) (hvertex : ¬ side vertex) :
    vertexKirchhoffSum G
      (inducedEdgeChainExtendZero G side chain) vertex = 0 := by
  classical
  unfold vertexKirchhoffSum
  apply Finset.sum_eq_zero
  intro edge hincident
  apply inducedEdgeChainExtendZero_eq_zero_of_not_exists
  rintro ⟨inducedEdge, heq⟩
  have hmem : vertex ∈
      ((inducedEdgeEmbedding G side inducedEdge).1 : Sym2 V) := by
    have hambient : vertex ∈ (edge.1 : Sym2 V) := by
      simpa only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
        true_and] using hincident
    simpa only [heq] using hambient
  exact hvertex
    (side_of_mem_inducedEdgeEmbedding G side vertex inducedEdge hmem)

/-- A Kirchhoff circulation on an induced graph remains a circulation after
zero extension to the ambient graph. -/
theorem isGraphFlow_inducedEdgeChainExtendZero
    (G : SimpleGraph V) [DecidableRel G.Adj] (side : V → Prop)
    [Fintype ↑({vertex | side vertex} : Set V)]
    [DecidableEq ↑({vertex | side vertex} : Set V)]
    {chain : (G.induce {vertex | side vertex}).edgeSet → Color}
    (hflow : IsGraphFlow (G.induce {vertex | side vertex}) chain) :
    IsGraphFlow G (inducedEdgeChainExtendZero G side chain) := by
  intro vertex
  by_cases hvertex : side vertex
  · rw [vertexKirchhoffSum_inducedEdgeChainExtendZero
      G side chain ⟨vertex, hvertex⟩]
    exact hflow ⟨vertex, hvertex⟩
  · exact
      vertexKirchhoffSum_inducedEdgeChainExtendZero_eq_zero_of_not_side
        G side chain vertex hvertex

/-- Zero extension is a circulation exactly when the original induced chain
is a circulation. -/
theorem isGraphFlow_inducedEdgeChainExtendZero_iff
    (G : SimpleGraph V) [DecidableRel G.Adj] (side : V → Prop)
    [Fintype ↑({vertex | side vertex} : Set V)]
    [DecidableEq ↑({vertex | side vertex} : Set V)]
    {chain : (G.induce {vertex | side vertex}).edgeSet → Color} :
    IsGraphFlow G (inducedEdgeChainExtendZero G side chain) ↔
      IsGraphFlow (G.induce {vertex | side vertex}) chain := by
  constructor
  · intro hflow vertex
    rw [← vertexKirchhoffSum_inducedEdgeChainExtendZero
      G side chain vertex]
    exact hflow vertex.1
  · exact isGraphFlow_inducedEdgeChainExtendZero G side

/-- The first coordinate of an `F₂²` graph circulation lies in the scalar
cycle space. -/
private theorem scalarVertexKirchhoffSum_eq_incidence_mulVec
    (chain : G.edgeSet → F2) (vertex : V) :
    scalarVertexKirchhoffSum G chain vertex =
      (f2IncidenceMatrix G).mulVecLin chain vertex := by
  classical
  unfold scalarVertexKirchhoffSum incidentEdgeFinset
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    f2IncidenceMatrix, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]

theorem fst_mem_f2CycleSpace_of_isGraphFlow
    {chain : G.edgeSet → Color} (hflow : IsGraphFlow G chain) :
    (fun edge => (chain edge).1) ∈ f2CycleSpace G := by
  rw [f2CycleSpace, LinearMap.mem_ker]
  funext vertex
  rw [← scalarVertexKirchhoffSum_eq_incidence_mulVec,
    scalarVertexKirchhoffSum_fst]
  simp only [Pi.zero_apply, hflow vertex]
  rfl

/-- The second coordinate of an `F₂²` graph circulation lies in the scalar
cycle space. -/
theorem snd_mem_f2CycleSpace_of_isGraphFlow
    {chain : G.edgeSet → Color} (hflow : IsGraphFlow G chain) :
    (fun edge => (chain edge).2) ∈ f2CycleSpace G := by
  rw [f2CycleSpace, LinearMap.mem_ker]
  funext vertex
  rw [← scalarVertexKirchhoffSum_eq_incidence_mulVec,
    scalarVertexKirchhoffSum_snd]
  simp only [Pi.zero_apply, hflow vertex]
  rfl

/-- A color chain is a graph circulation exactly when both of its binary
coordinates lie in the scalar cycle space. -/
theorem isGraphFlow_iff_fst_snd_mem_f2CycleSpace
    {chain : G.edgeSet → Color} :
    IsGraphFlow G chain ↔
      (fun edge => (chain edge).1) ∈ f2CycleSpace G ∧
        (fun edge => (chain edge).2) ∈ f2CycleSpace G := by
  constructor
  · intro hflow
    exact ⟨fst_mem_f2CycleSpace_of_isGraphFlow hflow,
      snd_mem_f2CycleSpace_of_isGraphFlow hflow⟩
  · rintro ⟨hfirst, hsecond⟩ vertex
    apply Prod.ext
    · rw [← scalarVertexKirchhoffSum_fst,
        scalarVertexKirchhoffSum_eq_incidence_mulVec]
      exact congrFun ((LinearMap.mem_ker).1 hfirst) vertex
    · rw [← scalarVertexKirchhoffSum_snd,
        scalarVertexKirchhoffSum_eq_incidence_mulVec]
      exact congrFun ((LinearMap.mem_ker).1 hsecond) vertex

/-- If both coordinates of a color chain are facial boundary combinations,
then the chain is a graph circulation. -/
theorem isGraphFlow_of_orbitFaceBoundary_coefficients
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {chain : G.edgeSet → Color}
    {first second : OrbitFace data.toRotationSystem → F2}
    (hfirst : orbitFaceBoundaryLinearMap data.toRotationSystem first =
      (fun edge => (chain edge).1))
    (hsecond : orbitFaceBoundaryLinearMap data.toRotationSystem second =
      (fun edge => (chain edge).2)) :
    IsGraphFlow G chain := by
  rw [isGraphFlow_iff_fst_snd_mem_f2CycleSpace]
  constructor
  · rw [← hfirst]
    exact range_orbitFaceBoundaryLinearMap_le_f2CycleSpace
      data htwoSided ⟨first, rfl⟩
  · rw [← hsecond]
    exact range_orbitFaceBoundaryLinearMap_le_f2CycleSpace
      data htwoSided ⟨second, rfl⟩

/-- On a cellular sphere, both coordinates of every ambient color
circulation are explicit linear combinations of facial boundaries. -/
theorem exists_orbitFaceBoundary_coefficients_of_isGraphFlow
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    {chain : G.edgeSet → Color} (hflow : IsGraphFlow G chain) :
    ∃ first second : OrbitFace data.toRotationSystem → F2,
      orbitFaceBoundaryLinearMap data.toRotationSystem first =
        (fun edge => (chain edge).1) ∧
      orbitFaceBoundaryLinearMap data.toRotationSystem second =
        (fun edge => (chain edge).2) := by
  have hfirst : (fun edge => (chain edge).1) ∈
      LinearMap.range
        (orbitFaceBoundaryLinearMap data.toRotationSystem) := by
    rw [range_orbitFaceBoundaryLinearMap_eq_f2CycleSpace
      data htwoSided hdual hconnected hsphere]
    exact fst_mem_f2CycleSpace_of_isGraphFlow hflow
  have hsecond : (fun edge => (chain edge).2) ∈
      LinearMap.range
        (orbitFaceBoundaryLinearMap data.toRotationSystem) := by
    rw [range_orbitFaceBoundaryLinearMap_eq_f2CycleSpace
      data htwoSided hdual hconnected hsphere]
    exact snd_mem_f2CycleSpace_of_isGraphFlow hflow
  rcases hfirst with ⟨first, hfirst⟩
  rcases hsecond with ⟨second, hsecond⟩
  exact ⟨first, second, hfirst, hsecond⟩

/-- On a cellular sphere, facial coefficient pairs characterize ambient
color circulations exactly. -/
theorem isGraphFlow_iff_exists_orbitFaceBoundary_coefficients
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    {chain : G.edgeSet → Color} :
    IsGraphFlow G chain ↔
      ∃ first second : OrbitFace data.toRotationSystem → F2,
        orbitFaceBoundaryLinearMap data.toRotationSystem first =
            (fun edge => (chain edge).1) ∧
          orbitFaceBoundaryLinearMap data.toRotationSystem second =
            (fun edge => (chain edge).2) := by
  constructor
  · exact exists_orbitFaceBoundary_coefficients_of_isGraphFlow
      data htwoSided hdual hconnected hsphere
  · rintro ⟨first, second, hfirst, hsecond⟩
    exact isGraphFlow_of_orbitFaceBoundary_coefficients
      data htwoSided hfirst hsecond

end

end GoertzelV24InducedChainExtension

end Mettapedia.GraphTheory.FourColor
