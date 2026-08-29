import Mettapedia.GraphTheory.FourColor.GoertzelV24InducedChainExtension
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphFaceDualConnectedness
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphTaitBridge
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalExactness

/-!
# Face potentials for the Spencer--Brown--Kauffman parity argument

The closed planar parity proof is most economical in Tutte's dual-potential
form.  A Tait colouring of a cubic spherical map is a nowhere-zero
`F2 × F2` circulation.  Since the facial boundaries span the cycle space on
the sphere, its two scalar coordinates integrate to a colour potential on
the quotient faces.

This file proves that integration step on the graph-backed rotation carrier
and records the exact algebra of translating a potential on a selected set
of faces.  Translation changes the represented edge chain by the boundary
of that face set; on an edge with exactly one selected incident face, the
change is exactly the translating colour.

The Euler-characteristic identity relating potential fibres to the number of
bicoloured circuits is deliberately not asserted here.  It is the remaining
topological-counting half of the parity lemma.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24KauffmanFacePotential

open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InducedChainExtension
open GoertzelV24ClosedWebLocalExactness
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceCycleSpaceEquality
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PrimalCycleSpace
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

private theorem f2_eq_zero_or_one (value : F2) :
    value = 0 ∨ value = 1 := by
  fin_cases value
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A colour-valued potential on quotient faces whose two binary boundary
coordinates represent the given primal edge chain. -/
structure ColorFacePotential (data : Data G)
    (chain : G.edgeSet → Color) where
  potential : OrbitFace data.toRotationSystem → Color
  boundary_first :
    orbitFaceBoundaryLinearMap data.toRotationSystem
        (fun face => (potential face).1) =
      fun edge => (chain edge).1
  boundary_second :
    orbitFaceBoundaryLinearMap data.toRotationSystem
        (fun face => (potential face).2) =
      fun edge => (chain edge).2

/-- Every Tait colouring of a connected two-sided spherical cubic graph has
a colour-valued face potential. -/
theorem exists_colorFacePotential_of_tait
    (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    Nonempty (ColorFacePotential data C) := by
  have hconnected : G.Connected := by
    rw [← rotationPrimalGraph_toRotationSystem_eq G data]
    exact hclass.primalConnected
  have hdual :
      (interiorDualGraph
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace data.toRotationSystem))).Connected :=
    orbitFaceInteriorDual_connected data.toRotationSystem
      hclass.spherical.cubic hclass.primalConnected
      hclass.vertexRotationCyclic
  have hcubicEdges : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      data hclass.spherical.cubic
  have hflow : IsGraphFlow G C :=
    isGraphFlow_of_taitEdgeColoring_of_hasCubicIncidentEdgeTriples
      (hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three
        hcubicEdges) hC
  rcases exists_orbitFaceBoundary_coefficients_of_isGraphFlow
      data htwoSided hdual hconnected hclass.spherical hflow with
    ⟨first, second, hfirst, hsecond⟩
  exact ⟨⟨fun face => (first face, second face), hfirst, hsecond⟩⟩

/-- Across a dart, the sum of the two incident face potentials is the colour
of its primal edge. -/
theorem ColorFacePotential.incident_add
    {data : Data G} {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (dart : data.toRotationSystem.D) :
    coordinates.potential (dartOrbitFace data.toRotationSystem dart) +
        coordinates.potential
          (dartOrbitFace data.toRotationSystem
            (data.toRotationSystem.alpha dart)) =
      chain (data.toRotationSystem.edgeOf dart) := by
  apply Prod.ext
  · have hvalue := congrFun coordinates.boundary_first
      (data.toRotationSystem.edgeOf dart)
    rw [orbitFaceBoundaryLinearMap_apply_edgeOf
      data.toRotationSystem htwoSided] at hvalue
    exact hvalue
  · have hvalue := congrFun coordinates.boundary_second
      (data.toRotationSystem.edgeOf dart)
    rw [orbitFaceBoundaryLinearMap_apply_edgeOf
      data.toRotationSystem htwoSided] at hvalue
    exact hvalue

/-- A nowhere-zero represented edge separates two distinct face-potential
values. -/
theorem ColorFacePotential.incident_ne
    {data : Data G} {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hnonzero : ∀ edge, chain edge ≠ 0)
    (dart : data.toRotationSystem.D) :
    coordinates.potential (dartOrbitFace data.toRotationSystem dart) ≠
      coordinates.potential
        (dartOrbitFace data.toRotationSystem
          (data.toRotationSystem.alpha dart)) := by
  intro heq
  have hadd := coordinates.incident_add htwoSided dart
  rw [heq, color_add_self] at hadd
  exact hnonzero _ hadd.symm

/-- Module-level interface for the incident-face addition law.  This alias is
kept separate from the method form so document tooling can resolve the
declaration without interpreting namespace-qualified method syntax. -/
theorem colorFacePotential_incident_add
    {data : Data G} {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (dart : data.toRotationSystem.D) :
    coordinates.potential (dartOrbitFace data.toRotationSystem dart) +
        coordinates.potential
          (dartOrbitFace data.toRotationSystem
            (data.toRotationSystem.alpha dart)) =
      chain (data.toRotationSystem.edgeOf dart) :=
  coordinates.incident_add htwoSided dart

/-- Module-level interface for separation of incident face potentials by a
nowhere-zero edge. -/
theorem colorFacePotential_incident_ne
    {data : Data G} {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hnonzero : ∀ edge, chain edge ≠ 0)
    (dart : data.toRotationSystem.D) :
    coordinates.potential (dartOrbitFace data.toRotationSystem dart) ≠
      coordinates.potential
        (dartOrbitFace data.toRotationSystem
          (data.toRotationSystem.alpha dart)) :=
  coordinates.incident_ne htwoSided hnonzero dart

/-! ## Exact face-set separation of a binary cycle -/

/-- The binary indicator of a selected quotient-face set. -/
def faceSetIndicator
    (data : Data G) (faces : Finset (OrbitFace data.toRotationSystem)) :
    OrbitFace data.toRotationSystem → F2 :=
  fun face => if face ∈ faces then 1 else 0

/-- Every binary cycle on a connected spherical map is exactly the boundary
of a finite set of quotient faces.  This is the combinatorial-map form of
the separation statement needed for an operated Kempe circuit. -/
theorem exists_faceSetBoundary_eq_of_mem_f2CycleSpace
    (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {chain : G.edgeSet → F2} (hchain : chain ∈ f2CycleSpace G) :
    ∃ faces : Finset (OrbitFace data.toRotationSystem),
      orbitFaceBoundaryLinearMap data.toRotationSystem
          (faceSetIndicator data faces) = chain := by
  have hconnected : G.Connected := by
    rw [← rotationPrimalGraph_toRotationSystem_eq G data]
    exact hclass.primalConnected
  have hdual :
      (interiorDualGraph
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace data.toRotationSystem))).Connected :=
    orbitFaceInteriorDual_connected data.toRotationSystem
      hclass.spherical.cubic hclass.primalConnected
      hclass.vertexRotationCyclic
  have hspan : chain ∈ LinearMap.range
      (orbitFaceBoundaryLinearMap data.toRotationSystem) := by
    rw [range_orbitFaceBoundaryLinearMap_eq_f2CycleSpace
      data htwoSided hdual hconnected hclass.spherical]
    exact hchain
  rcases hspan with ⟨coefficients, hcoefficients⟩
  let faces : Finset (OrbitFace data.toRotationSystem) :=
    Finset.univ.filter fun face => coefficients face = 1
  refine ⟨faces, ?_⟩
  rw [← hcoefficients]
  apply congrArg (orbitFaceBoundaryLinearMap data.toRotationSystem)
  funext face
  rcases f2_eq_zero_or_one (coefficients face) with hvalue | hvalue <;>
    simp [faceSetIndicator, faces, hvalue]

/-- On a two-sided map, a selected face-set boundary takes value one on an
edge exactly when the edge has one selected and one unselected incident
face. -/
theorem faceSetBoundary_apply_eq_one_iff_separates
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (faces : Finset (OrbitFace data.toRotationSystem))
    (dart : data.toRotationSystem.D) :
    orbitFaceBoundaryLinearMap data.toRotationSystem
        (faceSetIndicator data faces)
        (data.toRotationSystem.edgeOf dart) = 1 ↔
      ((dartOrbitFace data.toRotationSystem dart ∈ faces ∧
          dartOrbitFace data.toRotationSystem
            (data.toRotationSystem.alpha dart) ∉ faces) ∨
        (dartOrbitFace data.toRotationSystem dart ∉ faces ∧
          dartOrbitFace data.toRotationSystem
            (data.toRotationSystem.alpha dart) ∈ faces)) := by
  rw [orbitFaceBoundaryLinearMap_apply_edgeOf
    data.toRotationSystem htwoSided]
  by_cases hleft : dartOrbitFace data.toRotationSystem dart ∈ faces <;>
    by_cases hright : dartOrbitFace data.toRotationSystem
      (data.toRotationSystem.alpha dart) ∈ faces <;>
      simp [faceSetIndicator, hleft, hright]

/-- Consequently every binary cycle has a face set whose membership changes
across precisely the edges where the cycle vector is one. -/
theorem exists_faceSet_separates_iff_eq_one_of_mem_f2CycleSpace
    (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {chain : G.edgeSet → F2} (hchain : chain ∈ f2CycleSpace G) :
    ∃ faces : Finset (OrbitFace data.toRotationSystem),
      ∀ dart : data.toRotationSystem.D,
        chain (data.toRotationSystem.edgeOf dart) = 1 ↔
          ((dartOrbitFace data.toRotationSystem dart ∈ faces ∧
              dartOrbitFace data.toRotationSystem
                (data.toRotationSystem.alpha dart) ∉ faces) ∨
            (dartOrbitFace data.toRotationSystem dart ∉ faces ∧
              dartOrbitFace data.toRotationSystem
                (data.toRotationSystem.alpha dart) ∈ faces)) := by
  rcases exists_faceSetBoundary_eq_of_mem_f2CycleSpace
      data hclass htwoSided hchain with ⟨faces, hfaces⟩
  refine ⟨faces, fun dart => ?_⟩
  rw [← hfaces]
  exact faceSetBoundary_apply_eq_one_iff_separates
    data htwoSided faces dart

/-! ## A Kempe component is a binary primal cycle -/

/-- The scalar characteristic vector of one two-colour component. -/
def kempeComponentIndicator
    (C : G.EdgeColoring Color) (a b : Color)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    G.edgeSet → F2 := by
  classical
  exact fun edge =>
    if edge ∈ C.kempeComponentSet a b K then 1 else 0

@[simp] theorem kempeComponentIndicator_eq_one_iff
    (C : G.EdgeColoring Color) (a b : Color)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (edge : G.edgeSet) :
    kempeComponentIndicator C a b K edge = 1 ↔
      edge ∈ C.kempeComponentSet a b K := by
  classical
  simp [kempeComponentIndicator]

/-- In a cubic Tait-coloured graph, every two-colour component has even
incidence at every primal vertex, hence its characteristic vector belongs to
the primal binary cycle space. -/
theorem kempeComponentIndicator_mem_f2CycleSpace
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {a b : Color} (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3) :
    kempeComponentIndicator C a b K ∈ f2CycleSpace G := by
  classical
  rw [f2CycleSpace, LinearMap.mem_ker]
  funext vertex
  rw [Pi.zero_apply]
  change (∑ edge : G.edgeSet,
    (if vertex ∈ (edge.1 : Sym2 V) then (1 : F2) else 0) *
      kempeComponentIndicator C a b K edge) = 0
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  change (∑ edge ∈ incidentEdgeFinset G vertex,
    kempeComponentIndicator C a b K edge) = 0
  unfold kempeComponentIndicator
  let componentIncident : Finset G.edgeSet :=
    (incidentEdgeFinset G vertex).filter fun edge =>
      edge ∈ C.kempeComponentSet a b K
  have hcard : componentIncident.card = 0 ∨ componentIncident.card = 2 := by
    by_cases hempty : componentIncident = ∅
    · exact Or.inl (by simp [hempty])
    · rcases Finset.nonempty_iff_ne_empty.mpr hempty with ⟨root, hroot⟩
      have hrootData := Finset.mem_filter.mp hroot
      have hcomponentEq :
          componentIncident = incidentEdgesOfColorPair C a b vertex := by
        ext edge
        constructor
        · intro hedge
          have hedgeData := Finset.mem_filter.mp hedge
          exact (mem_incidentEdgesOfColorPair_iff
            C a b vertex edge).2
              ⟨hedgeData.1,
                C.mem_bicoloredSet_of_mem_kempeComponentSet hedgeData.2⟩
        · intro hedge
          have hedgeData :=
            (mem_incidentEdgesOfColorPair_iff C a b vertex edge).1 hedge
          apply Finset.mem_filter.mpr
          refine ⟨hedgeData.1, ?_⟩
          by_cases heq : edge = root
          · simpa [heq] using hrootData.2
          · have hrootAt : vertex ∈ (root : Sym2 V) := by
              simpa [incidentEdgeFinset] using hrootData.1
            have hedgeAt : vertex ∈ (edge : Sym2 V) := by
              simpa [incidentEdgeFinset] using hedgeData.1
            have hadj : G.lineGraph.Adj root edge :=
              G.lineGraph_adj_of_edgeSet_common_vertex
                (Ne.symm heq) hrootAt hedgeAt
            exact C.mem_kempeComponentSet_of_adj
              hrootData.2 hadj hedgeData.2
      right
      rw [hcomponentEq]
      exact incidentEdgesOfColorPair_card_eq_two_of_cubic_tait
        C hC vertex (hcubic vertex) hab
  change (∑ edge ∈ incidentEdgeFinset G vertex,
    if edge ∈ C.kempeComponentSet a b K then (1 : F2) else 0) = 0
  rw [← Finset.sum_filter]
  change (∑ _edge ∈ componentIncident, (1 : F2)) = 0
  rcases hcard with hcard | hcard <;> simp [hcard]

/-- A Kempe component in a spherical cubic map therefore has an exact
face-set separator. -/
theorem exists_faceSet_separates_iff_mem_kempeComponent
    (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {a b : Color} (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    ∃ faces : Finset (OrbitFace data.toRotationSystem),
      ∀ dart : data.toRotationSystem.D,
        (data.toRotationSystem.edgeOf dart ∈
            C.kempeComponentSet a b K) ↔
          ((dartOrbitFace data.toRotationSystem dart ∈ faces ∧
              dartOrbitFace data.toRotationSystem
                (data.toRotationSystem.alpha dart) ∉ faces) ∨
            (dartOrbitFace data.toRotationSystem dart ∉ faces ∧
              dartOrbitFace data.toRotationSystem
                (data.toRotationSystem.alpha dart) ∈ faces)) := by
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      data hclass.spherical.cubic
  have hcycle := kempeComponentIndicator_mem_f2CycleSpace
    C hC hab K hcubic
  rcases exists_faceSet_separates_iff_eq_one_of_mem_f2CycleSpace
      data hclass htwoSided hcycle with ⟨faces, hfaces⟩
  refine ⟨faces, fun dart => ?_⟩
  rw [← kempeComponentIndicator_eq_one_iff]
  exact hfaces dart

/-- The colour indicator of a selected quotient-face set. -/
def faceSetColorIndicator
    (data : Data G) (faces : Finset (OrbitFace data.toRotationSystem))
    (delta : Color) : OrbitFace data.toRotationSystem → Color :=
  fun face => if face ∈ faces then delta else 0

/-- The colour chain carried by the boundary of a selected face set. -/
def faceSetBoundaryColor
    (data : Data G) (faces : Finset (OrbitFace data.toRotationSystem))
    (delta : Color) : G.edgeSet → Color :=
  fun edge =>
    (orbitFaceBoundaryLinearMap data.toRotationSystem
        (fun face => (faceSetColorIndicator data faces delta face).1) edge,
      orbitFaceBoundaryLinearMap data.toRotationSystem
        (fun face => (faceSetColorIndicator data faces delta face).2) edge)

/-- Translating a face potential by `delta` on a selected face set adds the
corresponding coloured face-set boundary to its represented edge chain. -/
def ColorFacePotential.translate
    {data : Data G} {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain)
    (faces : Finset (OrbitFace data.toRotationSystem)) (delta : Color) :
    ColorFacePotential data
      (fun edge => chain edge + faceSetBoundaryColor data faces delta edge) where
  potential := fun face =>
    coordinates.potential face + faceSetColorIndicator data faces delta face
  boundary_first := by
    change orbitFaceBoundaryLinearMap data.toRotationSystem
        ((fun face => (coordinates.potential face).1) +
          fun face => (faceSetColorIndicator data faces delta face).1) =
      (fun edge => (chain edge).1) +
        fun edge =>
          (faceSetBoundaryColor data faces delta edge).1
    rw [map_add, coordinates.boundary_first]
    rfl
  boundary_second := by
    change orbitFaceBoundaryLinearMap data.toRotationSystem
        ((fun face => (coordinates.potential face).2) +
          fun face => (faceSetColorIndicator data faces delta face).2) =
      (fun edge => (chain edge).2) +
        fun edge =>
          (faceSetBoundaryColor data faces delta edge).2
    rw [map_add, coordinates.boundary_second]
    rfl

/-- Evaluating a translated potential adds the selected-face indicator at
exactly that face. -/
@[simp] theorem colorFacePotential_translate_potential
    {data : Data G} {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain)
    (faces : Finset (OrbitFace data.toRotationSystem)) (delta : Color)
    (face : OrbitFace data.toRotationSystem) :
    (coordinates.translate faces delta).potential face =
      coordinates.potential face +
        faceSetColorIndicator data faces delta face := rfl

/-- If exactly one dart-side face of an edge is selected, the coloured
face-set boundary has value `delta` on that edge. -/
theorem faceSetBoundaryColor_eq_delta_of_separates
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (faces : Finset (OrbitFace data.toRotationSystem)) (delta : Color)
    (dart : data.toRotationSystem.D)
    (hseparates :
      (dartOrbitFace data.toRotationSystem dart ∈ faces ∧
          dartOrbitFace data.toRotationSystem
            (data.toRotationSystem.alpha dart) ∉ faces) ∨
        (dartOrbitFace data.toRotationSystem dart ∉ faces ∧
          dartOrbitFace data.toRotationSystem
            (data.toRotationSystem.alpha dart) ∈ faces)) :
    faceSetBoundaryColor data faces delta
        (data.toRotationSystem.edgeOf dart) = delta := by
  rcases hseparates with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · have hrightSymm :
        dartOrbitFace data.toRotationSystem (Dart.symm dart) ∉ faces := by
      simpa using hright
    apply Prod.ext
    · change orbitFaceBoundaryLinearMap data.toRotationSystem
          (fun face =>
            (faceSetColorIndicator data faces delta face).1)
          (data.toRotationSystem.edgeOf dart) = delta.1
      rw [orbitFaceBoundaryLinearMap_apply_edgeOf
        data.toRotationSystem htwoSided]
      simp [faceSetColorIndicator, hleft, hrightSymm]
    · change orbitFaceBoundaryLinearMap data.toRotationSystem
          (fun face =>
            (faceSetColorIndicator data faces delta face).2)
          (data.toRotationSystem.edgeOf dart) = delta.2
      rw [orbitFaceBoundaryLinearMap_apply_edgeOf
        data.toRotationSystem htwoSided]
      simp [faceSetColorIndicator, hleft, hrightSymm]
  · have hrightSymm :
        dartOrbitFace data.toRotationSystem (Dart.symm dart) ∈ faces := by
      simpa using hright
    apply Prod.ext
    · change orbitFaceBoundaryLinearMap data.toRotationSystem
          (fun face =>
            (faceSetColorIndicator data faces delta face).1)
          (data.toRotationSystem.edgeOf dart) = delta.1
      rw [orbitFaceBoundaryLinearMap_apply_edgeOf
        data.toRotationSystem htwoSided]
      simp [faceSetColorIndicator, hleft, hrightSymm]
    · change orbitFaceBoundaryLinearMap data.toRotationSystem
          (fun face =>
            (faceSetColorIndicator data faces delta face).2)
          (data.toRotationSystem.edgeOf dart) = delta.2
      rw [orbitFaceBoundaryLinearMap_apply_edgeOf
        data.toRotationSystem htwoSided]
      simp [faceSetColorIndicator, hleft, hrightSymm]

/-- If the two dart-side faces of an edge have the same membership in the
selected set, the coloured face-set boundary vanishes on that edge. -/
theorem faceSetBoundaryColor_eq_zero_of_sameSide
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (faces : Finset (OrbitFace data.toRotationSystem)) (delta : Color)
    (dart : data.toRotationSystem.D)
    (hsame :
      (dartOrbitFace data.toRotationSystem dart ∈ faces ↔
        dartOrbitFace data.toRotationSystem
          (data.toRotationSystem.alpha dart) ∈ faces)) :
    faceSetBoundaryColor data faces delta
        (data.toRotationSystem.edgeOf dart) = 0 := by
  by_cases hleft : dartOrbitFace data.toRotationSystem dart ∈ faces
  · have hright := hsame.mp hleft
    have hrightSymm :
        dartOrbitFace data.toRotationSystem (Dart.symm dart) ∈ faces := by
      simpa using hright
    apply Prod.ext
    · change orbitFaceBoundaryLinearMap data.toRotationSystem
          (fun face =>
            (faceSetColorIndicator data faces delta face).1)
          (data.toRotationSystem.edgeOf dart) = 0
      rw [orbitFaceBoundaryLinearMap_apply_edgeOf
        data.toRotationSystem htwoSided]
      simp [faceSetColorIndicator, hleft, hrightSymm]
    · change orbitFaceBoundaryLinearMap data.toRotationSystem
          (fun face =>
            (faceSetColorIndicator data faces delta face).2)
          (data.toRotationSystem.edgeOf dart) = 0
      rw [orbitFaceBoundaryLinearMap_apply_edgeOf
        data.toRotationSystem htwoSided]
      simp [faceSetColorIndicator, hleft, hrightSymm]
  · have hright : dartOrbitFace data.toRotationSystem
        (data.toRotationSystem.alpha dart) ∉ faces := by
      exact fun h => hleft (hsame.mpr h)
    have hrightSymm :
        dartOrbitFace data.toRotationSystem (Dart.symm dart) ∉ faces := by
      simpa using hright
    apply Prod.ext
    · change orbitFaceBoundaryLinearMap data.toRotationSystem
          (fun face =>
            (faceSetColorIndicator data faces delta face).1)
          (data.toRotationSystem.edgeOf dart) = 0
      rw [orbitFaceBoundaryLinearMap_apply_edgeOf
        data.toRotationSystem htwoSided]
      simp [faceSetColorIndicator, hleft, hrightSymm]
    · change orbitFaceBoundaryLinearMap data.toRotationSystem
          (fun face =>
            (faceSetColorIndicator data faces delta face).2)
          (data.toRotationSystem.edgeOf dart) = 0
      rw [orbitFaceBoundaryLinearMap_apply_edgeOf
        data.toRotationSystem htwoSided]
      simp [faceSetColorIndicator, hleft, hrightSymm]

/-! ## The face translation is exactly the Kempe switch -/

/-- The colour increment supported on one Kempe component. -/
noncomputable def kempeComponentDelta
    (C : G.EdgeColoring Color) (a b : Color)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    G.edgeSet → Color := by
  classical
  exact fun edge =>
    if edge ∈ C.kempeComponentSet a b K then a + b else 0

/-- If a face set separates precisely one Kempe component, then its coloured
boundary is `a + b` on that component and zero away from it. -/
theorem faceSetBoundaryColor_eq_componentIndicator
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color) {a b : Color}
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (faces : Finset (OrbitFace data.toRotationSystem))
    (hfaces : ∀ dart : data.toRotationSystem.D,
      (data.toRotationSystem.edgeOf dart ∈
          C.kempeComponentSet a b K) ↔
        ((dartOrbitFace data.toRotationSystem dart ∈ faces ∧
            dartOrbitFace data.toRotationSystem
              (data.toRotationSystem.alpha dart) ∉ faces) ∨
          (dartOrbitFace data.toRotationSystem dart ∉ faces ∧
            dartOrbitFace data.toRotationSystem
              (data.toRotationSystem.alpha dart) ∈ faces))) :
    faceSetBoundaryColor data faces (a + b) =
      kempeComponentDelta C a b K := by
  classical
  funext edge
  unfold kempeComponentDelta
  rcases data.toRotationSystem.dartsOn_nonempty edge with ⟨dart, hdart⟩
  have hedge : data.toRotationSystem.edgeOf dart = edge :=
    data.toRotationSystem.mem_dartsOn.mp hdart
  by_cases hcomponent : edge ∈ C.kempeComponentSet a b K
  · have hcomponentDart : data.toRotationSystem.edgeOf dart ∈
        C.kempeComponentSet a b K := by
      rw [hedge]
      exact hcomponent
    have hseparates := (hfaces dart).mp hcomponentDart
    rw [if_pos hcomponent]
    rw [← hedge]
    exact faceSetBoundaryColor_eq_delta_of_separates
      data htwoSided faces (a + b) dart hseparates
  · have hnotSeparates :
        ¬ ((dartOrbitFace data.toRotationSystem dart ∈ faces ∧
              dartOrbitFace data.toRotationSystem
                (data.toRotationSystem.alpha dart) ∉ faces) ∨
            (dartOrbitFace data.toRotationSystem dart ∉ faces ∧
              dartOrbitFace data.toRotationSystem
                (data.toRotationSystem.alpha dart) ∈ faces)) := by
        intro hseparates
        apply hcomponent
        rw [← hedge]
        exact (hfaces dart).mpr hseparates
    have hsame :
        dartOrbitFace data.toRotationSystem dart ∈ faces ↔
          dartOrbitFace data.toRotationSystem
            (data.toRotationSystem.alpha dart) ∈ faces := by
      tauto
    rw [if_neg hcomponent]
    rw [← hedge]
    exact faceSetBoundaryColor_eq_zero_of_sameSide
      data htwoSided faces (a + b) dart hsame

/-- On a two-colour component, adding `a + b` is exactly the transposition of
`a` and `b`; away from the component both operations are the identity. -/
theorem add_componentIndicator_eq_swapOnKempeComponent
    (C : G.EdgeColoring Color) {a b : Color}
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    (fun edge => C edge + kempeComponentDelta C a b K edge) =
      C.swapOnKempeComponent a b K := by
  classical
  funext edge
  unfold kempeComponentDelta
  by_cases hcomponent : edge ∈ C.kempeComponentSet a b K
  · rw [if_pos hcomponent, C.swapOnKempeComponent_apply_of_mem hcomponent]
    rcases C.mem_bicoloredSet_of_mem_kempeComponentSet hcomponent with
      hcolor | hcolor
    · rw [hcolor, Equiv.swap_apply_left]
      calc
        a + (a + b) = (a + a) + b := by abel
        _ = b := by rw [color_add_self, zero_add]
    · rw [hcolor, Equiv.swap_apply_right]
      calc
        b + (a + b) = a + (b + b) := by abel
        _ = a := by rw [color_add_self, add_zero]
  · rw [if_neg hcomponent,
      C.swapOnKempeComponent_apply_of_not_mem hcomponent]
    simp

/-- A Kempe switch on a spherical cubic map is represented by translating
the integrated face potential by the forced third colour `a + b` on an exact
face separator.  In particular, no arbitrary third-colour parameter is
hidden in the parity argument. -/
theorem exists_translated_colorFacePotential_of_swapOnKempeComponent
    (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {a b : Color} (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (coordinates : ColorFacePotential data C) :
    ∃ faces : Finset (OrbitFace data.toRotationSystem),
      Nonempty
        (ColorFacePotential data (C.swapOnKempeComponent a b K)) := by
  rcases exists_faceSet_separates_iff_mem_kempeComponent
      data hclass htwoSided C hC hab K with ⟨faces, hfaces⟩
  refine ⟨faces, ?_⟩
  have hboundary := faceSetBoundaryColor_eq_componentIndicator
    data htwoSided C K faces hfaces
  have hchain :
      (fun edge => C edge + faceSetBoundaryColor data faces (a + b) edge) =
        C.swapOnKempeComponent a b K := by
    rw [hboundary]
    exact add_componentIndicator_eq_swapOnKempeComponent C K
  rw [← hchain]
  exact ⟨coordinates.translate faces (a + b)⟩

end

end GoertzelV24KauffmanFacePotential

end Mettapedia.GraphTheory.FourColor
