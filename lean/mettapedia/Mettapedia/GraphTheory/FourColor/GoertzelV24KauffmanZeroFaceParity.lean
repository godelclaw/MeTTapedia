import Mettapedia.GraphTheory.FourColor.GoertzelV24AlternatingCycleParity
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelAmbientClosureFlow
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedEdgeStructure
import Mettapedia.GraphTheory.FourColor.GoertzelV24KauffmanFacePotential
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceParityBoundary

/-!
# The zero-face term in the Kauffman parity formula

The face-potential proof changes the potential by the third colour on one
side of the operated Kempe circuit.  The only faces whose zero/nonzero
status can change are the selected faces with old potential `0` or the
third colour.  Their relative boundary is a binary primal cycle supported
on the two operated colours.  Such a cycle alternates between the two colour
classes, so it has even size.

This file proves that local parity statement.  The remaining part of the
full Kauffman lemma is the spherical Euler identity relating the three
bicoloured component counts to the zero-face term.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24KauffmanZeroFaceParity

open GoertzelV24AlternatingCycleParity
open GoertzelV24ClosedWebSelectedEdgeStructure
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24KauffmanFacePotential
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCycleSpaceEquality
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceParityBoundary
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PrimalCycleSpace
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

private theorem f2_eq_one_of_ne_zero {value : F2} (hvalue : value ≠ 0) :
    value = 1 := by
  fin_cases value
  · exact False.elim (hvalue rfl)
  · rfl

private theorem f2_add_eq_zero_iff_eq (left right : F2) :
    left + right = 0 ↔ left = right := by
  constructor
  · intro hzero
    calc
      left = left + 0 := by simp
      _ = left + (right + right) := by rw [zmod2_add_self]
      _ = (left + right) + right := by rw [add_assoc]
      _ = right := by rw [hzero]; simp
  · rintro rfl
    exact zmod2_add_self _

/-- The support graph carries exactly the ambient edges on which a binary
chain is nonzero. -/
noncomputable def scalarSupportEdgeEquiv (f : G.edgeSet → F2) :
    (scalarSupportGraph f).edgeSet ≃
      {edge : G.edgeSet // f edge ≠ 0} :=
  (zeroEdgeGraphEdgeEquiv G (scalarSupportComplementChain f)).trans {
    toFun := fun edge =>
      ⟨edge.1,
        (scalarSupportComplementChain_eq_zero_iff f edge.1).mp edge.2⟩
    invFun := fun edge =>
      ⟨edge.1,
        (scalarSupportComplementChain_eq_zero_iff f edge.1).mpr edge.2⟩
    left_inv := fun edge => Subtype.ext rfl
    right_inv := fun edge => Subtype.ext rfl
  }

/-- Cardinal form of `scalarSupportEdgeEquiv`. -/
theorem card_filter_ne_zero_eq_ncard_scalarSupportGraph
    (f : G.edgeSet → F2) :
    ((Finset.univ : Finset G.edgeSet).filter fun edge => f edge ≠ 0).card =
      (scalarSupportGraph f).edgeSet.ncard := by
  classical
  calc
    ((Finset.univ : Finset G.edgeSet).filter
        fun edge => f edge ≠ 0).card =
        Fintype.card {edge : G.edgeSet // f edge ≠ 0} :=
      (Fintype.card_subtype (fun edge : G.edgeSet => f edge ≠ 0)).symm
    _ = Fintype.card (scalarSupportGraph f).edgeSet :=
      (Fintype.card_congr (scalarSupportEdgeEquiv f)).symm
    _ = (scalarSupportGraph f).edgeSet.ncard :=
      Set.fintypeCard_eq_ncard _

/-- Over `F2`, an even number of nonzero coordinates has total sum zero. -/
theorem sum_eq_zero_of_even_scalarSupport
    (f : G.edgeSet → F2)
    (heven : Even (scalarSupportGraph f).edgeSet.ncard) :
    (∑ edge : G.edgeSet, f edge) = 0 := by
  classical
  have hsupportEven : Even
      ((Finset.univ : Finset G.edgeSet).filter fun edge => f edge ≠ 0).card := by
    rw [card_filter_ne_zero_eq_ncard_scalarSupportGraph]
    exact heven
  have hsumSupport :
      (∑ edge : G.edgeSet, f edge) =
        ∑ edge ∈ (Finset.univ : Finset G.edgeSet).filter
          (fun edge => f edge ≠ 0), f edge := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro edge _hedge
    by_cases hzero : f edge = 0 <;> simp [hzero]
  have hone : ∀ edge ∈
      (Finset.univ : Finset G.edgeSet).filter (fun edge => f edge ≠ 0),
      f edge = 1 := by
    intro edge hedge
    exact f2_eq_one_of_ne_zero (Finset.mem_filter.mp hedge).2
  rw [hsumSupport]
  calc
    (∑ edge ∈ (Finset.univ : Finset G.edgeSet).filter
        (fun edge => f edge ≠ 0), f edge) =
        (((Finset.univ : Finset G.edgeSet).filter
          (fun edge => f edge ≠ 0)).card : F2) := by
          rw [Finset.sum_congr rfl hone]
          simp
    _ = 0 := by
      rcases hsupportEven with ⟨half, hhalf⟩
      rw [hhalf, Nat.cast_add]
      exact zmod2_add_self _

/-- Summing a multiplicity-correct face boundary over all edges is the same
as summing the face coefficient over all darts: the edge fibers partition
the dart carrier. -/
theorem sum_orbitFaceParityBoundary_eq_sum_darts
    {E : Type*} [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E)
    (coefficients : OrbitFace RS → F2) :
    (∑ edge : E, orbitFaceParityBoundaryLinearMap RS coefficients edge) =
      ∑ dart : RS.D, coefficients (dartOrbitFace RS dart) := by
  classical
  change (∑ edge : E, ∑ dart ∈ RS.dartsOn edge,
      coefficients (dartOrbitFace RS dart)) =
    ∑ dart : RS.D, coefficients (dartOrbitFace RS dart)
  unfold RotationSystem.dartsOn
  simpa only [Finset.sum_filter] using
    (Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ) (t := Finset.univ) (g := RS.edgeOf)
      (fun dart _ => Finset.mem_univ (RS.edgeOf dart))
      (fun dart => coefficients (dartOrbitFace RS dart)))

/-- On a two-sided map, the same total-incidence identity holds for the
ordinary quotient-face boundary map. -/
theorem sum_orbitFaceBoundary_eq_sum_darts
    {E : Type*} [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (coefficients : OrbitFace RS → F2) :
    (∑ edge : E, orbitFaceBoundaryLinearMap RS coefficients edge) =
      ∑ dart : RS.D, coefficients (dartOrbitFace RS dart) := by
  rw [← orbitFaceParityBoundaryLinearMap_eq_orbitFaceBoundaryLinearMap
    RS htwoSided]
  exact sum_orbitFaceParityBoundary_eq_sum_darts RS coefficients

/-- A binary primal cycle supported on two Tait colours has even support.
The proof passes through its support graph: cubicity makes it a cycle
system, and proper edge colouring makes that system alternate. -/
theorem even_scalarSupport_of_mem_f2CycleSpace_of_colorPair
    (C : G.EdgeColoring Color)
    {a b : Color}
    (f : G.edgeSet → F2)
    (hcycle : f ∈ f2CycleSpace G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hsupport : ∀ edge : G.edgeSet, f edge ≠ 0 →
      C edge = a ∨ C edge = b) :
    Even (scalarSupportGraph f).edgeSet.ncard := by
  classical
  have hflow : ∀ vertex : V,
      scalarVertexKirchhoffSum G f vertex = 0 :=
    scalarVertexKirchhoffSum_eq_zero_of_mem_f2CycleSpace hcycle
  have hcycles : (scalarSupportGraph f).IsCycles :=
    scalarSupportGraph_isCycles f hflow hcubic
  have hle : scalarSupportGraph f ≤ colorPairGraph C a b := by
    intro left right hadj
    have hambient : G.Adj left right := scalarSupportGraph_le f hadj
    let edge : G.edgeSet :=
      ⟨s(left, right), by simpa using hambient⟩
    have hedgeSupport :
        (edge : Sym2 V) ∈ (scalarSupportGraph f).edgeSet := by
      change s(left, right) ∈ (scalarSupportGraph f).edgeSet
      exact (SimpleGraph.mem_edgeSet (scalarSupportGraph f)).2 hadj
    have hf : f edge ≠ 0 :=
      (ambientEdge_mem_scalarSupportGraph_edgeSet_iff f edge).1
        hedgeSupport
    rcases hsupport edge hf with ha | hb
    · exact (colorPairGraph_adj_iff C a b left right).2
        ⟨hambient, Or.inl ha⟩
    · exact (colorPairGraph_adj_iff C a b left right).2
        ⟨hambient, Or.inr hb⟩
  exact even_ncard_edgeSet_of_isCycles_isAlternating hcycles
    ((colorPairGraph_isAlternating_first C a b).mono hle)

/-! ## The selected dyad of face potentials -/

/-- Among the faces selected by the operated Kempe circuit, retain exactly
those whose old potential is zero or the translating colour.  These are
precisely the faces whose zero/nonzero status changes under translation. -/
def selectedDyadFaces
    {data : Data G} {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain)
    (faces : Finset (OrbitFace data.toRotationSystem)) (delta : Color) :
    Finset (OrbitFace data.toRotationSystem) :=
  faces.filter fun face =>
    coordinates.potential face = 0 ∨
      coordinates.potential face = delta

/-- The binary primal boundary of the selected dyad of faces. -/
def selectedDyadBoundary
    {data : Data G} {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain)
    (faces : Finset (OrbitFace data.toRotationSystem)) (delta : Color) :
    G.edgeSet → F2 :=
  orbitFaceBoundaryLinearMap data.toRotationSystem
    (faceSetIndicator data
      (selectedDyadFaces coordinates faces delta))

/-- If one face potential lies in the dyad `{0, a+b}` and the other does
not, then their sum is one of the two colours `a,b`.  This is the four-point
algebra at the heart of the zero-face parity argument. -/
theorem add_mem_pair_of_mem_dyad_of_not_mem_dyad
    {a b left right : Color} (hab : ValidColorPair a b)
    (hleft : left = 0 ∨ left = a + b)
    (hright : ¬ (right = 0 ∨ right = a + b)) :
    left + right = a ∨ left + right = b := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a hab.1 with
      rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hab.2.1 with
      rfl | rfl | rfl <;>
    rcases eq_zero_or_eq_red_or_eq_blue_or_eq_purple left with
      rfl | rfl | rfl | rfl <;>
    rcases eq_zero_or_eq_red_or_eq_blue_or_eq_purple right with
      rfl | rfl | rfl | rfl <;>
    simp_all [ValidColorPair]

/-- A selected dyad boundary is a binary primal cycle because every
quotient-face boundary lies in the spherical primal cycle space. -/
theorem selectedDyadBoundary_mem_f2CycleSpace
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain)
    (faces : Finset (OrbitFace data.toRotationSystem)) (delta : Color) :
    selectedDyadBoundary coordinates faces delta ∈ f2CycleSpace G := by
  exact range_orbitFaceBoundaryLinearMap_le_f2CycleSpace data
    htwoSided ⟨faceSetIndicator data
      (selectedDyadFaces coordinates faces delta), rfl⟩

/-- For an exact face separator of an `a,b` Kempe component, every edge of
the selected-dyad boundary has colour `a` or `b`.  If the two incident faces
lie on opposite sides of the separator, the edge belongs to the component.
If they lie on the same side, their potential values lie on opposite sides
of `{0,a+b}`, and the four-point colour algebra gives the same conclusion. -/
theorem selectedDyadBoundary_supports_only_pair
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color) {a b : Color}
    (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (coordinates : ColorFacePotential data C)
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
    ∀ edge : G.edgeSet,
      selectedDyadBoundary coordinates faces (a + b) edge ≠ 0 →
        C edge = a ∨ C edge = b := by
  classical
  intro edge hedgeBoundary
  rcases data.toRotationSystem.dartsOn_nonempty edge with ⟨dart, hdart⟩
  have hedgeOf : data.toRotationSystem.edgeOf dart = edge :=
    data.toRotationSystem.mem_dartsOn.mp hdart
  have hboundaryOne :
      selectedDyadBoundary coordinates faces (a + b)
        (data.toRotationSystem.edgeOf dart) = 1 := by
    rw [hedgeOf]
    exact f2_eq_one_of_ne_zero hedgeBoundary
  have hseparates :=
    (faceSetBoundary_apply_eq_one_iff_separates data htwoSided
      (selectedDyadFaces coordinates faces (a + b)) dart).mp
      hboundaryOne
  rcases hseparates with ⟨hleftSelected, hrightNotSelected⟩ |
      ⟨hleftNotSelected, hrightSelected⟩
  · have hleftData := Finset.mem_filter.mp hleftSelected
    by_cases hrightFaces :
        dartOrbitFace data.toRotationSystem
            (data.toRotationSystem.alpha dart) ∈ faces
    · have hrightNotDyad :
          ¬ (coordinates.potential
                (dartOrbitFace data.toRotationSystem
                  (data.toRotationSystem.alpha dart)) = 0 ∨
              coordinates.potential
                (dartOrbitFace data.toRotationSystem
                  (data.toRotationSystem.alpha dart)) = a + b) := by
        intro hdyad
        exact hrightNotSelected (Finset.mem_filter.mpr
          ⟨hrightFaces, hdyad⟩)
      have hpair := add_mem_pair_of_mem_dyad_of_not_mem_dyad hab
        hleftData.2 hrightNotDyad
      have hadd := coordinates.incident_add htwoSided dart
      rw [hedgeOf] at hadd
      rcases hpair with hpair | hpair
      · exact Or.inl (hadd.symm.trans hpair)
      · exact Or.inr (hadd.symm.trans hpair)
    · have hcomponent : data.toRotationSystem.edgeOf dart ∈
          C.kempeComponentSet a b K :=
        (hfaces dart).mpr (Or.inl ⟨hleftData.1, hrightFaces⟩)
      rw [hedgeOf] at hcomponent
      exact C.mem_bicoloredSet_of_mem_kempeComponentSet hcomponent
  · have hrightData := Finset.mem_filter.mp hrightSelected
    by_cases hleftFaces :
        dartOrbitFace data.toRotationSystem dart ∈ faces
    · have hleftNotDyad :
          ¬ (coordinates.potential
                (dartOrbitFace data.toRotationSystem dart) = 0 ∨
              coordinates.potential
                (dartOrbitFace data.toRotationSystem dart) = a + b) := by
        intro hdyad
        exact hleftNotSelected (Finset.mem_filter.mpr
          ⟨hleftFaces, hdyad⟩)
      have hpair := add_mem_pair_of_mem_dyad_of_not_mem_dyad hab
        hrightData.2 hleftNotDyad
      have hadd := coordinates.incident_add htwoSided dart
      rw [hedgeOf] at hadd
      rcases hpair with hpair | hpair
      · exact Or.inl (hadd.symm.trans (by simpa [add_comm] using hpair))
      · exact Or.inr (hadd.symm.trans (by simpa [add_comm] using hpair))
    · have hcomponent : data.toRotationSystem.edgeOf dart ∈
          C.kempeComponentSet a b K :=
        (hfaces dart).mpr (Or.inr ⟨hleftFaces, hrightData.1⟩)
      rw [hedgeOf] at hcomponent
      exact C.mem_bicoloredSet_of_mem_kempeComponentSet hcomponent

/-- The relative boundary of the faces whose zero status changes under a
Kempe-component translation contains an even number of edges. -/
theorem even_ncard_selectedDyadBoundary
    (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color) {a b : Color}
    (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (coordinates : ColorFacePotential data C)
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
    Even (scalarSupportGraph
      (selectedDyadBoundary coordinates faces (a + b))).edgeSet.ncard := by
  apply even_scalarSupport_of_mem_f2CycleSpace_of_colorPair C
    (selectedDyadBoundary coordinates faces (a + b))
  · exact selectedDyadBoundary_mem_f2CycleSpace data htwoSided
      coordinates faces (a + b)
  · exact incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      data hclass.spherical.cubic
  · exact selectedDyadBoundary_supports_only_pair data htwoSided C hab K
      coordinates faces hfaces

/-! ## Parity of zero-potential face lengths -/

/-- The binary indicator of the zero fibre of a colour face potential. -/
def zeroPotentialIndicator
    {data : Data G} {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain) :
    OrbitFace data.toRotationSystem → F2 :=
  fun face => if coordinates.potential face = 0 then 1 else 0

/-- The total length of all zero-potential faces, reduced modulo two.  It is
written as a dart sum so repeated visits of a face are counted with their
correct boundary multiplicity. -/
def zeroPotentialParity
    {data : Data G} {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain) : F2 :=
  ∑ dart : data.toRotationSystem.D,
    zeroPotentialIndicator coordinates
      (dartOrbitFace data.toRotationSystem dart)

/-- Pointwise change-of-zero-fibre formula under a nonzero face
translation.  A selected face changes zero status exactly when its old
potential was `0` or `delta`; unselected faces contribute twice and cancel. -/
theorem zeroPotentialIndicator_translate_add
    {data : Data G} {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain)
    (faces : Finset (OrbitFace data.toRotationSystem))
    {delta : Color} (hdelta : delta ≠ 0)
    (face : OrbitFace data.toRotationSystem) :
    zeroPotentialIndicator (coordinates.translate faces delta) face +
        zeroPotentialIndicator coordinates face =
      faceSetIndicator data
        (selectedDyadFaces coordinates faces delta) face := by
  classical
  by_cases hface : face ∈ faces
  · by_cases hzero : coordinates.potential face = 0
    · simp [zeroPotentialIndicator, ColorFacePotential.translate,
        faceSetColorIndicator, faceSetIndicator, selectedDyadFaces,
        hface, hzero, hdelta]
    · by_cases heqDelta : coordinates.potential face = delta
      · simp [zeroPotentialIndicator, ColorFacePotential.translate,
          faceSetColorIndicator, faceSetIndicator, selectedDyadFaces,
          hface, hzero, heqDelta, hdelta]
      · have haddNe : coordinates.potential face + delta ≠ 0 := by
          intro hadd
          exact heqDelta ((add_eq_zero_iff_eq _ _).mp hadd)
        simp [zeroPotentialIndicator, ColorFacePotential.translate,
          faceSetColorIndicator, faceSetIndicator, selectedDyadFaces,
          hface, hzero, heqDelta, haddNe]
  · by_cases hzero : coordinates.potential face = 0 <;>
      simp [zeroPotentialIndicator, ColorFacePotential.translate,
        faceSetColorIndicator, faceSetIndicator, selectedDyadFaces,
        hface, hzero]

/-- A Kempe-component face translation preserves the parity of the total
zero-potential face length. -/
theorem zeroPotentialParity_translate_kempeComponent
    (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color) {a b : Color}
    (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (coordinates : ColorFacePotential data C)
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
    zeroPotentialParity (coordinates.translate faces (a + b)) =
      zeroPotentialParity coordinates := by
  have hdelta : a + b ≠ 0 := add_ne_zero_of_ne hab.2.2
  refine (f2_add_eq_zero_iff_eq
    (zeroPotentialParity (coordinates.translate faces (a + b)))
    (zeroPotentialParity coordinates)).mp ?_
  unfold zeroPotentialParity
  rw [← Finset.sum_add_distrib]
  calc
    (∑ dart : data.toRotationSystem.D,
        (zeroPotentialIndicator (coordinates.translate faces (a + b))
            (dartOrbitFace data.toRotationSystem dart) +
          zeroPotentialIndicator coordinates
            (dartOrbitFace data.toRotationSystem dart))) =
        ∑ dart : data.toRotationSystem.D,
          faceSetIndicator data
            (selectedDyadFaces coordinates faces (a + b))
            (dartOrbitFace data.toRotationSystem dart) := by
      apply Finset.sum_congr rfl
      intro dart _hdart
      exact zeroPotentialIndicator_translate_add coordinates faces
        hdelta (dartOrbitFace data.toRotationSystem dart)
    _ = ∑ edge : G.edgeSet,
          selectedDyadBoundary coordinates faces (a + b) edge := by
      exact (sum_orbitFaceBoundary_eq_sum_darts
        data.toRotationSystem htwoSided
        (faceSetIndicator data
          (selectedDyadFaces coordinates faces (a + b)))).symm
    _ = 0 := sum_eq_zero_of_even_scalarSupport
      (selectedDyadBoundary coordinates faces (a + b))
      (even_ncard_selectedDyadBoundary data hclass htwoSided C hab K
        coordinates faces hfaces)

end

end GoertzelV24KauffmanZeroFaceParity

end Mettapedia.GraphTheory.FourColor
