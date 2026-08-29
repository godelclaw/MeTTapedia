import Mettapedia.GraphTheory.FourColor.GoertzelV24KauffmanDyadBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24KauffmanParity
import Mettapedia.GraphTheory.FourColor.GoertzelV24KauffmanZeroFaceParity

/-!
# The spherical Kauffman formation-parity theorem

For a Tait colouring on a connected spherical cubic map, integrate the edge
colours to a face potential `q`.  For each nonzero colour `x`, the faces with
potential in `{0,x}` form a ribbon subsurface.  Its boundary circles are
exactly the Kempe circuits in the complementary pair, and ribbon Euler parity
gives

`N_complement(x) = |{q = 0 or q = x}| + |internal x-edges|  (mod 2)`.

Adding this identity for the three nonzero colours leaves one copy of every
face and one copy of every dart incident with a zero-potential face.  Thus the
formation parity is the fixed face-count parity plus the zero-potential
boundary-length parity.  The latter was proved invariant under the face
translation representing a Kempe switch, so the source's cross-curve parity
principle follows without a Jordan-curve axiom.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24KauffmanFormationParity

open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceDualConnectedness
open GoertzelV24KauffmanDyadBoundary
open GoertzelV24KauffmanDyadRibbon
open GoertzelV24KauffmanFacePotential
open GoertzelV24KauffmanParity
open GoertzelV24KauffmanZeroFaceParity
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCycleSpace
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The `F2` indicator of a proposition. -/
def parityIndicator (proposition : Prop) [Decidable proposition] : F2 :=
  if proposition then 1 else 0

/-- A fourth nonzero colour distinct from a valid pair is their sum. -/
private theorem remaining_nonzero_color_eq_add
    {q a b : Color} (hq : q ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hqa : q ≠ a) (hqb : q ≠ b) (hab : a ≠ b) :
    q = a + b := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero q hq with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a ha with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hb with rfl | rfl | rfl <;>
    simp_all [red, blue, purple]

/-- The three dyads determined by a valid colour pair cover every face an odd
number of times: three times at potential zero and once otherwise. -/
private theorem three_dyad_indicators_sum_eq_one
    (q a b : Color) (hab : ValidColorPair a b) :
    parityIndicator (q = 0 ∨ q = a + b) +
        parityIndicator (q = 0 ∨ q = b) +
        parityIndicator (q = 0 ∨ q = a) = 1 := by
  have hc := third_color_properties hab.1 hab.2.1 hab.2.2
  by_cases hq0 : q = 0
  · subst q
    simp [parityIndicator]
  by_cases hqa : q = a
  · subst q
    have hac : a ≠ a + b := hc.2.1.symm
    simp [parityIndicator, hab.1, hab.2.2, hac]
  by_cases hqb : q = b
  · subst q
    have hba : b ≠ a := hab.2.2.symm
    have hbc : b ≠ a + b := hc.2.2.symm
    simp [parityIndicator, hab.2.1, hba, hbc]
  have hqc : q = a + b := remaining_nonzero_color_eq_add
    hq0 hab.1 hab.2.1 hqa hqb hab.2.2
  subst q
  simp [parityIndicator, hc.1, hc.2.1, hc.2.2]

/-- Cast the cardinality of a finite set to `F2` as its membership-indicator
sum over the ambient finite type. -/
theorem natCast_card_eq_sum_membership
    {A : Type*} [Fintype A] [DecidableEq A] (set : Finset A) :
    (set.card : F2) = ∑ element : A, parityIndicator (element ∈ set) := by
  simp [parityIndicator]

/-- The three dyad face counts sum to the total face count modulo two. -/
theorem dyadFaces_three_sum_cast
    {data : Data G} {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain)
    {a b : Color} (hab : ValidColorPair a b) :
    (((dyadFaces coordinates (a + b)).card +
          (dyadFaces coordinates b).card +
          (dyadFaces coordinates a).card : Nat) : F2) =
      (Fintype.card (OrbitFace data.toRotationSystem) : F2) := by
  rw [Nat.cast_add, Nat.cast_add,
    natCast_card_eq_sum_membership,
    natCast_card_eq_sum_membership,
    natCast_card_eq_sum_membership]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  change Finset.univ.sum (fun face : OrbitFace data.toRotationSystem =>
      (parityIndicator (face ∈ dyadFaces coordinates (a + b)) +
        parityIndicator (face ∈ dyadFaces coordinates b)) +
        parityIndicator (face ∈ dyadFaces coordinates a)) = _
  rw [show (Fintype.card (OrbitFace data.toRotationSystem) : F2) =
      ∑ _face : OrbitFace data.toRotationSystem, (1 : F2) by simp]
  apply Finset.sum_congr rfl
  intro face _hface
  simp only [mem_dyadFaces_iff]
  exact three_dyad_indicators_sum_eq_one
    (coordinates.potential face) a b hab

/-- The local `F2` indicator that an edge of colour `edgeColor` is internal to
the potential dyad `{0,x}`, using one chosen incident face value `q`. -/
def internalDyadIndicator (edgeColor q x : Color) : F2 :=
  parityIndicator (edgeColor = x ∧ (q = 0 ∨ q = x))

/-- For one edge, summing the three internal-dyad indicators gives the number
of its zero-potential incident sides modulo two. -/
private theorem single_internal_indicator_eq_zero_sides
    (edgeColor q r : Color) (hedgeColor : edgeColor ≠ 0)
    (hincident : q + r = edgeColor) :
    parityIndicator (q = 0 ∨ q = edgeColor) =
      parityIndicator (q = 0) + parityIndicator (r = 0) := by
  have hr0 : r = 0 ↔ q = edgeColor := by
    constructor
    · intro hr
      simpa [hr] using hincident
    · intro hq
      subst q
      apply add_left_cancel (a := edgeColor)
      simpa using hincident
  by_cases hq0 : q = 0
  · have hrne : r ≠ 0 := by
      intro hr
      rw [hq0, hr, zero_add] at hincident
      exact hedgeColor hincident.symm
    simp [parityIndicator, hq0, hrne]
  by_cases hqedge : q = edgeColor
  · have hr : r = 0 := hr0.mpr hqedge
    simp [parityIndicator, hqedge, hr, hedgeColor]
  · have hrne : r ≠ 0 := fun hr => hqedge (hr0.mp hr)
    simp [parityIndicator, hq0, hqedge, hrne]

private theorem three_internal_indicators_eq_zero_sides
    (edgeColor q r a b : Color)
    (hab : ValidColorPair a b) (hedgeColor : edgeColor ≠ 0)
    (hincident : q + r = edgeColor) :
    internalDyadIndicator edgeColor q (a + b) +
        internalDyadIndicator edgeColor q b +
        internalDyadIndicator edgeColor q a =
      parityIndicator (q = 0) + parityIndicator (r = 0) := by
  have hc := third_color_properties hab.1 hab.2.1 hab.2.2
  have hcases : edgeColor = a ∨ edgeColor = b ∨ edgeColor = a + b := by
    by_cases hea : edgeColor = a
    · exact Or.inl hea
    by_cases heb : edgeColor = b
    · exact Or.inr (Or.inl heb)
    exact Or.inr (Or.inr (remaining_nonzero_color_eq_add
      hedgeColor hab.1 hab.2.1 hea heb hab.2.2))
  rcases hcases with hea | heb | hec
  · rw [hea] at hincident ⊢
    simpa [internalDyadIndicator, parityIndicator, hab.1, hab.2.1,
      hab.2.2, hc.2.1, hc.2.2] using
        single_internal_indicator_eq_zero_sides a q r hab.1 hincident
  · rw [heb] at hincident ⊢
    simpa [internalDyadIndicator, parityIndicator, hab.1, hab.2.1,
      hab.2.2, hab.2.2.symm, hc.2.1, hc.2.2] using
        single_internal_indicator_eq_zero_sides b q r hab.2.1 hincident
  · rw [hec] at hincident ⊢
    simpa [internalDyadIndicator, parityIndicator, hc.1,
      hc.2.1, hc.2.2] using
        single_internal_indicator_eq_zero_sides (a + b) q r hc.1 hincident

/-- A sum over all darts may be regrouped into the two darts over each edge,
represented by `chosenDart` and its `alpha` mate. -/
theorem sum_darts_eq_sum_edges_chosen_alpha
    {data : Data G} (value : data.toRotationSystem.D → F2) :
    (∑ dart : data.toRotationSystem.D, value dart) =
      ∑ edge : G.edgeSet,
        (value (chosenDart data.toRotationSystem edge) +
          value (data.toRotationSystem.alpha
            (chosenDart data.toRotationSystem edge))) := by
  let RS := data.toRotationSystem
  calc
    (∑ dart : RS.D, value dart) =
        ∑ edge : G.edgeSet,
          ∑ dart ∈ RS.dartsOn edge, value dart := by
      unfold RotationSystem.dartsOn
      rw [Finset.sum_fiberwise_eq_sum_filter
        (Finset.univ : Finset RS.D) (Finset.univ : Finset G.edgeSet)
        RS.edgeOf value]
      simp
    _ = ∑ edge : G.edgeSet,
        (value (chosenDart RS edge) +
          value (RS.alpha (chosenDart RS edge))) := by
      apply Finset.sum_congr rfl
      intro edge _hedge
      have hchosen : chosenDart RS edge ∈ RS.dartsOn edge := by
        rw [RS.mem_dartsOn]
        exact chosenDart_edgeOf RS edge
      rw [RS.dartsOn_eq_pair_of_mem hchosen]
      have hne : chosenDart RS edge ≠ RS.alpha (chosenDart RS edge) :=
        (RS.alpha_fixfree (chosenDart RS edge)).symm
      simp [hne]

/-- The sum of the three internal-dyad edge counts is exactly the parity of
the zero-potential face boundary length. -/
theorem internalDyadEdges_three_sum_cast
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (coordinates : ColorFacePotential data C)
    {a b : Color} (hab : ValidColorPair a b) :
    (((internalDyadEdges C coordinates (a + b)).card +
          (internalDyadEdges C coordinates b).card +
          (internalDyadEdges C coordinates a).card : Nat) : F2) =
      zeroPotentialParity coordinates := by
  rw [Nat.cast_add, Nat.cast_add,
    natCast_card_eq_sum_membership,
    natCast_card_eq_sum_membership,
    natCast_card_eq_sum_membership]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [show zeroPotentialParity coordinates =
      ∑ edge : G.edgeSet,
        (zeroPotentialIndicator coordinates
            (dartOrbitFace data.toRotationSystem
              (chosenDart data.toRotationSystem edge)) +
          zeroPotentialIndicator coordinates
            (dartOrbitFace data.toRotationSystem
              (data.toRotationSystem.alpha
                (chosenDart data.toRotationSystem edge)))) by
    unfold zeroPotentialParity
    exact sum_darts_eq_sum_edges_chosen_alpha
      (fun dart => zeroPotentialIndicator coordinates
        (dartOrbitFace data.toRotationSystem dart))]
  apply Finset.sum_congr rfl
  intro edge _hedge
  simp only [mem_internalDyadEdges_iff, mem_dyadFaces_iff]
  change
    (internalDyadIndicator (C edge)
        (coordinates.potential (dartOrbitFace data.toRotationSystem
          (chosenDart data.toRotationSystem edge))) (a + b) +
      internalDyadIndicator (C edge)
        (coordinates.potential (dartOrbitFace data.toRotationSystem
          (chosenDart data.toRotationSystem edge))) b) +
      internalDyadIndicator (C edge)
        (coordinates.potential (dartOrbitFace data.toRotationSystem
          (chosenDart data.toRotationSystem edge))) a = _
  exact three_internal_indicators_eq_zero_sides
    (C edge)
    (coordinates.potential (dartOrbitFace data.toRotationSystem
      (chosenDart data.toRotationSystem edge)))
    (coordinates.potential (dartOrbitFace data.toRotationSystem
      (data.toRotationSystem.alpha
        (chosenDart data.toRotationSystem edge))))
    a b hab (hC edge)
    (by
      have hadd := coordinates.incident_add htwoSided
        (chosenDart data.toRotationSystem edge)
      rw [chosenDart_edgeOf] at hadd
      exact hadd)

/-- Cast form of the one-dyad ribbon Euler identity. -/
theorem bicoloredComponentCount_cast_eq_dyad
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (coordinates : ColorFacePotential data C)
    {a b : Color} (hab : ValidColorPair a b) :
    (bicoloredComponentCount C a b : F2) =
      ((dyadFaces coordinates (a + b)).card : F2) +
        ((internalDyadEdges C coordinates (a + b)).card : F2) := by
  have hmod := bicoloredComponentCount_mod_two_eq_dyad
    data htwoSided hcubic hrotation C hC coordinates hab
  have hcast : (bicoloredComponentCount C a b : F2) =
      (((dyadFaces coordinates (a + b)).card +
        (internalDyadEdges C coordinates (a + b)).card : Nat) : F2) :=
    (ZMod.natCast_eq_natCast_iff'
      (bicoloredComponentCount C a b)
      ((dyadFaces coordinates (a + b)).card +
        (internalDyadEdges C coordinates (a + b)).card) 2).2 hmod
  simpa only [Nat.cast_add] using hcast

/-- A finite cubic rotation system has an even number of vertices. -/
theorem even_card_vertices_of_isCubic
    (RS : RotationSystem V G.edgeSet) (hcubic : RS.IsCubic) :
    Even (Fintype.card V) := by
  have hthree := RS.card_darts_eq_three_times_card_vertices hcubic
  have htwo := RS.card_darts_eq_twice_card_edges
  have hbalance : 3 * Fintype.card V = 2 * Fintype.card G.edgeSet := by
    omega
  have hevenThree : Even (3 * Fintype.card V) := by
    rw [hbalance]
    exact even_two_mul _
  rcases (Nat.even_mul.mp hevenThree) with hthreeEven | hverticesEven
  · norm_num [Nat.even_iff] at hthreeEven
  · exact hverticesEven

/-- **Tutte--Kauffman formation formula.**  On a connected spherical cubic
map, the parity of the three Kempe-circuit counts is the fixed face-count
parity plus the boundary-length parity of the zero face-potential fibre. -/
theorem formationCurveCount_cast_eq_face_add_zeroPotentialParity
    (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (coordinates : ColorFacePotential data C)
    {a b : Color} (hab : ValidColorPair a b) :
    (formationCurveCount C a b (a + b) : F2) =
      (Fintype.card (OrbitFace data.toRotationSystem) : F2) +
        zeroPotentialParity coordinates := by
  have hc := third_color_properties hab.1 hab.2.1 hab.2.2
  have hac : ValidColorPair a (a + b) :=
    ⟨hab.1, hc.1, hc.2.1.symm⟩
  have hbc : ValidColorPair b (a + b) :=
    ⟨hab.2.1, hc.1, hc.2.2.symm⟩
  have habCount := bicoloredComponentCount_cast_eq_dyad
    data htwoSided hclass.spherical.cubic hclass.vertexRotationCyclic
    C hC coordinates hab
  have hacCount := bicoloredComponentCount_cast_eq_dyad
    data htwoSided hclass.spherical.cubic hclass.vertexRotationCyclic
    C hC coordinates hac
  have hbcCount := bicoloredComponentCount_cast_eq_dyad
    data htwoSided hclass.spherical.cubic hclass.vertexRotationCyclic
    C hC coordinates hbc
  have haac : a + (a + b) = b := by
    rw [← add_assoc, color_add_self, zero_add]
  have hbac : b + (a + b) = a := by
    calc
      b + (a + b) = a + (b + b) := by abel
      _ = a := by rw [color_add_self, add_zero]
  rw [haac] at hacCount
  rw [hbac] at hbcCount
  have hfaces := dyadFaces_three_sum_cast coordinates hab
  have hinternal := internalDyadEdges_three_sum_cast
    data htwoSided C hC coordinates hab
  have hfaces' :
      ((dyadFaces coordinates (a + b)).card : F2) +
          ((dyadFaces coordinates b).card : F2) +
          ((dyadFaces coordinates a).card : F2) =
        (Fintype.card (OrbitFace data.toRotationSystem) : F2) := by
    simpa only [Nat.cast_add] using hfaces
  have hinternal' :
      ((internalDyadEdges C coordinates (a + b)).card : F2) +
          ((internalDyadEdges C coordinates b).card : F2) +
          ((internalDyadEdges C coordinates a).card : F2) =
        zeroPotentialParity coordinates := by
    simpa only [Nat.cast_add] using hinternal
  unfold formationCurveCount
  simp only [Nat.cast_add]
  rw [habCount, hacCount, hbcCount]
  rw [← hfaces', ← hinternal']
  abel

/-- The face potential after a Kempe switch can be chosen so that its
zero-fibre boundary parity is literally the same as before the switch. -/
theorem exists_switched_colorFacePotential_zeroPotentialParity_eq
    (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {a b : Color} (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (coordinates : ColorFacePotential data C) :
    ∃ switchedCoordinates :
        ColorFacePotential data (C.swapOnKempeComponent a b K),
      zeroPotentialParity switchedCoordinates =
        zeroPotentialParity coordinates := by
  rcases exists_faceSet_separates_iff_mem_kempeComponent
      data hclass htwoSided C hC hab K with ⟨faces, hfaces⟩
  have hzero := zeroPotentialParity_translate_kempeComponent
    data hclass htwoSided C hab K coordinates faces hfaces
  have hboundary := faceSetBoundaryColor_eq_componentIndicator
    data htwoSided C K faces hfaces
  have hchain :
      (fun edge => C edge + faceSetBoundaryColor data faces (a + b) edge) =
        C.swapOnKempeComponent a b K := by
    rw [hboundary]
    exact add_componentIndicator_eq_swapOnKempeComponent C K
  rw [← hchain]
  exact ⟨coordinates.translate faces (a + b), hzero⟩

/-- **Spherical Kauffman parity, fully discharged.**  A Kempe switch on one
`(a,b)` circuit preserves the parity of the total three-formation curve
count for the three nonzero colours `a`, `b`, and `a+b`. -/
theorem formationParity_swapOnKempeComponent_spherical
    (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {a b : Color} (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    formationParity (C.swapOnKempeComponent a b K) a b (a + b) =
      formationParity C a b (a + b) := by
  rcases exists_colorFacePotential_of_tait data hclass htwoSided C hC with
    ⟨coordinates⟩
  rcases exists_switched_colorFacePotential_zeroPotentialParity_eq
      data hclass htwoSided C hC hab K coordinates with
    ⟨switchedCoordinates, hzero⟩
  have hC' : IsTaitEdgeColoring G (C.swapOnKempeComponent a b K) :=
    GoertzelV24FramedTrail.isTaitEdgeColoring_swapOnKempeComponent hC hab K
  have hold := formationCurveCount_cast_eq_face_add_zeroPotentialParity
    data hclass htwoSided C hC coordinates hab
  have hnew := formationCurveCount_cast_eq_face_add_zeroPotentialParity
    data hclass htwoSided (C.swapOnKempeComponent a b K) hC'
      switchedCoordinates hab
  rw [hzero] at hnew
  have hcast :
      (formationCurveCount (C.swapOnKempeComponent a b K) a b (a + b) : F2) =
        (formationCurveCount C a b (a + b) : F2) :=
    hnew.trans hold.symm
  unfold formationParity
  exact (ZMod.natCast_eq_natCast_iff'
    (formationCurveCount (C.swapOnKempeComponent a b K) a b (a + b))
    (formationCurveCount C a b (a + b)) 2).1 hcast

/-- The source's two-cross-pair parity statement, now with its exact Tait and
spherical hypotheses rather than the legacy graph-only receipt. -/
theorem crossPairParity_swapOnKempeComponent_spherical
    (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {a b : Color} (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    (bicoloredComponentCount (C.swapOnKempeComponent a b K) a (a + b) +
        bicoloredComponentCount (C.swapOnKempeComponent a b K) b (a + b)) % 2 =
      (bicoloredComponentCount C a (a + b) +
        bicoloredComponentCount C b (a + b)) % 2 := by
  have hformation := formationParity_swapOnKempeComponent_spherical
    data hclass htwoSided C hC hab K
  have hsame := bicoloredComponentCount_swapOnKempeComponent C a b K
  unfold formationParity formationCurveCount at hformation
  omega

/-- The five-versus-four contradiction in the exact spherical setting used by
the repaired Kauffman lane. -/
theorem not_five_and_four_of_spherical_swap
    (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {a b : Color} (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (hfive : formationCurveCount C a b (a + b) = 5)
    (hfour : formationCurveCount
      (C.swapOnKempeComponent a b K) a b (a + b) = 4) : False :=
  not_five_and_four_of_parity
    (formationParity_swapOnKempeComponent_spherical
      data hclass htwoSided C hC hab K).symm hfive hfour

end

end GoertzelV24KauffmanFormationParity

end Mettapedia.GraphTheory.FourColor
