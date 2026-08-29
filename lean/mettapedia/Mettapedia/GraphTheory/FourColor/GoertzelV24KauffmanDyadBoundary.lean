import Mettapedia.GraphTheory.FourColor.GoertzelV24KauffmanDyadRibbon
import Mettapedia.GraphTheory.FourColor.GoertzelV24InducedHexCorridorTypes
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutFaceReturnProfile

/-!
# Exact boundary carrier of a face-potential dyad

For a nonzero colour `x`, the dyad `{0,x}` cuts an edge exactly when the
edge colour is different from `x`.  Thus every complementary-colour edge has
exactly one incident dart in the selected dyad.  This file packages that
fact as an explicit equivalence between selected boundary darts and
complementary-colour edges.

This is the carrier-level bridge needed to compare the ribbon boundary
permutation with the ordinary two-colour Kempe components.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24KauffmanDyadBoundary

open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceDualConnectedness
open GoertzelV24KauffmanDyadRibbon
open GoertzelV24KauffmanFacePotential
open GoertzelV24KauffmanFaceRibbonParity
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24PermutationOrbitParity
open GoertzelV24PermutationOrbitSurgery
open GoertzelV24RotationCycleSpace
open GoertzelV24SeamFaceArc
open GoertzelV24SimpleGraphTaitBridge
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

private theorem color_mem_dyad_iff_iff_add_eq
    {left right x : Color} (hne : left ≠ right) (hx : x ≠ 0) :
    (((left = 0 ∨ left = x) ↔ (right = 0 ∨ right = x)) ↔
      left + right = x) := by
  rcases eq_zero_or_eq_red_or_eq_blue_or_eq_purple left with
      rfl | rfl | rfl | rfl <;>
    rcases eq_zero_or_eq_red_or_eq_blue_or_eq_purple right with
      rfl | rfl | rfl | rfl <;>
    rcases eq_zero_or_eq_red_or_eq_blue_or_eq_purple x with
      rfl | rfl | rfl | rfl <;>
    simp_all [red, blue, purple]

/-- The two incident face potentials lie on the same side of `{0,x}` exactly
when their nonzero difference is `x`. -/
theorem incident_mem_dyad_iff_iff_chain_eq
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain)
    (hnonzero : ∀ edge, chain edge ≠ 0) {x : Color} (hx : x ≠ 0)
    (dart : data.toRotationSystem.D) :
    ((dartOrbitFace data.toRotationSystem dart ∈ dyadFaces coordinates x) ↔
        (dartOrbitFace data.toRotationSystem
          (data.toRotationSystem.alpha dart) ∈ dyadFaces coordinates x)) ↔
      chain (data.toRotationSystem.edgeOf dart) = x := by
  rw [mem_dyadFaces_iff, mem_dyadFaces_iff]
  have hadd := coordinates.incident_add htwoSided dart
  have hne := coordinates.incident_ne htwoSided hnonzero dart
  rw [← hadd]
  exact color_mem_dyad_iff_iff_add_eq hne hx

/-- Equivalently, a non-`x` edge has exactly one dart-side face in the
selected dyad. -/
theorem incident_mem_dyad_xor_iff_chain_ne
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain)
    (hnonzero : ∀ edge, chain edge ≠ 0) {x : Color} (hx : x ≠ 0)
    (dart : data.toRotationSystem.D) :
    (((dartOrbitFace data.toRotationSystem dart ∈ dyadFaces coordinates x) ∧
        (dartOrbitFace data.toRotationSystem
          (data.toRotationSystem.alpha dart) ∉ dyadFaces coordinates x)) ∨
      ((dartOrbitFace data.toRotationSystem dart ∉ dyadFaces coordinates x) ∧
        (dartOrbitFace data.toRotationSystem
          (data.toRotationSystem.alpha dart) ∈ dyadFaces coordinates x))) ↔
      chain (data.toRotationSystem.edgeOf dart) ≠ x := by
  have hsame := incident_mem_dyad_iff_iff_chain_eq data htwoSided
    coordinates hnonzero hx dart
  tauto

/-- Selected dart-sides lying on the actual boundary of the dyad. -/
abbrev DyadBoundaryDart
    {data : Data G} {chain : G.edgeSet → Color}
  (coordinates : ColorFacePotential data chain) (x : Color) :=
  {dart : SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x) //
    chain (data.toRotationSystem.edgeOf dart.1) ≠ x}

/-- Edges carrying one of the colours complementary to `x`. -/
abbrev ComplementaryEdge
    (chain : G.edgeSet → Color) (x : Color) :=
  {edge : G.edgeSet // chain edge ≠ x}

/-- Choose the unique selected dart-side of a complementary edge. -/
def selectedDartOfComplementaryEdge
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain)
    (hnonzero : ∀ edge, chain edge ≠ 0) {x : Color} (hx : x ≠ 0)
    (edge : ComplementaryEdge chain x) :
    DyadBoundaryDart coordinates x := by
  let dart := chosenDart data.toRotationSystem edge.1
  have hedge : data.toRotationSystem.edgeOf dart = edge.1 :=
    chosenDart_edgeOf data.toRotationSystem edge.1
  have hedgeNe : chain (data.toRotationSystem.edgeOf dart) ≠ x := by
    rw [hedge]
    exact edge.2
  have hxor := (incident_mem_dyad_xor_iff_chain_ne data htwoSided
    coordinates hnonzero hx dart).2 hedgeNe
  by_cases hleft : dartOrbitFace data.toRotationSystem dart ∈
      dyadFaces coordinates x
  · exact ⟨⟨dart, hleft⟩, hedgeNe⟩
  · have hright : dartOrbitFace data.toRotationSystem
        (data.toRotationSystem.alpha dart) ∈ dyadFaces coordinates x := by
      rcases hxor with hxor | hxor
      · exact False.elim (hleft hxor.1)
      · exact hxor.2
    refine ⟨⟨data.toRotationSystem.alpha dart, hright⟩, ?_⟩
    rw [data.toRotationSystem.edge_alpha dart]
    exact hedgeNe

/-- Forgetting the selected dart-side recovers the complementary edge. -/
def dyadBoundaryDartToComplementaryEdge
    {data : Data G} {chain : G.edgeSet → Color}
    {coordinates : ColorFacePotential data chain} {x : Color} :
    DyadBoundaryDart coordinates x → ComplementaryEdge chain x :=
  fun dart => ⟨data.toRotationSystem.edgeOf dart.1.1, dart.2⟩

theorem edgeOf_selectedDartOfComplementaryEdge
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain)
    (hnonzero : ∀ edge, chain edge ≠ 0) {x : Color} (hx : x ≠ 0)
    (edge : ComplementaryEdge chain x) :
    data.toRotationSystem.edgeOf
        (selectedDartOfComplementaryEdge data htwoSided coordinates
          hnonzero hx edge).1.1 = edge.1 := by
  unfold selectedDartOfComplementaryEdge
  dsimp only
  split
  · exact chosenDart_edgeOf data.toRotationSystem edge.1
  · rw [data.toRotationSystem.edge_alpha]
    exact chosenDart_edgeOf data.toRotationSystem edge.1

theorem dyadBoundaryDartToComplementaryEdge_selectedDart
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain)
    (hnonzero : ∀ edge, chain edge ≠ 0) {x : Color} (hx : x ≠ 0)
    (edge : ComplementaryEdge chain x) :
    dyadBoundaryDartToComplementaryEdge
        (selectedDartOfComplementaryEdge data htwoSided coordinates
          hnonzero hx edge) = edge := by
  apply Subtype.ext
  exact edgeOf_selectedDartOfComplementaryEdge data htwoSided coordinates
    hnonzero hx edge

theorem selectedDartOfComplementaryEdge_dyadBoundaryDart
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain)
    (hnonzero : ∀ edge, chain edge ≠ 0) {x : Color} (hx : x ≠ 0)
    (dart : DyadBoundaryDart coordinates x) :
    selectedDartOfComplementaryEdge data htwoSided coordinates hnonzero hx
        (dyadBoundaryDartToComplementaryEdge dart) = dart := by
  apply Subtype.ext
  apply Subtype.ext
  let selected := selectedDartOfComplementaryEdge data htwoSided
    coordinates hnonzero hx (dyadBoundaryDartToComplementaryEdge dart)
  have hselectedEdge : data.toRotationSystem.edgeOf selected.1.1 =
      data.toRotationSystem.edgeOf dart.1.1 :=
    edgeOf_selectedDartOfComplementaryEdge data htwoSided coordinates
      hnonzero hx (dyadBoundaryDartToComplementaryEdge dart)
  rcases data.toRotationSystem.edge_fiber_two_cases hselectedEdge rfl with
      heq | heq
  · exact heq.symm
  · have hxor := (incident_mem_dyad_xor_iff_chain_ne data htwoSided
      coordinates hnonzero hx selected.1.1).2 selected.2
    have hoppositeNot : dartOrbitFace data.toRotationSystem
        (data.toRotationSystem.alpha selected.1.1) ∉
          dyadFaces coordinates x := by
      rcases hxor with hxor | hxor
      · exact hxor.2
      · exact False.elim (hxor.1 selected.1.2)
    exact False.elim (hoppositeNot (heq ▸ dart.1.2))

/-- A complementary-colour edge has exactly one selected incident dart-side. -/
def dyadBoundaryDartEquivComplementaryEdge
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain)
    (hnonzero : ∀ edge, chain edge ≠ 0) {x : Color} (hx : x ≠ 0) :
    DyadBoundaryDart coordinates x ≃ ComplementaryEdge chain x where
  toFun := dyadBoundaryDartToComplementaryEdge
  invFun := selectedDartOfComplementaryEdge data htwoSided coordinates
    hnonzero hx
  left_inv := selectedDartOfComplementaryEdge_dyadBoundaryDart data
    htwoSided coordinates hnonzero hx
  right_inv := dyadBoundaryDartToComplementaryEdge_selectedDart data
    htwoSided coordinates hnonzero hx

private theorem color_ne_third_iff_eq_left_or_right
    {value left right : Color} (hvalue : value ≠ 0)
    (hpair : ValidColorPair left right) :
    value ≠ left + right ↔ value = left ∨ value = right := by
  rcases eq_zero_or_eq_red_or_eq_blue_or_eq_purple value with
      rfl | rfl | rfl | rfl <;>
    rcases eq_zero_or_eq_red_or_eq_blue_or_eq_purple left with
      rfl | rfl | rfl | rfl <;>
    rcases eq_zero_or_eq_red_or_eq_blue_or_eq_purple right with
      rfl | rfl | rfl | rfl <;>
    simp_all [ValidColorPair, red, blue, purple]

/-- For a valid colour pair, the colours complementary to `a+b` are exactly
`a` and `b`. -/
theorem chain_ne_third_iff_mem_bicoloredSet
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {a b : Color} (hab : ValidColorPair a b) (edge : G.edgeSet) :
    C edge ≠ a + b ↔ edge ∈ C.bicoloredSet a b := by
  exact color_ne_third_iff_eq_left_or_right (hC edge) hab

/-- The selected boundary-dart carrier is canonically the vertex carrier of
the complementary two-colour line subgraph. -/
def dyadBoundaryDartEquivBicoloredEdge
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (coordinates : ColorFacePotential data C)
    {a b : Color} (hab : ValidColorPair a b) :
    DyadBoundaryDart coordinates (a + b) ≃
      {edge : G.edgeSet // edge ∈ C.bicoloredSet a b} :=
  (dyadBoundaryDartEquivComplementaryEdge data htwoSided coordinates hC
      (add_ne_zero_of_ne hab.2.2)).trans
    (Equiv.subtypeEquiv (Equiv.refl G.edgeSet) (fun edge =>
      chain_ne_third_iff_mem_bicoloredSet C hC hab edge))

/-- In particular, the dyad boundary has one oriented selected dart for every
edge of the complementary two-colour subgraph. -/
theorem card_dyadBoundaryDart_eq_card_bicoloredSet
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (coordinates : ColorFacePotential data C)
    {a b : Color} (hab : ValidColorPair a b) :
    Fintype.card (DyadBoundaryDart coordinates (a + b)) =
      Fintype.card {edge : G.edgeSet // edge ∈ C.bicoloredSet a b} :=
  Fintype.card_congr
    (dyadBoundaryDartEquivBicoloredEdge data htwoSided C hC coordinates hab)

/-! ## The literal gluing involution -/

/-- Flip a selected dart across its edge exactly when that edge has the dyad
colour `x`.  Such an edge has both incident faces in the dyad, so the result
is again a selected dart.  Boundary-colour darts are fixed. -/
def dyadGlueDart
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color) :
    SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x) →
      SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x) :=
  fun dart =>
    if hedge : C (data.toRotationSystem.edgeOf dart.1) = x then
      ⟨data.toRotationSystem.alpha dart.1,
        (incident_mem_dyad_iff_of_chain_eq data htwoSided coordinates x
          dart.1 hedge).mp dart.2⟩
    else dart

@[simp]
theorem dyadGlueDart_apply_of_eq
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color)
    (dart : SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x))
    (hedge : C (data.toRotationSystem.edgeOf dart.1) = x) :
    (dyadGlueDart data htwoSided C coordinates x dart).1 =
      data.toRotationSystem.alpha dart.1 := by
  unfold dyadGlueDart
  split
  · rfl
  · contradiction

@[simp]
theorem dyadGlueDart_apply_of_ne
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color)
    (dart : SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x))
    (hedge : C (data.toRotationSystem.edgeOf dart.1) ≠ x) :
    dyadGlueDart data htwoSided C coordinates x dart = dart := by
  unfold dyadGlueDart
  split
  · contradiction
  · rfl

theorem dyadGlueDart_involutive
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color) :
    Function.Involutive (dyadGlueDart data htwoSided C coordinates x) := by
  intro dart
  by_cases hedge : C (data.toRotationSystem.edgeOf dart.1) = x
  · let flipped := dyadGlueDart data htwoSided C coordinates x dart
    have hflipped : flipped.1 = data.toRotationSystem.alpha dart.1 :=
      dyadGlueDart_apply_of_eq data htwoSided C coordinates x dart hedge
    have hedgeFlipped : C (data.toRotationSystem.edgeOf flipped.1) = x := by
      rw [hflipped, data.toRotationSystem.edge_alpha]
      exact hedge
    apply Subtype.ext
    rw [dyadGlueDart_apply_of_eq data htwoSided C coordinates x
      flipped hedgeFlipped, hflipped, data.toRotationSystem.alpha_involutive]
  · rw [dyadGlueDart_apply_of_ne data htwoSided C coordinates x dart hedge]
    exact dyadGlueDart_apply_of_ne data htwoSided C coordinates x dart hedge

/-- The edge-gluing involution on all selected face darts. -/
def dyadGluePerm
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color) :
    Equiv.Perm
      (SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x)) :=
  { toFun := dyadGlueDart data htwoSided C coordinates x
    invFun := dyadGlueDart data htwoSided C coordinates x
    left_inv := dyadGlueDart_involutive data htwoSided C coordinates x
    right_inv := dyadGlueDart_involutive data htwoSided C coordinates x }

/-- The canonical ribbon successor: first follow the boundary of the current
face sector, then cross an internal `x`-edge when one is encountered. -/
def canonicalDyadRibbonPerm
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color) :
    Equiv.Perm
      (SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x)) :=
  dyadGluePerm data htwoSided C coordinates x *
    selectedFacePerm data.toRotationSystem (dyadFaces coordinates x)

@[simp]
theorem canonicalDyadRibbonPerm_apply_val
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color)
    (dart : SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x)) :
    (canonicalDyadRibbonPerm data htwoSided C coordinates x dart).1 =
      (dyadGlueDart data htwoSided C coordinates x
        (selectedFacePerm data.toRotationSystem
          (dyadFaces coordinates x) dart)).1 := by
  change (dyadGluePerm data htwoSided C coordinates x
    (selectedFacePerm data.toRotationSystem
      (dyadFaces coordinates x) dart)).1 = _
  rfl

/-- Every selected side of an `x`-edge belongs to the concrete internal-edge
list used by the face-ribbon surgery. -/
theorem edgeOf_mem_internalDyadEdges_of_selected_eq
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color)
    (dart : SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x))
    (hedge : C (data.toRotationSystem.edgeOf dart.1) = x) :
    data.toRotationSystem.edgeOf dart.1 ∈
      internalDyadEdges C coordinates x := by
  apply (mem_internalDyadEdges_iff C coordinates x _).2
  refine ⟨hedge, ?_⟩
  let chosen := chosenDart data.toRotationSystem
    (data.toRotationSystem.edgeOf dart.1)
  have hchosenEdge : data.toRotationSystem.edgeOf chosen =
      data.toRotationSystem.edgeOf dart.1 :=
    chosenDart_edgeOf data.toRotationSystem _
  change dartOrbitFace data.toRotationSystem chosen ∈ dyadFaces coordinates x
  rcases data.toRotationSystem.edge_fiber_two_cases hchosenEdge rfl with
      hdart | hdart
  · rw [← hdart]
    exact dart.2
  · have halphaSelected : dartOrbitFace data.toRotationSystem
        (data.toRotationSystem.alpha dart.1) ∈ dyadFaces coordinates x :=
      (incident_mem_dyad_iff_of_chain_eq data htwoSided coordinates x
        dart.1 hedge).mp dart.2
    have hchosen : chosen = data.toRotationSystem.alpha dart.1 := by
      apply data.toRotationSystem.alpha.injective
      rw [data.toRotationSystem.alpha_involutive]
      exact hdart.symm
    rw [hchosen]
    exact halphaSelected

/-- A listed internal pair has colour `x` on both endpoints. -/
theorem internalDyadPairList_endpoint_color
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color)
    (pair : SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x) ×
      SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x))
    (hpair : pair ∈ internalDyadPairList htwoSided C coordinates x) :
    C (data.toRotationSystem.edgeOf pair.1.1) = x ∧
      C (data.toRotationSystem.edgeOf pair.2.1) = x := by
  rcases List.mem_map.mp hpair with ⟨edge, _hedge, rfl⟩
  have hcolor :=
    (mem_internalDyadEdges_iff C coordinates x edge.1).1 edge.2 |>.1
  constructor
  · rw [edgeOf_internalDyadEdgePair_fst htwoSided C coordinates x edge]
    exact hcolor
  · rw [edgeOf_internalDyadEdgePair_snd htwoSided C coordinates x edge]
    exact hcolor

/-- The concrete pair list fixes a selected dart whose edge is not `x`. -/
theorem internalDyadPairList_glue_apply_of_ne
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color)
    (dart : SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x))
    (hedge : C (data.toRotationSystem.edgeOf dart.1) ≠ x) :
    leftSwapFold (internalDyadPairList htwoSided C coordinates x) 1 dart =
      dart := by
  apply leftSwapFold_one_apply_of_avoids
  intro pair hpair
  have hcolors := internalDyadPairList_endpoint_color
    data htwoSided C coordinates x pair hpair
  constructor
  · intro heq
    exact hedge (by simpa [heq] using hcolors.1)
  · intro heq
    exact hedge (by simpa [heq] using hcolors.2)

/-- The concrete pair list flips a selected dart whose edge is `x` to its
opposite dart-side. -/
theorem internalDyadPairList_glue_apply_of_eq
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color)
    (dart : SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x))
    (hedge : C (data.toRotationSystem.edgeOf dart.1) = x) :
    (leftSwapFold (internalDyadPairList htwoSided C coordinates x) 1 dart).1 =
      data.toRotationSystem.alpha dart.1 := by
  let edge : {edge : G.edgeSet //
      edge ∈ internalDyadEdges C coordinates x} :=
    ⟨data.toRotationSystem.edgeOf dart.1,
      edgeOf_mem_internalDyadEdges_of_selected_eq
        data htwoSided C coordinates x dart hedge⟩
  let pair := internalDyadEdgePair htwoSided C coordinates x edge
  have hpair : pair ∈ internalDyadPairList htwoSided C coordinates x := by
    simp [pair, internalDyadPairList]
  have hswap := leftSwapFold_one_apply_of_isolated_pair
    (internalDyadPairList htwoSided C coordinates x)
    (internalDyadPairList_nodup htwoSided C coordinates x)
    pair hpair
    (internalDyadPairList_isolated htwoSided C coordinates x pair hpair)
  have hchosenEdge : data.toRotationSystem.edgeOf
      (chosenDart data.toRotationSystem edge.1) =
        data.toRotationSystem.edgeOf dart.1 := by
    exact chosenDart_edgeOf data.toRotationSystem edge.1
  rcases data.toRotationSystem.edge_fiber_two_cases hchosenEdge rfl with
      hdart | hdart
  · have hdartPair : dart = pair.1 := by
      apply Subtype.ext
      exact hdart
    rw [hdartPair, hswap.1]
    rfl
  · have hdartPair : dart = pair.2 := by
      apply Subtype.ext
      exact hdart
    rw [hdartPair, hswap.2]
    change chosenDart data.toRotationSystem edge.1 =
      data.toRotationSystem.alpha
        (data.toRotationSystem.alpha
          (chosenDart data.toRotationSystem edge.1))
    rw [data.toRotationSystem.alpha_involutive]

/-- The list presentation of the dyad gluing is extensionally the literal
conditional gluing involution. -/
theorem leftSwapFold_internalDyadPairList_eq_dyadGluePerm
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color) :
    leftSwapFold (internalDyadPairList htwoSided C coordinates x) 1 =
      dyadGluePerm data htwoSided C coordinates x := by
  ext dart
  by_cases hedge : C (data.toRotationSystem.edgeOf dart.1) = x
  · rw [internalDyadPairList_glue_apply_of_eq
      data htwoSided C coordinates x dart hedge]
    change data.toRotationSystem.alpha dart.1 =
      (dyadGlueDart data htwoSided C coordinates x dart).1
    exact (dyadGlueDart_apply_of_eq
      data htwoSided C coordinates x dart hedge).symm
  · rw [internalDyadPairList_glue_apply_of_ne
      data htwoSided C coordinates x dart hedge]
    change dart.1 = (dyadGlueDart data htwoSided C coordinates x dart).1
    exact congrArg Subtype.val
      (dyadGlueDart_apply_of_ne data htwoSided C coordinates x dart hedge).symm

/-- Consequently the previously defined list-based ribbon permutation is the
canonical face-successor followed by the literal internal-edge flip. -/
theorem dyadBoundaryPerm_eq_canonicalDyadRibbonPerm
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color) :
    (dyadFaceRibbonSurgery htwoSided C coordinates x).boundaryPerm =
      canonicalDyadRibbonPerm data htwoSided C coordinates x := by
  change leftSwapFold (internalDyadPairList htwoSided C coordinates x)
      (selectedFacePerm data.toRotationSystem (dyadFaces coordinates x)) = _
  rw [leftSwapFold_eq_mul,
    leftSwapFold_internalDyadPairList_eq_dyadGluePerm]
  rfl

/-! ## First return to the literal dyad boundary -/

/-- Mark the selected face darts whose edge lies on the boundary of the
dyad.  For `x = a + b`, these are exactly the `a`/`b` edges. -/
def dyadBoundaryMark
    {data : Data G} (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color) :
    SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x) → Prop :=
  fun dart => C (data.toRotationSystem.edgeOf dart.1) ≠ x

/-- The next boundary corner encountered by the canonical ribbon walk. -/
def dyadBoundaryReturnPerm
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color) :
    Equiv.Perm (DyadBoundaryDart coordinates x) :=
  nextHitPerm (canonicalDyadRibbonPerm data htwoSided C coordinates x)
    (dyadBoundaryMark C coordinates x)

/-- Compressing to boundary darts neither splits nor merges a ribbon orbit. -/
theorem dyadBoundaryReturnPerm_sameCycle_iff
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color)
    (first second : DyadBoundaryDart coordinates x) :
    (dyadBoundaryReturnPerm data htwoSided C coordinates x).SameCycle
        first second ↔
      (canonicalDyadRibbonPerm data htwoSided C coordinates x).SameCycle
        first.1 second.1 := by
  exact nextHitPerm_sameCycle_iff
    (canonicalDyadRibbonPerm data htwoSided C coordinates x)
    (dyadBoundaryMark C coordinates x) first second

/-- The three darts in a cyclic cubic vertex fibre are pairwise distinct. -/
private theorem rho_triple_pairwise_ne
    (RS : RotationSystem V G.edgeSet)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (dart : RS.D) :
    dart ≠ RS.rho dart ∧
      dart ≠ RS.rho (RS.rho dart) ∧
      RS.rho dart ≠ RS.rho (RS.rho dart) := by
  have hdart : dart ∈ RS.dartsAt (RS.vertOf dart) := by
    simp [RotationSystem.dartsAt]
  have hnontrivialFinset : (RS.dartsAt (RS.vertOf dart)).Nontrivial := by
    apply Finset.one_lt_card_iff_nontrivial.mp
    rw [hcubic (RS.vertOf dart)]
    omega
  have hnontrivial :
      (RS.dartsAt (RS.vertOf dart) : Set RS.D).Nontrivial := by
    simpa only [Finset.coe_sort_coe] using hnontrivialFinset
  have hstep : RS.rho dart ≠ dart :=
    (rho_isCycleOn_dartsAt RS hrotation (RS.vertOf dart)).apply_ne
      hnontrivial hdart
  have hnext : RS.rho (RS.rho dart) ≠ RS.rho dart := by
    exact fun heq => hstep (RS.rho.injective heq)
  have hfirstThird : dart ≠ RS.rho (RS.rho dart) := by
    intro heq
    have hcube := rho_cube_apply_of_isCubic RS hcubic hrotation dart
    have hrho := congrArg RS.rho heq
    rw [hcube] at hrho
    exact hstep hrho
  exact ⟨hstep.symm, hfirstThird, hnext.symm⟩

/-- Advancing once around a cyclic cubic graph vertex changes the graph
edge.  This light local lemma avoids importing any adjacent-pair machinery. -/
private theorem edgeOf_rho_ne_edgeOf
    (data : Data G) (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (dart : G.Dart) :
    data.toRotationSystem.edgeOf (data.toRotationSystem.rho dart) ≠
      data.toRotationSystem.edgeOf dart := by
  intro hedge
  have hfst : (data.toRotationSystem.rho dart).fst = dart.fst := by
    simpa only [Data.toRotationSystem_vertOf] using
      data.toRotationSystem.vert_rho dart
  have hedgeValue : (data.toRotationSystem.rho dart).edge = dart.edge := by
    simpa only [Data.toRotationSystem_edgeOf] using congrArg Subtype.val hedge
  have hdart : data.toRotationSystem.rho dart = dart := by
    rcases (SimpleGraph.dart_edge_eq_iff
      (data.toRotationSystem.rho dart) dart).1 hedgeValue with
      hsame | hopposite
    · exact hsame
    · exfalso
      apply dart.snd_ne_fst
      calc
        dart.snd = dart.symm.fst := rfl
        _ = (data.toRotationSystem.rho dart).fst :=
          congrArg (fun value : G.Dart => value.fst) hopposite.symm
        _ = dart.fst := hfst
  exact (rho_triple_pairwise_ne data.toRotationSystem hcubic hrotation dart).1
    hdart.symm

/-- Two steps around a cyclic cubic graph vertex also change the graph
edge. -/
private theorem edgeOf_rho_rho_ne_edgeOf
    (data : Data G) (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (dart : G.Dart) :
    data.toRotationSystem.edgeOf
        (data.toRotationSystem.rho (data.toRotationSystem.rho dart)) ≠
      data.toRotationSystem.edgeOf dart := by
  intro hedge
  have hfst :
      (data.toRotationSystem.rho
        (data.toRotationSystem.rho dart)).fst = dart.fst := by
    have hfirst := data.toRotationSystem.vert_rho dart
    have hsecond := data.toRotationSystem.vert_rho
      (data.toRotationSystem.rho dart)
    simpa only [Data.toRotationSystem_vertOf] using hsecond.trans hfirst
  have hedgeValue :
      (data.toRotationSystem.rho
        (data.toRotationSystem.rho dart)).edge = dart.edge := by
    simpa only [Data.toRotationSystem_edgeOf] using congrArg Subtype.val hedge
  have hdart : data.toRotationSystem.rho
      (data.toRotationSystem.rho dart) = dart := by
    rcases (SimpleGraph.dart_edge_eq_iff
      (data.toRotationSystem.rho (data.toRotationSystem.rho dart)) dart).1
        hedgeValue with hsame | hopposite
    · exact hsame
    · exfalso
      apply dart.snd_ne_fst
      calc
        dart.snd = dart.symm.fst := rfl
        _ = (data.toRotationSystem.rho
              (data.toRotationSystem.rho dart)).fst :=
          congrArg (fun value : G.Dart => value.fst) hopposite.symm
        _ = dart.fst := hfst
  exact (rho_triple_pairwise_ne data.toRotationSystem hcubic hrotation dart).2.1
    hdart.symm

/-- At a boundary dart the ribbon walk returns after one face turn, unless
that turn encounters the internal `x`-edge.  In the latter case it crosses
that edge and returns after the next turn.  This is the local, picture-free
form of the boundary walk. -/
theorem dyadBoundaryReturnPerm_apply_val
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color)
    (root : DyadBoundaryDart coordinates x) :
    ((dyadBoundaryReturnPerm data htwoSided C coordinates x root).1.1) =
      if C (data.toRotationSystem.edgeOf
          (data.toRotationSystem.phi root.1.1)) = x then
        data.toRotationSystem.rho (data.toRotationSystem.phi root.1.1)
      else data.toRotationSystem.phi root.1.1 := by
  let RS := data.toRotationSystem
  let faces := dyadFaces coordinates x
  let ribbon := canonicalDyadRibbonPerm data htwoSided C coordinates x
  let hit := dyadBoundaryMark C coordinates x
  let turn : SelectedFaceDart RS faces :=
    selectedFacePerm RS faces root.1
  have hturnVal : turn.1 = RS.phi root.1.1 := rfl
  by_cases hturnColor : C (RS.edgeOf turn.1) = x
  · have hturnRhoNe : RS.edgeOf (RS.rho turn.1) ≠ RS.edgeOf turn.1 :=
      edgeOf_rho_ne_edgeOf data hcubic hrotation turn.1
    have hturnAt : turn.1.fst ∈ (RS.edgeOf turn.1 : Sym2 V) := by
      simp [RS, Data.toRotationSystem_edgeOf, SimpleGraph.Dart.edge]
    have hrhoFst : (RS.rho turn.1).fst = turn.1.fst := by
      simpa [RS, Data.toRotationSystem_vertOf] using RS.vert_rho turn.1
    have hrhoAt : turn.1.fst ∈ (RS.edgeOf (RS.rho turn.1) : Sym2 V) := by
      rw [← hrhoFst]
      simp [RS, Data.toRotationSystem_edgeOf, SimpleGraph.Dart.edge]
    have hrhoColor : C (RS.edgeOf (RS.rho turn.1)) ≠ x := by
      intro heq
      exact C.valid
        (G.lineGraph_adj_of_edgeSet_common_vertex
          hturnRhoNe hrhoAt hturnAt)
        (heq.trans hturnColor.symm)
    have hribbonOne : (ribbon root.1).1 = RS.alpha turn.1 := by
      rw [show ribbon = canonicalDyadRibbonPerm
        data htwoSided C coordinates x by rfl,
        canonicalDyadRibbonPerm_apply_val]
      exact dyadGlueDart_apply_of_eq data htwoSided C coordinates x
        turn hturnColor
    have hribbonTwo : ((ribbon ^ 2) root.1).1 = RS.rho turn.1 := by
      rw [pow_two, Equiv.Perm.mul_apply]
      rw [show ribbon = canonicalDyadRibbonPerm
        data htwoSided C coordinates x by rfl,
        canonicalDyadRibbonPerm_apply_val]
      let nextTurn : SelectedFaceDart RS faces :=
        selectedFacePerm RS faces (ribbon root.1)
      have hnextTurnVal : nextTurn.1 = RS.rho turn.1 := by
        change RS.phi (ribbon root.1).1 = RS.rho turn.1
        rw [hribbonOne, RotationSystem.phi_apply,
          RS.alpha_involutive]
      have hnextColor : C (RS.edgeOf nextTurn.1) ≠ x := by
        simpa only [hnextTurnVal] using hrhoColor
      calc
        (dyadGlueDart data htwoSided C coordinates x nextTurn).1 =
            nextTurn.1 := congrArg Subtype.val
          (dyadGlueDart_apply_of_ne data htwoSided C coordinates x
            nextTurn hnextColor)
        _ = RS.rho turn.1 := hnextTurnVal
    have htimeLe : firstPositiveHitTime ribbon hit root.1 root.2 ≤ 2 := by
      apply firstPositiveHitTime_le_of_hit ribbon hit root.1 root.2
      · omega
      · change C (RS.edgeOf ((ribbon ^ 2) root.1).1) ≠ x
        simpa only [hribbonTwo] using hrhoColor
    have htimeNeOne : firstPositiveHitTime ribbon hit root.1 root.2 ≠ 1 := by
      intro htime
      have hhit := firstPositiveHitTime_hits ribbon hit root.1 root.2
      change C (RS.edgeOf
        ((ribbon ^ firstPositiveHitTime ribbon hit root.1 root.2)
          root.1).1) ≠ x at hhit
      rw [htime, pow_one, hribbonOne, RS.edge_alpha] at hhit
      exact hhit hturnColor
    have htime : firstPositiveHitTime ribbon hit root.1 root.2 = 2 := by
      have hpos := firstPositiveHitTime_pos ribbon hit root.1 root.2
      omega
    simp only [hturnVal] at hturnColor ⊢
    rw [if_pos hturnColor]
    change ((ribbon ^ firstPositiveHitTime ribbon hit root.1 root.2)
      root.1).1 = RS.rho turn.1
    rw [htime]
    exact hribbonTwo
  · have hribbonOne : (ribbon root.1).1 = turn.1 := by
      rw [show ribbon = canonicalDyadRibbonPerm
        data htwoSided C coordinates x by rfl,
        canonicalDyadRibbonPerm_apply_val]
      exact congrArg Subtype.val
        (dyadGlueDart_apply_of_ne data htwoSided C coordinates x
          turn hturnColor)
    have htimeLe : firstPositiveHitTime ribbon hit root.1 root.2 ≤ 1 := by
      apply firstPositiveHitTime_le_of_hit ribbon hit root.1 root.2
      · omega
      · change C (RS.edgeOf ((ribbon ^ 1) root.1).1) ≠ x
        rw [pow_one, hribbonOne]
        exact hturnColor
    have htime : firstPositiveHitTime ribbon hit root.1 root.2 = 1 := by
      have hpos := firstPositiveHitTime_pos ribbon hit root.1 root.2
      omega
    simp only [hturnVal] at hturnColor ⊢
    rw [if_neg hturnColor]
    change ((ribbon ^ firstPositiveHitTime ribbon hit root.1 root.2)
      root.1).1 = turn.1
    rw [htime, pow_one]
    exact hribbonOne

/-- The returned boundary dart is based at the head of the original dart.
Thus repeated returns traverse a boundary component coherently rather than
choosing unrelated incident edges. -/
theorem dyadBoundaryReturnPerm_apply_fst
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color)
    (root : DyadBoundaryDart coordinates x) :
    ((dyadBoundaryReturnPerm data htwoSided C coordinates x root).1.1).fst =
      root.1.1.snd := by
  let RS := data.toRotationSystem
  have hphi : (RS.phi root.1.1).fst = root.1.1.snd := by
    change RS.vertOf (RS.phi root.1.1) = root.1.1.snd
    rw [RS.vert_phi_eq_vert_alpha]
    rfl
  rw [dyadBoundaryReturnPerm_apply_val data htwoSided hcubic hrotation]
  split
  · change RS.vertOf (RS.rho (RS.phi root.1.1)) = root.1.1.snd
    rw [RS.vert_rho]
    exact hphi
  · exact hphi

/-- One compressed ribbon step follows one of the two ordinary neighbours of
the corresponding complementary-colour edge. -/
theorem lineGraph_adj_dyadBoundaryReturnPerm
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (coordinates : ColorFacePotential data C)
    {a b : Color} (hab : ValidColorPair a b)
    (root : DyadBoundaryDart coordinates (a + b)) :
    G.lineGraph.Adj
      (data.toRotationSystem.edgeOf root.1.1)
      (data.toRotationSystem.edgeOf
        ((dyadBoundaryReturnPerm data htwoSided C coordinates (a + b)
          root).1.1)) := by
  let RS := data.toRotationSystem
  let first := RS.alpha root.1.1
  let turn := RS.rho first
  have hfirstEdge : RS.edgeOf first = RS.edgeOf root.1.1 :=
    RS.edge_alpha root.1.1
  have hfirstAt : first.fst ∈ (RS.edgeOf first : Sym2 V) := by
    simp [RS, Data.toRotationSystem_edgeOf, SimpleGraph.Dart.edge]
  have hturnFst : turn.fst = first.fst := by
    simpa [turn, RS, Data.toRotationSystem_vertOf] using RS.vert_rho first
  have hturnAt : first.fst ∈ (RS.edgeOf turn : Sym2 V) := by
    rw [← hturnFst]
    simp [turn, RS, Data.toRotationSystem_edgeOf, SimpleGraph.Dart.edge]
  have hrhoTurnFst : (RS.rho turn).fst = first.fst := by
    have hstep := RS.vert_rho turn
    simpa [RS, Data.toRotationSystem_vertOf] using hstep.trans hturnFst
  have hrhoTurnAt : first.fst ∈ (RS.edgeOf (RS.rho turn) : Sym2 V) := by
    rw [← hrhoTurnFst]
    simp [RS, Data.toRotationSystem_edgeOf, SimpleGraph.Dart.edge]
  rw [dyadBoundaryReturnPerm_apply_val data htwoSided hcubic hrotation]
  change G.lineGraph.Adj (RS.edgeOf root.1.1)
    (RS.edgeOf (if C (RS.edgeOf turn) = a + b then RS.rho turn else turn))
  split
  · apply G.lineGraph_adj_of_edgeSet_common_vertex
    · rw [← hfirstEdge]
      simpa [RS, turn] using
        (edgeOf_rho_rho_ne_edgeOf data hcubic hrotation first).symm
    · rw [← hfirstEdge]
      exact hfirstAt
    · exact hrhoTurnAt
  · apply G.lineGraph_adj_of_edgeSet_common_vertex
    · rw [← hfirstEdge]
      simpa [RS, turn] using
        (edgeOf_rho_ne_edgeOf data hcubic hrotation first).symm
    · rw [← hfirstEdge]
      exact hfirstAt
    · exact hturnAt

/-- Transport the boundary successor to the literal vertex carrier of the
ordinary two-colour line subgraph. -/
def bicoloredBoundaryPerm
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (coordinates : ColorFacePotential data C)
    {a b : Color} (hab : ValidColorPair a b) :
    Equiv.Perm {edge : G.edgeSet // edge ∈ C.bicoloredSet a b} :=
  (dyadBoundaryDartEquivBicoloredEdge data htwoSided C hC coordinates hab).permCongr
    (dyadBoundaryReturnPerm data htwoSided C coordinates (a + b))

/-- Every transported successor step is an edge of the ordinary bicoloured
subgraph. -/
theorem bicoloredSubgraph_adj_bicoloredBoundaryPerm
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (coordinates : ColorFacePotential data C)
    {a b : Color} (hab : ValidColorPair a b)
    (edge : {edge : G.edgeSet // edge ∈ C.bicoloredSet a b}) :
    (C.bicoloredSubgraph a b).Adj edge
      (bicoloredBoundaryPerm data htwoSided C hC coordinates hab edge) := by
  let equiv := dyadBoundaryDartEquivBicoloredEdge
    data htwoSided C hC coordinates hab
  let root := equiv.symm edge
  have hadj := lineGraph_adj_dyadBoundaryReturnPerm
    data htwoSided hcubic hrotation C hC coordinates hab root
  have hedge : equiv root = edge := equiv.apply_symm_apply edge
  have hnext :
      bicoloredBoundaryPerm data htwoSided C hC coordinates hab edge =
        equiv (dyadBoundaryReturnPerm data htwoSided C coordinates (a + b)
          root) := by
    simp [bicoloredBoundaryPerm, equiv, root]
  change G.lineGraph.Adj edge.1
    (bicoloredBoundaryPerm data htwoSided C hC coordinates hab edge).1
  rw [hnext, ← hedge]
  exact hadj

/-- The selected boundary orientation attached to a bicoloured edge. -/
def orientedBicoloredBoundaryDart
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (coordinates : ColorFacePotential data C)
    {a b : Color} (hab : ValidColorPair a b)
    (edge : {edge : G.edgeSet // edge ∈ C.bicoloredSet a b}) :
    DyadBoundaryDart coordinates (a + b) :=
  (dyadBoundaryDartEquivBicoloredEdge
    data htwoSided C hC coordinates hab).symm edge

@[simp]
theorem edgeOf_orientedBicoloredBoundaryDart
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (coordinates : ColorFacePotential data C)
    {a b : Color} (hab : ValidColorPair a b)
    (edge : {edge : G.edgeSet // edge ∈ C.bicoloredSet a b}) :
    data.toRotationSystem.edgeOf
        (orientedBicoloredBoundaryDart
          data htwoSided C hC coordinates hab edge).1.1 = edge.1 := by
  let equiv := dyadBoundaryDartEquivBicoloredEdge
    data htwoSided C hC coordinates hab
  have happly : equiv (equiv.symm edge) = edge := equiv.apply_symm_apply edge
  exact congrArg Subtype.val happly

/-- Conjugation says that orienting the next edge is the same operation as
taking the next boundary dart. -/
theorem orientedBicoloredBoundaryDart_perm
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (coordinates : ColorFacePotential data C)
    {a b : Color} (hab : ValidColorPair a b)
    (edge : {edge : G.edgeSet // edge ∈ C.bicoloredSet a b}) :
    orientedBicoloredBoundaryDart data htwoSided C hC coordinates hab
        (bicoloredBoundaryPerm data htwoSided C hC coordinates hab edge) =
      dyadBoundaryReturnPerm data htwoSided C coordinates (a + b)
        (orientedBicoloredBoundaryDart
          data htwoSided C hC coordinates hab edge) := by
  simp [orientedBicoloredBoundaryDart, bicoloredBoundaryPerm]

/-- The boundary orientation advances coherently across a transported
successor step. -/
theorem orientedBicoloredBoundaryDart_perm_fst
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (coordinates : ColorFacePotential data C)
    {a b : Color} (hab : ValidColorPair a b)
    (edge : {edge : G.edgeSet // edge ∈ C.bicoloredSet a b}) :
    (orientedBicoloredBoundaryDart data htwoSided C hC coordinates hab
      (bicoloredBoundaryPerm data htwoSided C hC coordinates hab edge)).1.1.fst =
        (orientedBicoloredBoundaryDart
          data htwoSided C hC coordinates hab edge).1.1.snd := by
  rw [orientedBicoloredBoundaryDart_perm]
  exact dyadBoundaryReturnPerm_apply_fst data htwoSided hcubic hrotation
    C coordinates (a + b)
      (orientedBicoloredBoundaryDart
        data htwoSided C hC coordinates hab edge)

/-- The transported successor cannot be a two-cycle.  Coherent dart
orientation would otherwise make two distinct simple edges have both
endpoints in common. -/
theorem bicoloredBoundaryPerm_sq_ne
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (coordinates : ColorFacePotential data C)
    {a b : Color} (hab : ValidColorPair a b)
    (edge : {edge : G.edgeSet // edge ∈ C.bicoloredSet a b}) :
    bicoloredBoundaryPerm data htwoSided C hC coordinates hab
        (bicoloredBoundaryPerm data htwoSided C hC coordinates hab edge) ≠
      edge := by
  let perm := bicoloredBoundaryPerm data htwoSided C hC coordinates hab
  let orient := orientedBicoloredBoundaryDart
    data htwoSided C hC coordinates hab
  intro hsquare
  have hstep := bicoloredSubgraph_adj_bicoloredBoundaryPerm
    data htwoSided hcubic hrotation C hC coordinates hab edge
  have hfirst := orientedBicoloredBoundaryDart_perm_fst
    data htwoSided hcubic hrotation C hC coordinates hab edge
  have hsecond := orientedBicoloredBoundaryDart_perm_fst
    data htwoSided hcubic hrotation C hC coordinates hab (perm edge)
  change (orient (perm edge)).1.1.fst = (orient edge).1.1.snd at hfirst
  change (orient (perm (perm edge))).1.1.fst =
    (orient (perm edge)).1.1.snd at hsecond
  rw [hsquare] at hsecond
  have hdart : (orient (perm edge)).1.1 = (orient edge).1.1.symm := by
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · exact hfirst
    · exact hsecond.symm
  have hedgeEq : perm edge = edge := by
    apply Subtype.ext
    rw [← edgeOf_orientedBicoloredBoundaryDart
      data htwoSided C hC coordinates hab (perm edge),
      ← edgeOf_orientedBicoloredBoundaryDart
        data htwoSided C hC coordinates hab edge,
      hdart]
    exact data.toRotationSystem.edge_alpha (orient edge).1.1
  exact hstep.ne hedgeEq.symm

/-- In a proper two-colour induced subgraph, two neighbours of the same
vertex carry the same colour. -/
private theorem bicolored_neighbor_colors_eq
    {W Alpha : Type*} {H : SimpleGraph W}
    (coloring : H.Coloring Alpha) (a b : Alpha)
    {center first second : coloring.bicoloredSet a b}
    (hfirst : (coloring.bicoloredSubgraph a b).Adj center first)
    (hsecond : (coloring.bicoloredSubgraph a b).Adj center second) :
    coloring first.1 = coloring second.1 := by
  have hcenterFirst : coloring center.1 ≠ coloring first.1 :=
    coloring.valid hfirst
  have hcenterSecond : coloring center.1 ≠ coloring second.1 :=
    coloring.valid hsecond
  rcases center.property with hcenter | hcenter <;>
    rcases first.property with hfirstColor | hfirstColor <;>
      rcases second.property with hsecondColor | hsecondColor
  all_goals
    first
    | exact hfirstColor.trans hsecondColor.symm
    | exact False.elim
        (hcenterFirst (hcenter.trans hfirstColor.symm))
    | exact False.elim
        (hcenterSecond (hcenter.trans hsecondColor.symm))

/-- Every bicoloured subgraph of a proper edge colouring has maximum degree
two.  This is the small generic line-graph fact needed by the orbit/component
comparison; it uses no planarity. -/
private theorem bicoloredSubgraph_neighborSet_ncard_le_two
    (C : G.EdgeColoring Color) (a b : Color)
    (edge : C.bicoloredSet a b) :
    ((C.bicoloredSubgraph a b).neighborSet edge).ncard ≤ 2 := by
  classical
  let neighbors := (C.bicoloredSubgraph a b).neighborSet edge
  by_contra hdegree
  have hthree : 2 < neighbors.ncard := Nat.lt_of_not_ge hdegree
  have hthreeFinset : 2 < neighbors.toFinset.card := by
    rw [Set.ncard_eq_toFinset_card'] at hthree
    exact hthree
  rcases Finset.two_lt_card_iff.mp hthreeFinset with
    ⟨first, second, third, hfirst, hsecond, hthird,
      hfirstSecond, hfirstThird, hsecondThird⟩
  have hedgeFirst : G.lineGraph.Adj edge.1 first.1 := by
    simpa [neighbors] using hfirst
  have hedgeSecond : G.lineGraph.Adj edge.1 second.1 := by
    simpa [neighbors] using hsecond
  have hedgeThird : G.lineGraph.Adj edge.1 third.1 := by
    simpa [neighbors] using hthird
  rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hedgeFirst with
    ⟨_hedgeFirstNe, firstCommon, hfirstCommonEdge, hfirstCommonFirst⟩
  rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hedgeSecond with
    ⟨_hedgeSecondNe, secondCommon, hsecondCommonEdge, hsecondCommonSecond⟩
  rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hedgeThird with
    ⟨_hedgeThirdNe, thirdCommon, hthirdCommonEdge, hthirdCommonThird⟩
  have hcommonNotPairwise :
      ¬ (firstCommon ≠ secondCommon ∧
        firstCommon ≠ thirdCommon ∧
        secondCommon ≠ thirdCommon) := by
    intro hpairwise
    have htooMany : 2 < edge.1.1.toFinset.card :=
      Finset.two_lt_card_iff.mpr
        ⟨firstCommon, secondCommon, thirdCommon,
          by simpa using hfirstCommonEdge,
          by simpa using hsecondCommonEdge,
          by simpa using hthirdCommonEdge,
          hpairwise.1, hpairwise.2.1, hpairwise.2.2⟩
    have hcard : edge.1.1.toFinset.card = 2 :=
      Sym2.card_toFinset_of_not_isDiag edge.1.1
        (G.not_isDiag_of_mem_edgeSet edge.1.2)
    omega
  have hfirstNeighbor :
      (C.bicoloredSubgraph a b).Adj edge first := by
    simpa [neighbors] using hfirst
  have hsecondNeighbor :
      (C.bicoloredSubgraph a b).Adj edge second := by
    simpa [neighbors] using hsecond
  have hthirdNeighbor :
      (C.bicoloredSubgraph a b).Adj edge third := by
    simpa [neighbors] using hthird
  by_cases hfirstSecondCommon : firstCommon = secondCommon
  · have hfirstSecondVal : first.1 ≠ second.1 := by
      intro heq
      exact hfirstSecond (Subtype.ext heq)
    have hfirstSecondAdj : G.lineGraph.Adj first.1 second.1 :=
      (SimpleGraph.lineGraph_adj_iff_exists).2
        ⟨hfirstSecondVal, firstCommon, hfirstCommonFirst, by
          simpa [hfirstSecondCommon] using hsecondCommonSecond⟩
    exact C.valid hfirstSecondAdj
      (bicolored_neighbor_colors_eq C a b
        hfirstNeighbor hsecondNeighbor)
  · by_cases hfirstThirdCommon : firstCommon = thirdCommon
    · have hfirstThirdVal : first.1 ≠ third.1 := by
        intro heq
        exact hfirstThird (Subtype.ext heq)
      have hfirstThirdAdj : G.lineGraph.Adj first.1 third.1 :=
        (SimpleGraph.lineGraph_adj_iff_exists).2
          ⟨hfirstThirdVal, firstCommon, hfirstCommonFirst, by
            simpa [hfirstThirdCommon] using hthirdCommonThird⟩
      exact C.valid hfirstThirdAdj
        (bicolored_neighbor_colors_eq C a b
          hfirstNeighbor hthirdNeighbor)
    · have hsecondThirdCommon : secondCommon = thirdCommon := by
        by_contra hne
        exact hcommonNotPairwise
          ⟨hfirstSecondCommon, hfirstThirdCommon, hne⟩
      have hsecondThirdVal : second.1 ≠ third.1 := by
        intro heq
        exact hsecondThird (Subtype.ext heq)
      have hsecondThirdAdj : G.lineGraph.Adj second.1 third.1 :=
        (SimpleGraph.lineGraph_adj_iff_exists).2
          ⟨hsecondThirdVal, secondCommon, hsecondCommonSecond, by
            simpa [hsecondThirdCommon] using hthirdCommonThird⟩
      exact C.valid hsecondThirdAdj
        (bicolored_neighbor_colors_eq C a b
          hsecondNeighbor hthirdNeighbor)

/-- The two-colour edge-line subgraph is a disjoint union of cycles, with the
boundary successor furnishing its cyclic orientation. -/
theorem bicoloredSubgraph_isCycles
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (coordinates : ColorFacePotential data C)
    {a b : Color} (hab : ValidColorPair a b) :
    (C.bicoloredSubgraph a b).IsCycles := by
  apply isCycles_of_perm_adj_of_sq_ne_of_degree_le_two
    (C.bicoloredSubgraph a b)
    (bicoloredBoundaryPerm data htwoSided C hC coordinates hab)
  · exact bicoloredSubgraph_adj_bicoloredBoundaryPerm
      data htwoSided hcubic hrotation C hC coordinates hab
  · exact bicoloredBoundaryPerm_sq_ne
      data htwoSided hcubic hrotation C hC coordinates hab
  · exact bicoloredSubgraph_neighborSet_ncard_le_two C a b

/-- The cycles of the transported ribbon successor are exactly the Kempe
components of the ordinary two-colour subgraph. -/
theorem bicoloredBoundaryPerm_sameCycle_iff_reachable
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (coordinates : ColorFacePotential data C)
    {a b : Color} (hab : ValidColorPair a b)
    (first second : {edge : G.edgeSet // edge ∈ C.bicoloredSet a b}) :
    (bicoloredBoundaryPerm data htwoSided C hC coordinates hab).SameCycle
        first second ↔
      (C.bicoloredSubgraph a b).Reachable first second := by
  exact sameCycle_iff_reachable_of_isCycles_of_adj_of_sq_ne
    (C.bicoloredSubgraph a b)
    (bicoloredBoundaryPerm data htwoSided C hC coordinates hab)
    (bicoloredSubgraph_isCycles data htwoSided hcubic hrotation
      C hC coordinates hab)
    (bicoloredSubgraph_adj_bicoloredBoundaryPerm
      data htwoSided hcubic hrotation C hC coordinates hab)
    (bicoloredBoundaryPerm_sq_ne
      data htwoSided hcubic hrotation C hC coordinates hab)
    first second

/-! ## Equality of ribbon orbits and Kempe components -/

/-- Every ribbon orbit meets the literal dyad boundary.  Starting at an
arbitrary selected corner, either the next face turn is already a boundary
edge, or it is the internal `x`-edge and the following turn is a boundary
edge by properness at the cubic vertex. -/
theorem exists_dyadBoundaryDart_sameCycle
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color)
    (dart : SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x)) :
    ∃ boundary : DyadBoundaryDart coordinates x,
      (canonicalDyadRibbonPerm data htwoSided C coordinates x).SameCycle
        dart boundary.1 := by
  let RS := data.toRotationSystem
  let faces := dyadFaces coordinates x
  let ribbon := canonicalDyadRibbonPerm data htwoSided C coordinates x
  let turn : SelectedFaceDart RS faces := selectedFacePerm RS faces dart
  by_cases hturnColor : C (RS.edgeOf turn.1) = x
  · have hturnRhoNe : RS.edgeOf (RS.rho turn.1) ≠ RS.edgeOf turn.1 :=
      edgeOf_rho_ne_edgeOf data hcubic hrotation turn.1
    have hturnAt : turn.1.fst ∈ (RS.edgeOf turn.1 : Sym2 V) := by
      simp [RS, Data.toRotationSystem_edgeOf, SimpleGraph.Dart.edge]
    have hrhoFst : (RS.rho turn.1).fst = turn.1.fst := by
      simpa [RS, Data.toRotationSystem_vertOf] using RS.vert_rho turn.1
    have hrhoAt : turn.1.fst ∈ (RS.edgeOf (RS.rho turn.1) : Sym2 V) := by
      rw [← hrhoFst]
      simp [RS, Data.toRotationSystem_edgeOf, SimpleGraph.Dart.edge]
    have hrhoColor : C (RS.edgeOf (RS.rho turn.1)) ≠ x := by
      intro heq
      exact C.valid
        (G.lineGraph_adj_of_edgeSet_common_vertex
          hturnRhoNe hrhoAt hturnAt)
        (heq.trans hturnColor.symm)
    have hribbonOne : (ribbon dart).1 = RS.alpha turn.1 := by
      rw [show ribbon = canonicalDyadRibbonPerm
        data htwoSided C coordinates x by rfl,
        canonicalDyadRibbonPerm_apply_val]
      exact dyadGlueDart_apply_of_eq data htwoSided C coordinates x
        turn hturnColor
    have hribbonTwo : ((ribbon ^ 2) dart).1 = RS.rho turn.1 := by
      rw [pow_two, Equiv.Perm.mul_apply]
      rw [show ribbon = canonicalDyadRibbonPerm
        data htwoSided C coordinates x by rfl,
        canonicalDyadRibbonPerm_apply_val]
      let nextTurn : SelectedFaceDart RS faces :=
        selectedFacePerm RS faces (ribbon dart)
      have hnextTurnVal : nextTurn.1 = RS.rho turn.1 := by
        change RS.phi (ribbon dart).1 = RS.rho turn.1
        rw [hribbonOne, RotationSystem.phi_apply, RS.alpha_involutive]
      have hnextColor : C (RS.edgeOf nextTurn.1) ≠ x := by
        simpa only [hnextTurnVal] using hrhoColor
      calc
        (dyadGlueDart data htwoSided C coordinates x nextTurn).1 =
            nextTurn.1 := congrArg Subtype.val
          (dyadGlueDart_apply_of_ne data htwoSided C coordinates x
            nextTurn hnextColor)
        _ = RS.rho turn.1 := hnextTurnVal
    let boundary : DyadBoundaryDart coordinates x :=
      ⟨(ribbon ^ 2) dart, by
        change C (RS.edgeOf ((ribbon ^ 2) dart).1) ≠ x
        simpa only [hribbonTwo] using hrhoColor⟩
    refine ⟨boundary, ?_⟩
    exact (Equiv.Perm.sameCycle_pow_right).2
      (Equiv.Perm.SameCycle.refl ribbon dart)
  · have hribbonOne : (ribbon dart).1 = turn.1 := by
      rw [show ribbon = canonicalDyadRibbonPerm
        data htwoSided C coordinates x by rfl,
        canonicalDyadRibbonPerm_apply_val]
      exact congrArg Subtype.val
        (dyadGlueDart_apply_of_ne data htwoSided C coordinates x
          turn hturnColor)
    let boundary : DyadBoundaryDart coordinates x :=
      ⟨ribbon dart, by
        change C (RS.edgeOf (ribbon dart).1) ≠ x
        simpa only [hribbonOne] using hturnColor⟩
    refine ⟨boundary, ?_⟩
    exact (Equiv.Perm.sameCycle_apply_right).2
      (Equiv.Perm.SameCycle.refl ribbon dart)

/-- Send a first-return orbit to its ambient ribbon orbit. -/
def dyadBoundaryOrbitToRibbonOrbit
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color) :
    Quotient (Equiv.Perm.SameCycle.setoid
      (dyadBoundaryReturnPerm data htwoSided C coordinates x)) →
      Quotient (Equiv.Perm.SameCycle.setoid
        (canonicalDyadRibbonPerm data htwoSided C coordinates x)) :=
  Quotient.lift (fun boundary => Quotient.mk _ boundary.1) (by
    intro first second hsame
    apply Quotient.sound
    exact (dyadBoundaryReturnPerm_sameCycle_iff
      data htwoSided C coordinates x first second).1 hsame)

theorem dyadBoundaryOrbitToRibbonOrbit_injective
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color) :
    Function.Injective
      (dyadBoundaryOrbitToRibbonOrbit data htwoSided C coordinates x) := by
  intro left right heq
  induction left, right using Quotient.inductionOn₂ with
  | _ left right =>
      apply Quotient.sound
      apply (dyadBoundaryReturnPerm_sameCycle_iff
        data htwoSided C coordinates x left right).2
      exact Quotient.exact heq

theorem dyadBoundaryOrbitToRibbonOrbit_surjective
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color) :
    Function.Surjective
      (dyadBoundaryOrbitToRibbonOrbit data htwoSided C coordinates x) := by
  intro orbit
  induction orbit using Quotient.inductionOn with
  | _ dart =>
      rcases exists_dyadBoundaryDart_sameCycle
        data htwoSided hcubic hrotation C coordinates x dart with
        ⟨boundary, hsame⟩
      refine ⟨Quotient.mk _ boundary, ?_⟩
      exact Quotient.sound hsame.symm

/-- Boundary first-return cycles and full ribbon cycles are canonically
equivalent; there are no closed selected components hidden from the boundary. -/
def dyadBoundaryOrbitEquivRibbonOrbit
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color) :
    Quotient (Equiv.Perm.SameCycle.setoid
      (dyadBoundaryReturnPerm data htwoSided C coordinates x)) ≃
      Quotient (Equiv.Perm.SameCycle.setoid
        (canonicalDyadRibbonPerm data htwoSided C coordinates x)) :=
  Equiv.ofBijective
    (dyadBoundaryOrbitToRibbonOrbit data htwoSided C coordinates x)
    ⟨dyadBoundaryOrbitToRibbonOrbit_injective
        data htwoSided C coordinates x,
      dyadBoundaryOrbitToRibbonOrbit_surjective
        data htwoSided hcubic hrotation C coordinates x⟩

theorem orbitCount_dyadBoundaryReturnPerm_eq_ribbon
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color) :
    orbitCount (dyadBoundaryReturnPerm data htwoSided C coordinates x) =
      orbitCount (canonicalDyadRibbonPerm data htwoSided C coordinates x) := by
  unfold orbitCount
  exact Fintype.card_congr
    (dyadBoundaryOrbitEquivRibbonOrbit
      data htwoSided hcubic hrotation C coordinates x)

/-- Transporting the first-return permutation from boundary darts to
bicoloured edges preserves its orbit count. -/
theorem orbitCount_bicoloredBoundaryPerm_eq_return
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (coordinates : ColorFacePotential data C)
    {a b : Color} (hab : ValidColorPair a b) :
    orbitCount (bicoloredBoundaryPerm
        data htwoSided C hC coordinates hab) =
      orbitCount (dyadBoundaryReturnPerm
        data htwoSided C coordinates (a + b)) := by
  unfold orbitCount
  exact (Fintype.card_congr
    (Quotient.congr
      (dyadBoundaryDartEquivBicoloredEdge
        data htwoSided C hC coordinates hab)
      (fun first second =>
        (permCongr_sameCycle_iff
          (dyadBoundaryDartEquivBicoloredEdge
            data htwoSided C hC coordinates hab)
          (dyadBoundaryReturnPerm data htwoSided C coordinates (a + b))
          first second).symm))).symm

/-- **Exact dyad boundary/component correspondence.**  The orbit count of
the concrete face-ribbon surgery is the number of complementary two-colour
Kempe components. -/
theorem orbitCount_dyadBoundaryPerm_eq_bicoloredComponentCount
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (coordinates : ColorFacePotential data C)
    {a b : Color} (hab : ValidColorPair a b) :
    orbitCount (dyadFaceRibbonSurgery
        htwoSided C coordinates (a + b)).boundaryPerm =
      Nat.card ((C.bicoloredSubgraph a b).ConnectedComponent) := by
  rw [dyadBoundaryPerm_eq_canonicalDyadRibbonPerm,
    ← orbitCount_dyadBoundaryReturnPerm_eq_ribbon
      data htwoSided hcubic hrotation C coordinates (a + b),
    ← orbitCount_bicoloredBoundaryPerm_eq_return
      data htwoSided C hC coordinates hab]
  exact orbitCount_eq_natCard_connectedComponent
    (C.bicoloredSubgraph a b)
    (bicoloredBoundaryPerm data htwoSided C hC coordinates hab)
    (bicoloredBoundaryPerm_sameCycle_iff_reachable
      data htwoSided hcubic hrotation C hC coordinates hab)

/-- Euler parity for one potential dyad, now stated directly with the
ordinary Kempe-component count. -/
theorem bicoloredComponentCount_mod_two_eq_dyad
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (coordinates : ColorFacePotential data C)
    {a b : Color} (hab : ValidColorPair a b) :
    Nat.card ((C.bicoloredSubgraph a b).ConnectedComponent) % 2 =
      ((dyadFaces coordinates (a + b)).card +
        (internalDyadEdges C coordinates (a + b)).card) % 2 := by
  rw [← orbitCount_dyadBoundaryPerm_eq_bicoloredComponentCount
    data htwoSided hcubic hrotation C hC coordinates hab]
  exact orbitCount_dyadBoundaryPerm_mod_two
    htwoSided C coordinates (a + b)

end

end GoertzelV24KauffmanDyadBoundary

end Mettapedia.GraphTheory.FourColor
