import Mettapedia.GraphTheory.FourColor.FaceRegionFaces

/-!
# Curvature and degree codes on complete facial contours

The inner curvature of the extracted patch is the sum on the original
selected faces. Consequently an alternating degree-two/degree-three contour
requires curvature six on that side. For a pentagon/hexagon region this
means exactly six selected pentagons; fewer force consecutive degree-two
vertices in the actual boundary order.

For nested regions the curvature difference is exactly the sum on the
intervening faces. A hexagonal shell therefore preserves boundary degree
imbalance, without a claim that it preserves width or enforces alternation.

The final constructor applies to every deep distance region, deriving the
patch and identifying its full boundary with the original distance frontier.
These are necessary geometric conditions for a regular tube interface, not
a tube supply theorem or a bound on contour width.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceRegionCurvature

open GoertzelV24FaceOrbitIncidence GoertzelV24PrimalCycleFacialBond
open GoertzelV24TwoEdgeCutMinimality SimpleGraphDartRotation
open FaceRegionDegree EdgeShoreRotation PlanePatchCurvature
open FaceRegionPatch FaceRegionFaces FaceRegionConnectivity FaceDistanceFrontiers

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G) (F : Finset (OrbitFace data.toRotationSystem))
variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
variable (outer : Dart data.toRotationSystem (edges data.toRotationSystem F))
variable (ho : dartOrbitFace data.toRotationSystem outer.val ∉ F)
variable (hF : ((orbitFaceDualGraph data).induce (F : Set _)).Connected)
variable (hFc : ((orbitFaceDualGraph data).induce (F : Set _)ᶜ).Connected)

include ambient ho hF hFc

theorem curvature_eq_source :
    curvature (toMap data.toRotationSystem (edges data.toRotationSystem F) outer) =
      ∑ f ∈ F, (6 - ((orbitFaceDarts data.toRotationSystem f).card : ℤ)) :=
  curvature_eq_selected outer (mem_outerDarts_iff data F ambient outer ho hF hFc)

/-- The boundary imbalance is computed on the same faces and vertices as
the source map, with all embedding hypotheses supplied by the source class. -/
theorem boundary_balance :
    (∑ f ∈ F, (6 - ((orbitFaceDarts data.toRotationSystem f).card : ℤ))) =
      6 - (degreeTwo (toMap data.toRotationSystem (edges data.toRotationSystem F) outer)).card +
        (boundaryThree (toMap data.toRotationSystem (edges data.toRotationSystem F) outer)).card := by
  rw [← curvature_eq_source data F ambient outer ho hF hFc]
  exact (patch data F ambient outer ho hF hFc).curvature_eq

/-- Alternation is a restrictive geometric condition, not a consequence
of having a complete simple contour. -/
theorem alternating_requires_six
    (ha : BoundaryAlternates (toMap data.toRotationSystem (edges data.toRotationSystem F) outer)) :
    (∑ f ∈ F, (6 - ((orbitFaceDarts data.toRotationSystem f).card : ℤ))) = 6 := by
  rw [← curvature_eq_source data F ambient outer ho hF hFc]
  exact (patch data F ambient outer ho hF hFc).curvature_eq_six_of_alternates ha

theorem alternating_requires_six_pentagons
    (hfaces : ∀ f ∈ F, (orbitFaceDarts data.toRotationSystem f).card = 5 ∨
      (orbitFaceDarts data.toRotationSystem f).card = 6)
    (ha : BoundaryAlternates (toMap data.toRotationSystem (edges data.toRotationSystem F) outer)) :
    (F.filter fun f => (orbitFaceDarts data.toRotationSystem f).card = 5).card = 6 := by
  have hs : (∑ f ∈ F, (6 - ((orbitFaceDarts data.toRotationSystem f).card : ℤ))) =
      (F.filter fun f => (orbitFaceDarts data.toRotationSystem f).card = 5).card := by
    calc
      _ = ∑ f ∈ F, if (orbitFaceDarts data.toRotationSystem f).card = 5 then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro f hf
        rcases hfaces f hf with h | h <;> simp [h]
      _ = _ := by simp
  have hh := alternating_requires_six data F ambient outer ho hF hFc ha
  rw [hs] at hh
  exact_mod_cast hh

/-- Signed curvature below six forces a pair of consecutive degree-two
vertices on the actual extracted boundary, with no face-size restriction. -/
theorem consecutive_two_of_source_curvature_lt
    (hlt : (∑ f ∈ F, (6 - ((orbitFaceDarts data.toRotationSystem f).card : ℤ))) < 6) :
    let T := toMap data.toRotationSystem (edges data.toRotationSystem F) outer
    ∃ d ∈ outerDarts T, (T.dartsAt (T.vertOf d)).card = 2 ∧
      (T.dartsAt (T.vertOf (T.phi d))).card = 2 := by
  apply (patch data F ambient outer ho hF hFc).consecutive_two_of_curvature_lt
  rwa [curvature_eq_source data F ambient outer ho hF hFc]

section Nested

variable (S : Finset (OrbitFace data.toRotationSystem))
variable (inner : Dart data.toRotationSystem (edges data.toRotationSystem S))
variable (hi : dartOrbitFace data.toRotationSystem inner.val ∉ S)
variable (hS : ((orbitFaceDualGraph data).induce (S : Set _)).Connected)
variable (hSc : ((orbitFaceDualGraph data).induce (S : Set _)ᶜ).Connected)
variable (hSF : S ⊆ F)

include hi hS hSc hSF

/-- Curvature composes across nested complete interfaces by the exact
contribution of the intervening original faces. -/
theorem nested_curvature_difference :
    curvature (toMap data.toRotationSystem (edges data.toRotationSystem F) outer) -
      curvature (toMap data.toRotationSystem (edges data.toRotationSystem S) inner) =
        ∑ f ∈ F \ S, (6 - ((orbitFaceDarts data.toRotationSystem f).card : ℤ)) := by
  rw [curvature_eq_source data F ambient outer ho hF hFc,
    curvature_eq_source data S ambient inner hi hS hSc]
  exact (Finset.sum_sdiff_eq_sub hSF).symm

/-- A shell of hexagonal faces preserves the boundary degree imbalance.
It need not preserve boundary length or make either boundary alternate. -/
theorem hexagonal_shell_preserves_imbalance
    (hhex : ∀ f ∈ F \ S, (orbitFaceDarts data.toRotationSystem f).card = 6) :
    let T := toMap data.toRotationSystem (edges data.toRotationSystem F) outer
    let U := toMap data.toRotationSystem (edges data.toRotationSystem S) inner
    ((degreeTwo T).card : ℤ) - (boundaryThree T).card =
      (degreeTwo U).card - (boundaryThree U).card := by
  have hh := nested_curvature_difference data F ambient outer ho hF hFc S inner hi hS hSc hSF
  have hz : (∑ f ∈ F \ S, (6 - ((orbitFaceDarts data.toRotationSystem f).card : ℤ))) = 0 := by
    apply Finset.sum_eq_zero
    intro f hf
    simp [hhex f hf]
  rw [hz] at hh
  have hbig := (patch data F ambient outer ho hF hFc).curvature_eq
  have hsmall := (patch data S ambient inner hi hS hSc).curvature_eq
  dsimp
  linarith

end Nested

omit ho hF hFc in
/-- Every genuine deep distance component supplies the literal patch,
its complete original frontier, and its exact original face curvature. -/
theorem exists_deep_patch
    (root far : OrbitFace data.toRotationSystem) (depth : ℕ)
    (hdepth : depth < (orbitFaceDualGraph data).dist root far) :
    let F := Finset.univ.filter fun f => f ∈ deepRegion (orbitFaceDualGraph data) root far depth
    ∃ outer : Dart data.toRotationSystem (edges data.toRotationSystem F),
      dartOrbitFace data.toRotationSystem outer.val ∉ F ∧
      Patch (toMap data.toRotationSystem (edges data.toRotationSystem F) outer) ∧
      (∀ v : Vertex data.toRotationSystem (edges data.toRotationSystem F),
        v ∈ boundaryVertices (toMap data.toRotationSystem (edges data.toRotationSystem F) outer) ↔
          v.val ∈ SphericalContourSeparators.frontier data root far depth) ∧
      curvature (toMap data.toRotationSystem (edges data.toRotationSystem F) outer) =
        ∑ f ∈ F, (6 - ((orbitFaceDarts data.toRotationSystem f).card : ℤ)) := by
  let F := Finset.univ.filter fun f => f ∈ deepRegion (orbitFaceDualGraph data) root far depth
  have hcoe : (F : Set _) = deepRegion (orbitFaceDualGraph data) root far depth := by
    ext f
    simp [F]
  have hF : ((orbitFaceDualGraph data).induce (F : Set _)).Connected := by
    rw [hcoe]
    exact deepRegion_connected _ root far depth hdepth
  have hFc : ((orbitFaceDualGraph data).induce (F : Set _)ᶜ).Connected := by
    rw [hcoe]
    exact deepRegion_compl_connected _ root far (orbitFaceDualGraph_connected data ambient) depth
  obtain ⟨outer, ho, _⟩ := deep_region_map data ambient root far depth hdepth
  refine ⟨outer, ho, patch data F ambient outer ho hF hFc, ?_,
    curvature_eq_source data F ambient outer ho hF hFc⟩
  intro v
  rw [boundaryVertices_iff_mixed data F ambient outer ho hF hFc, hcoe]
  rfl

end
end Mettapedia.GraphTheory.FourColor.FaceRegionCurvature
