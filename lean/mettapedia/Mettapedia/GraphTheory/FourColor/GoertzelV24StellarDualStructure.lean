import Mettapedia.GraphTheory.FourColor.GoertzelV24DualMap
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualRotationSystem
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationBridgeFace
import Mettapedia.GraphTheory.FourColor.GoertzelV24SphericalGraphPresentation
import Mettapedia.GraphTheory.FourColor.GoertzelV24StellarRotationSystem
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

/-!
# The stellar dual is a bridgeless spherical cubic map

This is the structural half of Tait's reduction on the source's actual
carriers.  Starting from a connected spherical presentation of a finite
simple graph, it packages the stellar subdivision, proves that its semantic
vertex carrier agrees with its rotation cycles, and then packages its facial
dual as a bridgeless spherical cubic map.

Parallel stellar spokes are retained.  No simple-graph projection is used in
the dual construction.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24StellarDualStructure

open Equiv
open GoertzelV24DualMap
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24PermutationOrbitSurgery
open GoertzelV24RotationBridgeFace
open GoertzelV24RotationEdgeBridge
open GoertzelV24SphericalGraphPresentation
open GoertzelV24StellarEuler
open GoertzelV24StellarStructure
open GoertzelV24StellarSubdivision
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WordReachability
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u v

variable {V : Type u} {E : Type v}
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ## Generic vertex-orbit and reachability adapters -/

/-- A cyclic stored rotation whose vertex map is onto has one rotation orbit
for each displayed vertex. -/
def rhoOrbitEquivVertex (RS : RotationSystem V E)
    (hrotation : VertexRotationCyclic RS)
    (hsurj : Function.Surjective RS.vertOf) :
    Quotient (Perm.SameCycle.setoid RS.rho) ≃ V where
  toFun := Quotient.lift RS.vertOf
    (fun _ _ h =>
      GoertzelV24StellarRotationSystem.vertOf_eq_of_rho_sameCycle RS h)
  invFun vertex := Quotient.mk _ (Classical.choose (hsurj vertex))
  left_inv component := by
    induction component using Quotient.inductionOn with
    | h dart =>
        apply Quotient.sound
        apply hrotation
        exact Classical.choose_spec (hsurj (RS.vertOf dart))
  right_inv vertex := Classical.choose_spec (hsurj vertex)

theorem orbitCount_rho_eq_card_vertex (RS : RotationSystem V E)
    (hrotation : VertexRotationCyclic RS)
    (hsurj : Function.Surjective RS.vertOf) :
    orbitCount RS.rho = Fintype.card V := by
  unfold orbitCount
  exact Fintype.card_congr (rhoOrbitEquivVertex RS hrotation hsurj)

theorem orbitCount_alpha_eq_card_edge (RS : RotationSystem V E) :
    orbitCount RS.alpha = Fintype.card E := by
  have hdartsEdges := RS.card_darts_eq_twice_card_edges
  have hdartsOrbits :=
    card_eq_two_mul_orbitCount_flip
      RS.alpha_involutive RS.alpha_fixfree
  omega

theorem orbitCount_phi_eq_card_orbitFace (RS : RotationSystem V E) :
    orbitCount RS.phi = Fintype.card (OrbitFace RS) :=
  Fintype.card_congr (Equiv.refl _)

/-- A cyclic rotation step is a word in the two map generators. -/
theorem wordReachable_pair_of_rho_sameCycle
    (RS : RotationSystem V E) {left right : RS.D}
    (hsame : RS.rho.SameCycle left right) :
    WordReachable [RS.rho, RS.alpha] left right := by
  obtain ⟨power, hpower⟩ :=
    GoertzelV24PermutationOrbitSurgery.exists_nat_pow_apply_eq hsame
  have hreach := wordReachable_pow
    (L := [RS.rho, RS.alpha]) (g := RS.rho) (by simp) left power
  rwa [hpower] at hreach

/-- A primal graph walk lifts to reachability by the rotation and flip. -/
theorem wordReachable_pair_of_primalWalk
    (RS : RotationSystem V E) (hrotation : VertexRotationCyclic RS)
    {first last : V} (walk : (rotationPrimalGraph RS).Walk first last) :
    ∀ (left right : RS.D), RS.vertOf left = first →
      RS.vertOf right = last →
        WordReachable [RS.rho, RS.alpha] left right := by
  induction walk with
  | nil =>
      intro left right hleft hright
      exact wordReachable_pair_of_rho_sameCycle RS
        (hrotation left right (hleft.trans hright.symm))
  | @cons first middle last hadj tail ih =>
      intro left right hleft hright
      obtain ⟨crossing, hcrossingFirst, hcrossingMiddle⟩ :=
        (rotationPrimalGraph_adj_iff RS).1 hadj
      have hrotate := wordReachable_pair_of_rho_sameCycle RS
        (hrotation left crossing (hleft.trans hcrossingFirst.symm))
      have hcross : WordReachable [RS.rho, RS.alpha]
          crossing (RS.alpha crossing) :=
        wordReachable_step (g := RS.alpha) (by simp) crossing
      exact hrotate.trans
        (hcross.trans (ih (RS.alpha crossing) right hcrossingMiddle hright))

theorem wordReachable_pair_all_of_primalConnected
    (RS : RotationSystem V E)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (hrotation : VertexRotationCyclic RS) (left right : RS.D) :
    WordReachable [RS.rho, RS.alpha] left right := by
  obtain ⟨walk⟩ := hconnected (RS.vertOf left) (RS.vertOf right)
  exact wordReachable_pair_of_primalWalk RS hrotation walk left right rfl rfl

/-- Conversely, a word in the two generators projects to primal graph
reachability: a rotation step stays put and a flip step crosses one edge. -/
theorem primalReachable_of_wordReachable_pair
    (RS : RotationSystem V E) {left right : RS.D}
    (hreach : WordReachable [RS.rho, RS.alpha] left right) :
    (rotationPrimalGraph RS).Reachable (RS.vertOf left) (RS.vertOf right) := by
  induction hreach with
  | refl => exact SimpleGraph.Reachable.rfl
  | tail _ hstep ih =>
      obtain ⟨generator, hgenerator, rfl⟩ := hstep
      rcases List.mem_cons.1 hgenerator with rfl | hgenerator
      · simpa only [RS.vert_rho] using ih
      · rw [List.mem_singleton] at hgenerator
        subst generator
        exact ih.trans (SimpleGraph.Adj.reachable
          ((rotationPrimalGraph_adj_iff RS).2 ⟨_, rfl, rfl⟩))

theorem primalConnected_of_wordReachable_pair_all
    (RS : RotationSystem V E)
    (hsurj : Function.Surjective RS.vertOf)
    (hall : ∀ left right : RS.D,
      WordReachable [RS.rho, RS.alpha] left right) :
    (rotationPrimalGraph RS).Connected := by
  letI : Nonempty V := ⟨RS.vertOf RS.outer⟩
  constructor
  intro left right
  obtain ⟨leftDart, hleft⟩ := hsurj left
  obtain ⟨rightDart, hright⟩ := hsurj right
  simpa [hleft, hright] using
    (primalReachable_of_wordReachable_pair RS (hall leftDart rightDart))

/-! ## The stellar map -/

variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem graphData_vertOf_surjective
    (presentation : ConnectedSphericalGraphPresentation G)
    (hcard : 3 ≤ Fintype.card V) :
    Function.Surjective presentation.graphData.toRotationSystem.vertOf := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  intro vertex
  have hnotIsolated :=
    presentation.connected.preconnected.not_isIsolated vertex
  obtain ⟨neighbor, hadj⟩ :=
    SimpleGraph.exists_adj_iff_not_isIsolated.mpr hnotIsolated
  exact ⟨(⟨(vertex, neighbor), hadj⟩ : G.Dart), rfl⟩

theorem stellar_vertexRotationCyclic
    (RS : RotationSystem V E) (hrotation : VertexRotationCyclic RS) :
    VertexRotationCyclic (GoertzelV24StellarRotationSystem.rotationSystem RS) := by
  let stellar := GoertzelV24StellarRotationSystem.rotationSystem RS
  intro left right hvertex
  rcases left with (left | left | left) <;>
    rcases right with (right | right | right)
  · apply (stellarRotation_sameCycle_old_iff RS.alpha_involutive _ _).2
    apply hrotation
    exact Sum.inl.inj hvertex
  · have hbase : RS.rho.SameCycle left (RS.alpha right) :=
      hrotation _ _ (Sum.inl.inj hvertex)
    exact ((stellarRotation_sameCycle_old_iff RS.alpha_involutive _ _).2
      hbase).trans
        (stellarRotation_sameCycle_old_apex RS.alpha_involutive right)
  · simp [GoertzelV24StellarRotationSystem.stellarVertOf] at hvertex
  · have hbase : RS.rho.SameCycle (RS.alpha left) right :=
      hrotation _ _ (Sum.inl.inj hvertex)
    exact (stellarRotation_sameCycle_old_apex RS.alpha_involutive left).symm.trans
      ((stellarRotation_sameCycle_old_iff RS.alpha_involutive _ _).2 hbase)
  · have hbase : RS.rho.SameCycle (RS.alpha left) (RS.alpha right) :=
      hrotation _ _ (Sum.inl.inj hvertex)
    exact (stellarRotation_sameCycle_old_apex RS.alpha_involutive left).symm.trans
      (((stellarRotation_sameCycle_old_iff RS.alpha_involutive _ _).2 hbase).trans
        (stellarRotation_sameCycle_old_apex RS.alpha_involutive right))
  · simp [GoertzelV24StellarRotationSystem.stellarVertOf] at hvertex
  · simp [GoertzelV24StellarRotationSystem.stellarVertOf] at hvertex
  · simp [GoertzelV24StellarRotationSystem.stellarVertOf] at hvertex
  · apply (stellarRotation_sameCycle_rim_iff _ _).2
    exact Quotient.exact (Sum.inr.inj hvertex)

theorem stellar_vertOf_surjective
    (RS : RotationSystem V E) (hsurj : Function.Surjective RS.vertOf) :
    Function.Surjective
      (GoertzelV24StellarRotationSystem.rotationSystem RS).vertOf := by
  rintro (vertex | face)
  · obtain ⟨dart, hdart⟩ := hsurj vertex
    exact ⟨old dart, by simp [hdart]⟩
  · obtain ⟨dart, rfl⟩ := Quotient.exists_rep face
    exact ⟨rim dart, rfl⟩

theorem stellar_primalConnected
    (presentation : ConnectedSphericalGraphPresentation G)
    (hcard : 3 ≤ Fintype.card V) :
    (rotationPrimalGraph
      (GoertzelV24StellarRotationSystem.rotationSystem
        presentation.graphData.toRotationSystem)).Connected := by
  let RS := presentation.graphData.toRotationSystem
  have horiginal : ∀ left right : RS.D,
      WordReachable [RS.rho, RS.alpha] left right :=
    wordReachable_pair_all_of_primalConnected RS presentation.primalConnected
      presentation.vertexRotationCyclic
  have hstellar := wordReachable_stellar RS.alpha_involutive horiginal
  exact primalConnected_of_wordReachable_pair_all
    (GoertzelV24StellarRotationSystem.rotationSystem RS)
    (stellar_vertOf_surjective RS
      (graphData_vertOf_surjective presentation hcard)) hstellar

theorem stellar_euler_semantic
    (presentation : ConnectedSphericalGraphPresentation G)
    (hcard : 3 ≤ Fintype.card V) :
    let stellar := GoertzelV24StellarRotationSystem.rotationSystem
      presentation.graphData.toRotationSystem
    (Fintype.card (GoertzelV24StellarRotationSystem.StellarVertex
        presentation.graphData.toRotationSystem) : Int) -
      Fintype.card (GoertzelV24StellarRotationSystem.rewiredDartSystem
        presentation.graphData.toRotationSystem).Edge +
      Fintype.card (OrbitFace stellar) = 2 := by
  let RS := presentation.graphData.toRotationSystem
  let stellar := GoertzelV24StellarRotationSystem.rotationSystem RS
  have hsurj := graphData_vertOf_surjective presentation hcard
  have horiginalRho := orbitCount_rho_eq_card_vertex RS
    presentation.vertexRotationCyclic hsurj
  have horiginalAlpha := orbitCount_alpha_eq_card_edge RS
  have horiginalPhi := orbitCount_phi_eq_card_orbitFace RS
  have hstellarRotation := orbitCount_rho_eq_card_vertex stellar
    (stellar_vertexRotationCyclic RS presentation.vertexRotationCyclic)
    (stellar_vertOf_surjective RS hsurj)
  have hstellarAlpha := orbitCount_alpha_eq_card_edge stellar
  have hstellarPhi := orbitCount_phi_eq_card_orbitFace stellar
  have hraw := stellar_euler
    (σ := RS.rho) (α := RS.alpha)
    RS.alpha_involutive RS.alpha_fixfree
  change orbitCount stellar.rho + orbitCount stellar.phi + orbitCount RS.alpha =
      orbitCount RS.rho + orbitCount RS.phi + orbitCount stellar.alpha at hraw
  change (Fintype.card (GoertzelV24StellarRotationSystem.StellarVertex RS) : Int) -
      Fintype.card (GoertzelV24StellarRotationSystem.rewiredDartSystem RS).Edge +
      Fintype.card (OrbitFace stellar) = 2
  rw [← hstellarRotation, ← hstellarAlpha, ← hstellarPhi]
  have horiginalEuler := presentation.euler
  rw [← horiginalRho, ← horiginalAlpha, ← horiginalPhi] at horiginalEuler
  omega

/-! ## The facial dual -/

abbrev StellarRS (presentation : ConnectedSphericalGraphPresentation G) :=
  GoertzelV24StellarRotationSystem.rotationSystem
    presentation.graphData.toRotationSystem

abbrev StellarDualRS (presentation : ConnectedSphericalGraphPresentation G) :=
  GoertzelV24DualRotationSystem.rotationSystem (StellarRS presentation)
    (GoertzelV24StellarRotationSystem.orbitFacesTwoSided
      presentation.graphData.toRotationSystem)

theorem stellarDual_primalConnected
    (presentation : ConnectedSphericalGraphPresentation G) :
    (rotationPrimalGraph (StellarDualRS presentation)).Connected := by
  let RS := presentation.graphData.toRotationSystem
  let stellar := StellarRS presentation
  let dual := StellarDualRS presentation
  have horiginal : ∀ left right : RS.D,
      WordReachable [RS.rho, RS.alpha] left right :=
    wordReachable_pair_all_of_primalConnected RS presentation.primalConnected
      presentation.vertexRotationCyclic
  have hstellar : ∀ left right : stellar.D,
      WordReachable [stellar.rho, stellar.alpha] left right :=
    wordReachable_stellar RS.alpha_involutive horiginal
  have hdual : ∀ left right : dual.D,
      WordReachable [dual.rho, dual.alpha] left right := by
    intro left right
    exact (wordReachable_dualRotation_iff
      (σ := stellar.rho) (α := stellar.alpha)
      (by ext dart; simp [stellar.alpha_involutive]) left right).2
      (hstellar left right)
  have hsurj : Function.Surjective dual.vertOf := by
    intro face
    obtain ⟨dart, rfl⟩ := Quotient.exists_rep face
    exact ⟨dart, rfl⟩
  exact primalConnected_of_wordReachable_pair_all dual hsurj hdual

theorem stellarDual_edgeBridgeFree
    (presentation : ConnectedSphericalGraphPresentation G) :
    EdgeBridgeFree (StellarDualRS presentation) := by
  let stellar := StellarRS presentation
  let dual := StellarDualRS presentation
  intro dart
  by_contra hbridge
  have hsame := phi_sameCycle_alpha_of_not_edgeDeleted_reachable
    dual dart hbridge
  have hphi : dual.phi = stellar.rho := by
    ext current
    exact GoertzelV24DualRotationSystem.rotationSystem_phi stellar
      (GoertzelV24StellarRotationSystem.orbitFacesTwoSided
        presentation.graphData.toRotationSystem) current
  rw [hphi] at hsame
  exact stellar.no_self_loops dart
    (GoertzelV24StellarRotationSystem.vertOf_eq_of_rho_sameCycle stellar hsame)

theorem stellarDual_orbitSphericalCubicMapData
    (presentation : ConnectedSphericalGraphPresentation G)
    (hcard : 3 ≤ Fintype.card V) :
    OrbitSphericalCubicMapData (StellarDualRS presentation) := by
  let stellar := StellarRS presentation
  let dual := StellarDualRS presentation
  refine ⟨?_, ?_⟩
  · exact GoertzelV24DualRotationSystem.isCubic_of_face_card_three stellar
      (GoertzelV24StellarRotationSystem.orbitFacesTwoSided
        presentation.graphData.toRotationSystem)
      (GoertzelV24StellarRotationSystem.orbitFaceDarts_card_three
        presentation.graphData.toRotationSystem)
  · have hstellarEuler := stellar_euler_semantic presentation hcard
    change
      (Fintype.card (GoertzelV24StellarRotationSystem.StellarVertex
          presentation.graphData.toRotationSystem) : Int) -
        Fintype.card (GoertzelV24StellarRotationSystem.rewiredDartSystem
          presentation.graphData.toRotationSystem).Edge +
        Fintype.card (OrbitFace stellar) = 2 at hstellarEuler
    have hstellarRho := orbitCount_rho_eq_card_vertex stellar
      (stellar_vertexRotationCyclic presentation.graphData.toRotationSystem
        presentation.vertexRotationCyclic)
      (stellar_vertOf_surjective presentation.graphData.toRotationSystem
        (graphData_vertOf_surjective presentation hcard))
    have hdualFaces := orbitCount_phi_eq_card_orbitFace dual
    have hdualPhi : dual.phi = stellar.rho := by
      ext current
      exact GoertzelV24DualRotationSystem.rotationSystem_phi stellar
        (GoertzelV24StellarRotationSystem.orbitFacesTwoSided
          presentation.graphData.toRotationSystem) current
    rw [hdualPhi] at hdualFaces
    have hdualFaceCard :
        Fintype.card (OrbitFace dual) =
          Fintype.card (GoertzelV24StellarRotationSystem.StellarVertex
            presentation.graphData.toRotationSystem) :=
      hdualFaces.symm.trans hstellarRho
    change (Fintype.card (OrbitFace stellar) : Int) -
        Fintype.card (GoertzelV24StellarRotationSystem.rewiredDartSystem
          presentation.graphData.toRotationSystem).Edge +
        Fintype.card (OrbitFace dual) = 2
    rw [hdualFaceCard]
    omega

/-- The structural Tait target produced by stellar subdivision and facial
duality. -/
theorem stellarDual_bridgelessSphericalCubicMapData
    (presentation : ConnectedSphericalGraphPresentation G)
    (hcard : 3 ≤ Fintype.card V) :
    BridgelessSphericalCubicMapData (StellarDualRS presentation) where
  spherical := stellarDual_orbitSphericalCubicMapData presentation hcard
  primalConnected := stellarDual_primalConnected presentation
  vertexRotationCyclic :=
    GoertzelV24DualRotationSystem.vertexRotationCyclic _ _
  edgeBridgeFree := stellarDual_edgeBridgeFree presentation

end

end GoertzelV24StellarDualStructure

end Mettapedia.GraphTheory.FourColor
