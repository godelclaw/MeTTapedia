import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedMapEulerBound
import Mettapedia.GraphTheory.FourColor.GoertzelV24CanonicalHubClosure

/-!
# Exact rank forces the canonical hub to be one vertex

`ClosedSideSpherical T ρ` counts the cap as one added vertex.  A priori,
however, the permutation `ρ` on the hub darts could have several cycles and
therefore describe several vertices.  This file shows that this cannot occur
for a connected open shore.

The proof is deliberately combinatorial.  The rotation and flip generators
act transitively on the capped dart carrier: side connectedness moves between
old vertices, cyclic open rotations move within a vertex, and one spoke moves
between every hub dart and its old boundary dart.  Euler's inequality therefore
applies with one component.  Comparing it with the exact one-hub Euler rank
forces `ρ` to have one orbit; two distinct ports then make that orbit a genuine
cycle.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CanonicalHubCyclicity

set_option linter.unusedSectionVars false

open Equiv Equiv.Perm
open GoertzelV24BoundaryEssentialGluing
open GoertzelV24CanonicalHubClosure
open GoertzelV24CompositeSeamCubic
open GoertzelV24CompositeSeamMultigraph
open GoertzelV24CompositeSphericity
open GoertzelV24ConnectedMapEulerBound
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24InvolutionEdgeList
open GoertzelV24MapEulerBound
open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24OrbitCountCongr
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PermutationOrbitSurgery
open GoertzelV24SeamExchange
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24VertexSideOpenTangle
open GoertzelV24WordReachability

noncomputable section

variable {V I B : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]

/-- Rotation on the closed-side carrier: old rotation on real darts and the
chosen hub rotation on hub darts. -/
def hubRho (T : OpenTangleData V I B) (ρ : Perm B) :
    Perm ((I ⊕ B) ⊕ B) :=
  Equiv.sumCongr T.rho ρ

/-- The generators used to read connected components in the capped shore. -/
def hubGenerators (T : OpenTangleData V I B) (ρ : Perm B) :
    List (Perm ((I ⊕ B) ⊕ B)) :=
  hubRho T ρ :: swapGenerators (edgeList (hubAlpha T))

/-- A side-multigraph step can be oriented by an actual interior dart. -/
theorem exists_interiorDart_of_sideStep
    (T : OpenTangleData V I B) {u v : V}
    (hstep : (sideMultigraph T).Step u v) :
    ∃ dart : I,
      T.interiorVert dart = u ∧
        T.interiorVert (T.interiorAlpha dart) = v := by
  rcases hstep with ⟨edge, -, hends⟩
  let dart := edge.2.choose
  rcases hends with hends | hends
  · exact ⟨dart, hends.1, hends.2⟩
  · refine ⟨T.interiorAlpha dart, ?_, ?_⟩
    · exact hends.2
    · simpa [dart, sideMultigraph, T.interiorAlpha_involutive] using hends.1

/-- Rotation inside one old vertex is a word in the capped generators. -/
theorem wordReachable_hub_real_of_sameVertex
    (T : OpenTangleData V I B) (ρ : Perm B)
    (hrotation : OpenRotationCyclic T)
    {left right : I ⊕ B}
    (hvertex : T.vertOf left = T.vertOf right) :
    WordReachable (hubGenerators T ρ) (Sum.inl left) (Sum.inl right) := by
  have hsame : (hubRho T ρ).SameCycle (Sum.inl left) (Sum.inl right) :=
    sameCycle_sumCongr_inl T.rho ρ (hrotation left right hvertex)
  obtain ⟨power, hpower⟩ := exists_nat_pow_apply_eq hsame
  have hreach := wordReachable_pow
    (L := hubGenerators T ρ) (List.mem_cons_self) (Sum.inl left) power
  rwa [hpower] at hreach

/-- Crossing any paired edge of the hub closure is a word in the capped
generators. -/
theorem wordReachable_hubAlpha
    (T : OpenTangleData V I B) (ρ : Perm B)
    (dart : (I ⊕ B) ⊕ B) :
    WordReachable (hubGenerators T ρ) dart (hubAlpha T dart) := by
  have hreach := wordReachable_swapProduct (hubRho T ρ)
    (edgeList (hubAlpha T)) dart
  rwa [swapProduct_edgeList (hubAlpha T) (hubAlphaFun_involutive T)] at hreach

/-- Side connectedness lifts from vertices to all real darts of the capped
carrier. -/
theorem wordReachable_hub_real_of_sideReach
    (T : OpenTangleData V I B) (ρ : Perm B)
    (hrotation : OpenRotationCyclic T)
    {u v : V} (hreach : (sideMultigraph T).Reach u v) :
    ∀ (left right : I ⊕ B), T.vertOf left = u → T.vertOf right = v →
      WordReachable (hubGenerators T ρ) (Sum.inl left) (Sum.inl right) := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro left right hleft hright
      exact wordReachable_hub_real_of_sameVertex T ρ hrotation
        (hleft.trans hright.symm)
  | head hstep htail ih =>
      intro left right hleft hright
      obtain ⟨dart, hdartLeft, hdartRight⟩ :=
        exists_interiorDart_of_sideStep T hstep
      have hdartLeft' : T.vertOf (Sum.inl dart) = _ := hdartLeft
      have hdartRight' : T.vertOf
          (Sum.inl (T.interiorAlpha dart)) = _ := hdartRight
      have hrotateLeft := wordReachable_hub_real_of_sameVertex T ρ hrotation
        (hleft.trans hdartLeft'.symm)
      have hedge := wordReachable_hubAlpha T ρ (Sum.inl (Sum.inl dart))
      have htailReach := ih (Sum.inl (T.interiorAlpha dart)) right
        hdartRight' hright
      exact hrotateLeft.trans (hedge.trans htailReach)

/-- The capped generator family is transitive.  Notice that no cyclicity of
the proposed hub rotation is used: every hub dart reaches the side across its
own spoke. -/
theorem wordReachable_hub_all
    (T : OpenTangleData V I B) (ρ : Perm B)
    (hconnected : (sideMultigraph T).Connected)
    (hrotation : OpenRotationCyclic T)
    (left right : (I ⊕ B) ⊕ B) :
    WordReachable (hubGenerators T ρ) left right := by
  have hreal : ∀ left right : I ⊕ B,
      WordReachable (hubGenerators T ρ) (Sum.inl left) (Sum.inl right) := by
    intro first second
    exact wordReachable_hub_real_of_sideReach T ρ hrotation
      (hconnected (T.vertOf first) (T.vertOf second)) first second rfl rfl
  rcases left with realLeft | hubLeft
  · rcases right with realRight | hubRight
    · exact hreal realLeft realRight
    · have htoBoundary := hreal realLeft (Sum.inr hubRight)
      have hspoke := wordReachable_hubAlpha T ρ
        (Sum.inl (Sum.inr hubRight))
      simpa [hubAlphaFun] using htoBoundary.trans hspoke
  · have hspokeLeft := wordReachable_hubAlpha T ρ (Sum.inr hubLeft)
    rcases right with realRight | hubRight
    · have hinside := hreal (Sum.inr hubLeft) realRight
      simpa [hubAlphaFun] using hspokeLeft.trans hinside
    · have hinside := hreal (Sum.inr hubLeft) (Sum.inr hubRight)
      have hspokeRight := wordReachable_hubAlpha T ρ
        (Sum.inl (Sum.inr hubRight))
      simpa [hubAlphaFun] using
        hspokeLeft.trans (hinside.trans hspokeRight)

/-- Therefore the component term in the generic Euler inequality is one. -/
theorem wordOrbitCount_hubGenerators_eq_one
    (T : OpenTangleData V I B) (ρ : Perm B)
    (hconnected : (sideMultigraph T).Connected)
    (hrotation : OpenRotationCyclic T)
    (port : B) :
    wordOrbitCount (hubGenerators T ρ) = 1 := by
  unfold wordOrbitCount
  rw [Fintype.card_eq_one_iff]
  refine ⟨Quotient.mk _ (Sum.inr port), ?_⟩
  intro component
  induction component using Quotient.inductionOn with
  | h dart =>
      exact Quotient.sound
        (wordReachable_hub_all T ρ hconnected hrotation dart (Sum.inr port))

/-- The old vertex map is constant along powers of the old rotation. -/
theorem vertOf_rho_pow
    (T : OpenTangleData V I B) (n : Nat) (dart : I ⊕ B) :
    T.vertOf ((T.rho ^ n) dart) = T.vertOf dart := by
  induction n generalizing dart with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Perm.mul_apply, ih]
      exact T.vert_rho dart

/-- Hence it is constant on whole rotation cycles. -/
theorem vertOf_eq_of_rho_sameCycle
    (T : OpenTangleData V I B) {left right : I ⊕ B}
    (hsame : T.rho.SameCycle left right) :
    T.vertOf left = T.vertOf right := by
  obtain ⟨power, hpower⟩ := exists_nat_pow_apply_eq hsame
  rw [← hpower, vertOf_rho_pow]

/-- When every displayed vertex has a dart and each vertex rotation is cyclic,
rotation orbits are exactly vertices. -/
def rhoOrbitEquivVertex
    (T : OpenTangleData V I B)
    (hrotation : OpenRotationCyclic T)
    (hsurj : Function.Surjective T.vertOf) :
    Quotient (SameCycle.setoid T.rho) ≃ V where
  toFun := Quotient.lift T.vertOf (fun _ _ h =>
    vertOf_eq_of_rho_sameCycle T h)
  invFun vertex := Quotient.mk _ (Classical.choose (hsurj vertex))
  left_inv component := by
    induction component using Quotient.inductionOn with
    | h dart =>
        apply Quotient.sound
        apply hrotation
        exact Classical.choose_spec (hsurj (T.vertOf dart))
  right_inv vertex := Classical.choose_spec (hsurj vertex)

theorem orbitCount_rho_eq_card_vertex
    (T : OpenTangleData V I B)
    (hrotation : OpenRotationCyclic T)
    (hsurj : Function.Surjective T.vertOf) :
    orbitCount T.rho = Fintype.card V := by
  unfold orbitCount
  exact Fintype.card_congr (rhoOrbitEquivVertex T hrotation hsurj)

/-- Cubicity is more than enough to ensure that every displayed open vertex
has a dart. -/
theorem vertOf_surjective_of_openIsCubic
    (T : OpenTangleData V I B) (hcubic : OpenIsCubic T) :
    Function.Surjective T.vertOf := by
  intro vertex
  have hcard := hcubic vertex
  have hnonempty : (openDartsAt T vertex).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hcard
    simp at hcard
  obtain ⟨dart, hdart⟩ := hnonempty
  exact ⟨dart, (Finset.mem_filter.1 hdart).2⟩

/-- Euler's inequality for the capped shore, without assuming that its hub
rotation is one cycle. -/
theorem orbitCount_hubRho_add_hubPhi_le
    (T : OpenTangleData V I B) (ρ : Perm B)
    (hconnected : (sideMultigraph T).Connected)
    (hrotation : OpenRotationCyclic T)
    (port : B) :
    orbitCount T.rho + orbitCount ρ + orbitCount (hubPhi T ρ) ≤
      orbitCount (hubAlpha T) + 2 := by
  have heuler := orbitCount_add_orbitCount_mul_le'
    (hubRho T ρ) (hubAlpha T) (hubAlphaFun_involutive T)
  have hcomponents := wordOrbitCount_hubGenerators_eq_one
    T ρ hconnected hrotation port
  have hlength := length_edgeList_eq_orbitCount
    (hubAlpha T) (hubAlphaFun_involutive T) (by
      rintro ((dart | boundary) | hub)
      · simpa [hubAlphaFun] using T.interiorAlpha_fixfree dart
      · simp [hubAlphaFun]
      · simp [hubAlphaFun])
  have hsum := orbitCount_sumCongr T.rho ρ
  change orbitCount (hubRho T ρ) + orbitCount (hubPhi T ρ) ≤ _ at heuler
  unfold hubGenerators at hcomponents
  rw [hcomponents, hlength] at heuler
  rw [hubRho, hsum] at heuler
  omega

/-- Exact one-hub rank leaves room for only one hub-rotation orbit. -/
theorem orbitCount_hubRotation_eq_one_of_closedSideSpherical
    (T : OpenTangleData V I B) (ρ : Perm B)
    (hconnected : (sideMultigraph T).Connected)
    (hrotation : OpenRotationCyclic T)
    (hcubic : OpenIsCubic T)
    (port : B)
    (hclosed : ClosedSideSpherical T ρ) :
    orbitCount ρ = 1 := by
  have heuler := orbitCount_hubRho_add_hubPhi_le
    T ρ hconnected hrotation port
  have hrho := orbitCount_rho_eq_card_vertex T hrotation
    (vertOf_surjective_of_openIsCubic T hcubic)
  have hpositive : 0 < orbitCount ρ := by
    unfold orbitCount
    exact Fintype.card_pos_iff.mpr ⟨Quotient.mk _ port⟩
  unfold ClosedSideSpherical at hclosed
  omega

/-- A one-orbit permutation puts every two points on the same cycle. -/
theorem sameCycle_all_of_orbitCount_eq_one
    (ρ : Perm B) (hcount : orbitCount ρ = 1) (left right : B) :
    ρ.SameCycle left right := by
  unfold orbitCount at hcount
  obtain ⟨root, hroot⟩ := Fintype.card_eq_one_iff.mp hcount
  have hrel : (SameCycle.setoid ρ).r left right :=
    Quotient.exact ((hroot (Quotient.mk _ left)).trans
      (hroot (Quotient.mk _ right)).symm)
  exact hrel

/-- If the carrier has two distinct points, one orbit is a genuine nontrivial
cycle with full support. -/
theorem isCycle_of_orbitCount_eq_one_of_ne
    (ρ : Perm B) (hcount : orbitCount ρ = 1)
    (first second : B) (hne : first ≠ second) :
    ρ.IsCycle := by
  have hall := sameCycle_all_of_orbitCount_eq_one ρ hcount
  have hfixfree : ∀ point : B, ρ point ≠ point := by
    intro point hfixed
    have hfirst := exists_nat_pow_apply_eq (hall point first)
    have hsecond := exists_nat_pow_apply_eq (hall point second)
    have hpowers : ∀ n : Nat, (ρ ^ n) point = point := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, Perm.mul_apply, hfixed, ih]
    obtain ⟨n, hn⟩ := hfirst
    obtain ⟨m, hm⟩ := hsecond
    apply hne
    rw [← hn, hpowers n, ← hm, hpowers m]
  apply (isCycle_iff_sameCycle (hfixfree first)).2
  intro point
  exact ⟨fun _ => hfixfree point, fun _ => hall first point⟩

/-- The reusable conclusion: on a connected cubic open shore, exact one-hub
Euler rank forces the proposed hub permutation to be a single cycle. -/
theorem hubRotation_isCycle_of_closedSideSpherical
    (T : OpenTangleData V I B) (ρ : Perm B)
    (hconnected : (sideMultigraph T).Connected)
    (hrotation : OpenRotationCyclic T)
    (hcubic : OpenIsCubic T)
    (first second : B) (hne : first ≠ second)
    (hclosed : ClosedSideSpherical T ρ) :
    ρ.IsCycle := by
  have hcount := orbitCount_hubRotation_eq_one_of_closedSideSpherical
    T ρ hconnected hrotation hcubic first hclosed
  exact isCycle_of_orbitCount_eq_one_of_ne ρ hcount first second hne

/-- The three exact cap facts consumed by the physical seam theorem. -/
structure CanonicalHubDiscData (T : OpenTangleData V I B) (ρ : Perm B) : Prop where
  facesDistinct : HubFacesDistinct T ρ
  closedSpherical : ClosedSideSpherical T ρ
  hubCycle : ρ.IsCycle

section GraphBacked

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- For a connected spherical planar bond, the canonical inverse first-return
order is automatically one cyclic hub.  No noose or Jordan separation theorem
is an input: connectedness supplies one word component, while the already
proved exact side rank supplies equality in Euler's bound. -/
theorem canonicalHubRotation_isCycle_of_planarBond
    (rotation : SimpleGraphDartRotation.Data G)
    (deleted : Finset V)
    (outer : RetainedDart rotation.toRotationSystem
      (deletedRegionKeep deleted))
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        ¬ deletedRegionKeep deleted vertex}).Connected)
    (first second : BoundaryDart rotation.toRotationSystem
      (deletedRegionKeep deleted))
    (hne : first ≠ second) :
    (canonicalHubRotation rotation.toRotationSystem
      (deletedRegionKeep deleted)).IsCycle := by
  let RS := rotation.toRotationSystem
  let keep := deletedRegionKeep deleted
  let T := ofVertexSide RS keep outer
  have hretainedConnected' :
      ((rotationPrimalGraph RS).induce {vertex | keep vertex}).Connected := by
    simpa [RS, keep,
      GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq]
      using hretainedConnected
  have hside : (sideMultigraph T).Connected :=
    sideMultigraph_connected_of_induce_connected RS keep outer
      hretainedConnected'
  have hopenRotation : OpenRotationCyclic T :=
    openRotationCyclic_ofVertexSide RS keep outer hrotation
  have hopenCubic : OpenIsCubic T :=
    openIsCubic_ofVertexSide RS keep outer hsphere.cubic
  have hclosed : ClosedSideSpherical T (canonicalHubRotation RS keep) :=
    closedSideSpherical_canonical_of_planarBond rotation deleted outer
      hsphere htwoSided hconnected hrotation
      hretainedConnected hdeletedConnected
  exact hubRotation_isCycle_of_closedSideSpherical T
    (canonicalHubRotation RS keep) hside hopenRotation hopenCubic
    first second hne hclosed

/-- A graph-backed connected planar bond supplies the whole canonical cap
package: face-simplicity, exact spherical rank, and one cyclic hub. -/
def canonicalHubDiscData_of_planarBond
    (rotation : SimpleGraphDartRotation.Data G)
    (deleted : Finset V)
    (outer : RetainedDart rotation.toRotationSystem
      (deletedRegionKeep deleted))
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        ¬ deletedRegionKeep deleted vertex}).Connected)
    (first second : BoundaryDart rotation.toRotationSystem
      (deletedRegionKeep deleted))
    (hne : first ≠ second) :
    CanonicalHubDiscData
      (ofVertexSide rotation.toRotationSystem
        (deletedRegionKeep deleted) outer)
      (canonicalHubRotation rotation.toRotationSystem
        (deletedRegionKeep deleted)) where
  facesDistinct := hubFacesDistinct_canonical rotation.toRotationSystem
    (deletedRegionKeep deleted) outer
  closedSpherical := closedSideSpherical_canonical_of_planarBond
    rotation deleted outer hsphere htwoSided hconnected hrotation
      hretainedConnected hdeletedConnected
  hubCycle := canonicalHubRotation_isCycle_of_planarBond
    rotation deleted outer hsphere htwoSided hconnected hrotation
      hretainedConnected hdeletedConnected first second hne

end GraphBacked

end

end GoertzelV24CanonicalHubCyclicity

end Mettapedia.GraphTheory.FourColor
