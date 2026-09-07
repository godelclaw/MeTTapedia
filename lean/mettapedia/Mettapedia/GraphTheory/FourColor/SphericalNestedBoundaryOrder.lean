import Mettapedia.GraphTheory.FourColor.InvolutionRestrictionEdgeList
import Mettapedia.GraphTheory.FourColor.PlanarMapBoundaryRestriction
import Mettapedia.GraphTheory.FourColor.GoertzelV24StellarDualStructure
import Mettapedia.GraphTheory.FourColor.GoertzelV24CanonicalHubCyclicity

/-!
# Boundary order of nested vertex sides

The internal-edge involutions of nested vertex sides admit a planar edge
extension on the original dart carrier. Euler equality and component
reachability are derived from the ambient spherical map, not supplied as
properties of a proposed slab. The resulting order theorem concerns the
literal persistent crossing darts.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalNestedBoundaryOrder

open Equiv Equiv.Perm
open GoertzelV24MapEulerBound GoertzelV24InvolutionEdgeList
open GoertzelV24ConnectedMapEulerBound GoertzelV24WordReachability
open GoertzelV24PermutationOrbitSurgery GoertzelV24FaceDualConnectedness
open GoertzelV24RotationMultigraphAdapter GoertzelV24StellarDualStructure
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24FaceOrbitIncidence
open GoertzelV24OrderedCutFaceReturnProfile
open InvolutionRestrictionEdgeList PlanarMapBoundaryRestriction

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def InsideEdge (RS : RotationSystem V E) (side : V → Prop) (d : RS.D) : Prop :=
  side (RS.vertOf d) ∧ side (RS.vertOf (RS.alpha d))

theorem inside_alpha (RS : RotationSystem V E) (side : V → Prop) (d : RS.D) :
    InsideEdge RS side (RS.alpha d) ↔ InsideEdge RS side d := by
  simp only [InsideEdge, RS.alpha_involutive, and_comm]

/-- The full-carrier capped flip fixes every edge not internal to the side. -/
def cappedAlpha (RS : RotationSystem V E) (side : V → Prop) : Perm RS.D :=
  restrict RS.alpha RS.alpha_involutive (InsideEdge RS side) (inside_alpha RS side)

theorem cappedAlpha_apply (RS : RotationSystem V E) (side : V → Prop) (d : RS.D) :
    cappedAlpha RS side d = if InsideEdge RS side d then RS.alpha d else d :=
  restrict_apply _ _ _ _ _

theorem cappedAlpha_involutive (RS : RotationSystem V E) (side : V → Prop) :
    Function.Involutive (cappedAlpha RS side) := restrict_involutive _ _ _ _

def cappedPhi (RS : RotationSystem V E) (side : V → Prop) : Perm RS.D :=
  RS.rho * cappedAlpha RS side

/-- Any exact edge presentation of a connected spherical map has Euler
equality, irrespective of the order in which its edges are presented. -/
theorem planeEdges_of_spherical (RS : RotationSystem V E)
    (hsphere : OrbitSphericalCubicMapData RS)
    (hconn : (rotationPrimalGraph RS).Connected) (hrot : VertexRotationCyclic RS)
    (edges : List (RS.D × RS.D)) (hprod : swapProduct edges = RS.alpha)
    (hlen : edges.length = Fintype.card E) : PlaneEdges RS.rho edges := by
  have hall (x y : RS.D) : WordReachable (RS.rho :: swapGenerators edges) x y := by
    apply wordReachable_absorb _ (wordReachable_pair_all_of_primalConnected RS hconn hrot x y)
    intro g hg d
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact wordReachable_step List.mem_cons_self d
    · simpa only [hprod] using wordReachable_swapProduct RS.rho edges d
  have hc : wordOrbitCount (RS.rho :: swapGenerators edges) = 1 := by
    unfold wordOrbitCount
    rw [Fintype.card_eq_one_iff]
    refine ⟨Quotient.mk _ RS.outer, ?_⟩
    intro component
    induction component using Quotient.inductionOn with
    | h d => exact Quotient.sound (hall d RS.outer)
  have hsurj : Function.Surjective RS.vertOf := by
    intro v
    have hcard := hsphere.cubic v
    have hn : (RS.dartsAt v).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨d, hd⟩ := hn
    exact ⟨d, (Finset.mem_filter.mp hd).2⟩
  have hv := GoertzelV24StellarDualStructure.orbitCount_rho_eq_card_vertex RS hrot hsurj
  have hf := orbitCount_phi_eq_card_orbitFace RS
  unfold PlaneEdges
  rw [hprod, hlen, hc, hv]
  change Fintype.card V + orbitCount RS.phi = Fintype.card E + 2 * 1
  rw [hf]
  have he := hsphere.euler
  omega

/-- The extension is constructed from actual internal edges of the two sides.
The remaining ambient edges certify its planarity by deletion. -/
theorem exists_capped_edge_extension (RS : RotationSystem V E)
    (hsphere : OrbitSphericalCubicMapData RS)
    (hconn : (rotationPrimalGraph RS).Connected) (hrot : VertexRotationCyclic RS)
    (inner outer : V → Prop) (hsub : ∀ v, inner v → outer v) :
    ∃ added : List (RS.D × RS.D),
      swapProduct (added ++ edgeList (cappedAlpha RS inner)) = cappedAlpha RS outer ∧
      (∀ e ∈ added ++ edgeList (cappedAlpha RS inner), e.1 ≠ e.2) ∧
      PlaneEdges RS.rho (added ++ edgeList (cappedAlpha RS inner)) := by
  let a := cappedAlpha RS outer
  let keep := InsideEdge RS inner
  have hk (d : RS.D) : keep (a d) ↔ keep d := by
    dsimp only [a, keep]
    rw [cappedAlpha_apply]
    split_ifs
    · exact inside_alpha RS inner d
    · rfl
  have heq : restrict a (cappedAlpha_involutive RS outer) keep hk = cappedAlpha RS inner := by
    ext d
    simp only [restrict_apply]
    by_cases hi : keep d
    · have ho : InsideEdge RS outer d := ⟨hsub _ hi.1, hsub _ hi.2⟩
      change InsideEdge RS inner d at hi
      simp only [keep, hi, if_pos, a, cappedAlpha_apply, ho]
    · change ¬ InsideEdge RS inner d at hi
      simp [keep, hi, cappedAlpha_apply]
  let added := edgeList (restrict a (cappedAlpha_involutive RS outer)
    (fun d => ¬ keep d) (fun d => not_congr (hk d)))
  let base := edgeList (cappedAlpha RS inner)
  have hp : swapProduct (added ++ base) = a := by
    rw [swapProduct_append]
    dsimp only [added, base]
    rw [swapProduct_edgeList _ (restrict_involutive _ _ _ _),
      swapProduct_edgeList _ (cappedAlpha_involutive RS inner), ← heq]
    exact restrict_compl_mul _ _ _ _
  have hl : (added ++ base).length = (edgeList a).length := by
    have hh := length_restrict_add_compl a (cappedAlpha_involutive RS outer) keep hk
    rw [heq] at hh
    simpa only [List.length_append] using hh
  let excluded := edgeList (restrict RS.alpha RS.alpha_involutive
    (fun d => ¬ InsideEdge RS outer d) (fun d => not_congr (inside_alpha RS outer d)))
  have hpAll : swapProduct (excluded ++ (added ++ base)) = RS.alpha := by
    rw [swapProduct_append, hp]
    dsimp only [excluded, a, cappedAlpha]
    rw [swapProduct_edgeList _ (restrict_involutive _ _ _ _)]
    exact restrict_compl_mul _ _ _ _
  have hlAll : (excluded ++ (added ++ base)).length = Fintype.card E := by
    rw [List.length_append, hl]
    have hh := length_restrict_add_compl RS.alpha RS.alpha_involutive
      (InsideEdge RS outer) (inside_alpha RS outer)
    change excluded.length + (edgeList a).length = (edgeList RS.alpha).length at hh
    rw [hh, length_edgeList_eq_orbitCount RS.alpha RS.alpha_involutive RS.alpha_fixfree,
      orbitCount_alpha_eq_card_edge RS]
  have hn : ∀ e ∈ excluded ++ (added ++ base), e.1 ≠ e.2 := by
    intro e he
    simp only [List.mem_append] at he
    rcases he with he | he | he <;> exact edgeList_fst_ne_snd _ e he
  refine ⟨added, hp, fun e he => hn e (List.mem_append_right _ he), ?_⟩
  exact plane_tail RS.rho excluded (added ++ base) hn
    (planeEdges_of_spherical RS hsphere hconn hrot _ hpAll hlAll)

open GoertzelV24RotationCutDartDecomposition GoertzelV24RetainedRegionBoundaryOrder
open PermutationFirstReturnRestriction

/-- A marked subset of the boundary, with the ambient dart unchanged. -/
def markedBoundaryEquiv (RS : RotationSystem V E) (side : V → Prop)
    (hit : RS.D → Prop) (hin : ∀ d, hit d → side (RS.vertOf d))
    (hout : ∀ d, hit d → ¬ side (RS.vertOf (RS.alpha d))) :
    {d // hit d} ≃ {b : BoundaryDart RS side // hit b.val.val} where
  toFun d := ⟨⟨⟨d.val, hin _ d.2⟩, hout _ d.2⟩, d.2⟩
  invFun b := ⟨b.val.val.val, b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Restrict the stack's complete boundary successor to marked darts and
return to their original ambient identities. -/
def boundaryOrderOn (RS : RotationSystem V E) (side : V → Prop)
    (hit : RS.D → Prop) (hin : ∀ d, hit d → side (RS.vertOf d))
    (hout : ∀ d, hit d → ¬ side (RS.vertOf (RS.alpha d))) : Perm {d // hit d} :=
  (markedBoundaryEquiv RS side hit hin hout).symm.permCongr
    (nextHitPerm (retainedRegionBoundarySuccessor RS side) (fun b => hit b.val.val))

/-- A walk inside a vertex side lifts through its actual internal edges. -/
theorem wordReachable_capped_of_walk (RS : RotationSystem V E)
    (hrot : VertexRotationCyclic RS) (side : V → Prop)
    {u v : {v // side v}} (walk : ((rotationPrimalGraph RS).induce {v | side v}).Walk u v) :
    ∀ x y : RS.D, RS.vertOf x = u.val → RS.vertOf y = v.val →
      WordReachable (RS.rho :: swapGenerators (edgeList (cappedAlpha RS side))) x y := by
  have hrotate (x y : RS.D) (hv : RS.vertOf x = RS.vertOf y) :
      WordReachable (RS.rho :: swapGenerators (edgeList (cappedAlpha RS side))) x y := by
    obtain ⟨n, hn⟩ := exists_nat_pow_apply_eq (hrot x y hv)
    simpa only [hn] using wordReachable_pow (L := RS.rho ::
      swapGenerators (edgeList (cappedAlpha RS side))) List.mem_cons_self x n
  induction walk with
  | nil => intro x y hx hy; exact hrotate x y (hx.trans hy.symm)
  | @cons u w v hadj tail ih =>
    intro x y hx hy
    obtain ⟨d, hdU, hdW⟩ := (rotationPrimalGraph_adj_iff RS).mp hadj
    have hi : InsideEdge RS side d := ⟨hdU ▸ u.2, hdW ▸ w.2⟩
    have he := wordReachable_swapProduct RS.rho (edgeList (cappedAlpha RS side)) d
    rw [swapProduct_edgeList _ (cappedAlpha_involutive RS side),
      cappedAlpha_apply, if_pos hi] at he
    exact (hrotate x d (hx.trans hdU.symm)).trans
      (he.trans (ih (RS.alpha d) y hdW hy))

/-- The full-carrier capped face walk restricts to the existing retained-dart
face walk by the literal subtype inclusion. -/
theorem cappedPhi_retained (RS : RotationSystem V E) (side : V → Prop)
    (d : RetainedDart RS side) :
    cappedPhi RS side d.val = (retainedCappedFacePerm RS side d).val := by
  simp only [cappedPhi, retainedCappedFacePerm, Perm.mul_apply, retainedRho_val,
    cappedAlpha_apply, InsideEdge, d.2, true_and]
  by_cases h : side (RS.vertOf (RS.alpha d.val))
  · rw [if_pos h, retainedCappedAlpha_apply_internal RS side d h]
  · rw [if_neg h, retainedCappedAlpha_apply_boundary RS side d h]

/-- Computing first return on the complete boundary and then restricting
agrees exactly with computing it on the full-carrier capped face walk. -/
theorem boundaryOrderOn_eq (RS : RotationSystem V E) (side : V → Prop)
    (hit : RS.D → Prop) (hin : ∀ d, hit d → side (RS.vertOf d))
    (hout : ∀ d, hit d → ¬ side (RS.vertOf (RS.alpha d))) :
    boundaryOrderOn RS side hit hin hout = nextHitPerm (cappedPhi RS side) hit := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  let small := fun d : RetainedDart RS side => hit d.val
  let big := fun d : RetainedDart RS side => ¬ side (RS.vertOf (RS.alpha d.val))
  have hs (d : RetainedDart RS side) (hd : small d) : big d := hout d.val hd
  let sx : {d : RetainedDart RS side // small d} := ⟨⟨x.val, hin _ x.2⟩, x.2⟩
  have hn := congrArg
    (fun p : Perm {d : {d : RetainedDart RS side // big d} // small d.val} =>
      (p (nestedMarks small big hs sx)).val.val.val)
    (nextHit_nested (retainedCappedFacePerm RS side) small big hs)
  change (boundaryOrderOn RS side hit hin hout x).val =
    (nextHitPerm (retainedCappedFacePerm RS side) small sx).val.val at hn
  have hm := nextHit_map (retainedCappedFacePerm RS side) (cappedPhi RS side)
    Subtype.val (cappedPhi_retained RS side) small hit (fun _ => Iff.rfl) sx
  exact hn.trans hm.symm

/-- One connected old side suffices for the component condition in the
planar extension theorem; the marked set may omit arbitrarily many ports. -/
theorem nextHit_capped_eq (RS : RotationSystem V E)
    (hsphere : OrbitSphericalCubicMapData RS)
    (hconn : (rotationPrimalGraph RS).Connected) (hrot : VertexRotationCyclic RS)
    (inner outer : V → Prop) (hsub : ∀ v, inner v → outer v)
    (hinner : ((rotationPrimalGraph RS).induce {v | inner v}).Connected)
    (hit : RS.D → Prop) (hin : ∀ d, hit d → inner (RS.vertOf d))
    (hface : ∀ x y, hit x → hit y → (cappedPhi RS outer).SameCycle x y) :
    nextHitPerm (cappedPhi RS outer) hit = nextHitPerm (cappedPhi RS inner) hit := by
  obtain ⟨added, hp, hn, hplane⟩ :=
    exists_capped_edge_extension RS hsphere hconn hrot inner outer hsub
  have hc (x y : RS.D) (hx : hit x) (hy : hit y) :
      WordReachable (RS.rho :: swapGenerators (edgeList (cappedAlpha RS inner))) x y := by
    obtain ⟨walk⟩ := hinner ⟨RS.vertOf x, hin x hx⟩ ⟨RS.vertOf y, hin y hy⟩
    exact wordReachable_capped_of_walk RS hrot inner walk x y rfl rfl
  have hh := nextHit_face_extension RS.rho added (edgeList (cappedAlpha RS inner))
    hit hn hplane hc (by simpa only [hp, cappedPhi] using hface)
  simpa only [hp, swapProduct_edgeList _ (cappedAlpha_involutive RS inner), cappedPhi] using hh

open GoertzelV24CanonicalHubCyclicity GoertzelV24CanonicalHubClosure
open GoertzelV24CompositeSeamCubic GoertzelV24CompositeSeamMultigraph
open GoertzelV24CompositeSphericity GoertzelV24DeletedRegionRotationSplice
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24VertexSideOpenTangle GoertzelV24OrbitFaceTwoSided

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A connected and coconnected spherical side has all of its exposed darts
on one capped face, including the singleton-boundary case. -/
theorem retained_boundary_sameCycle (rotation : SimpleGraphDartRotation.Data G)
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconn : G.Connected) (hrot : VertexRotationCyclic rotation.toRotationSystem)
    (side : V → Prop) (hside : (G.induce {v | side v}).Connected)
    (hcomp : (G.induce {v | ¬ side v}).Connected)
    (x y : BoundaryDart rotation.toRotationSystem side) :
    (retainedCappedFacePerm rotation.toRotationSystem side).SameCycle x.val y.val := by
  let deleted := Finset.univ.filter (fun v => ¬ side v)
  have heq : deletedRegionKeep deleted = side := by
    funext v
    simp [deletedRegionKeep, deleted]
  revert x y
  rw [← heq] at hside hcomp ⊢
  intro x y
  let RS := rotation.toRotationSystem
  let keep := deletedRegionKeep deleted
  let T := ofVertexSide RS keep x.val
  have hside' : ((rotationPrimalGraph RS).induce {v | keep v}).Connected := by
    simpa only [RS, keep,
      GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq]
      using hside
  have hcount := orbitCount_hubRotation_eq_one_of_closedSideSpherical T
    (canonicalHubRotation RS keep)
    (sideMultigraph_connected_of_induce_connected RS keep x.val hside')
    (openRotationCyclic_ofVertexSide RS keep x.val hrot)
    (openIsCubic_ofVertexSide RS keep x.val hsphere.cubic) x
    (closedSideSpherical_canonical_of_planarBond rotation deleted x.val
      hsphere htwo hconn hrot hside hcomp)
  have hh := sameCycle_all_of_orbitCount_eq_one (canonicalHubRotation RS keep) hcount x y
  exact (nextHitPerm_sameCycle_iff _ _ x y).mp hh.of_inv

/-- The same one-face fact on the original ambient dart carrier. -/
theorem capped_boundary_sameCycle (rotation : SimpleGraphDartRotation.Data G)
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconn : G.Connected) (hrot : VertexRotationCyclic rotation.toRotationSystem)
    (side : V → Prop) (hside : (G.induce {v | side v}).Connected)
    (hcomp : (G.induce {v | ¬ side v}).Connected)
    (x y : rotation.toRotationSystem.D)
    (hx : side (rotation.toRotationSystem.vertOf x) ∧
      ¬ side (rotation.toRotationSystem.vertOf (rotation.toRotationSystem.alpha x)))
    (hy : side (rotation.toRotationSystem.vertOf y) ∧
      ¬ side (rotation.toRotationSystem.vertOf (rotation.toRotationSystem.alpha y))) :
    (cappedPhi rotation.toRotationSystem side).SameCycle x y := by
  let RS := rotation.toRotationSystem
  let bx : BoundaryDart RS side := ⟨⟨x, hx.1⟩, hx.2⟩
  let by' : BoundaryDart RS side := ⟨⟨y, hy.1⟩, hy.2⟩
  obtain ⟨n, hn⟩ := exists_nat_pow_apply_eq
    (retained_boundary_sameCycle rotation hsphere htwo hconn hrot side hside hcomp bx by')
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast]
  have hh := pow_map (retainedCappedFacePerm RS side) (cappedPhi RS side)
    Subtype.val (cappedPhi_retained RS side) n bx.val
  rw [hn] at hh
  exact hh

/-- Darts crossing both nested cuts in the outward orientation. -/
def CommonWire (RS : RotationSystem V E) (inner outer : V → Prop) (d : RS.D) : Prop :=
  inner (RS.vertOf d) ∧ ¬ outer (RS.vertOf (RS.alpha d))

/-- Persistent crossing darts retain their exact first-return order when
the outer side and its complement are connected. All geometry is derived
from the original spherical map and actual nested vertex predicates. -/
theorem commonWire_order (rotation : SimpleGraphDartRotation.Data G)
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconn : G.Connected) (hrot : VertexRotationCyclic rotation.toRotationSystem)
    (inner outer : V → Prop) (hsub : ∀ v, inner v → outer v)
    (hinner : (G.induce {v | inner v}).Connected)
    (houter : (G.induce {v | outer v}).Connected)
    (hcomp : (G.induce {v | ¬ outer v}).Connected) :
    nextHitPerm (cappedPhi rotation.toRotationSystem outer)
        (CommonWire rotation.toRotationSystem inner outer) =
      nextHitPerm (cappedPhi rotation.toRotationSystem inner)
        (CommonWire rotation.toRotationSystem inner outer) := by
  let RS := rotation.toRotationSystem
  apply nextHit_capped_eq RS hsphere
    (by simpa only [RS,
      GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq]
      using hconn) hrot inner outer hsub
    (by simpa only [RS,
      GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq]
      using hinner) _ (fun _ hd => hd.1)
  intro x y hx hy
  exact capped_boundary_sameCycle rotation hsphere htwo hconn hrot outer houter hcomp
    x y ⟨hsub _ hx.1, hx.2⟩ ⟨hsub _ hy.1, hy.2⟩

/-- The exact persistent-wire order in the stack's original boundary API.
The two identifications fix every ambient dart, rather than choosing a
cyclic shift or an arbitrary permutation of surviving wires. -/
theorem commonWire_boundaryOrder (rotation : SimpleGraphDartRotation.Data G)
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconn : G.Connected) (hrot : VertexRotationCyclic rotation.toRotationSystem)
    (inner outer : V → Prop) (hsub : ∀ v, inner v → outer v)
    (hinner : (G.induce {v | inner v}).Connected)
    (houter : (G.induce {v | outer v}).Connected)
    (hcomp : (G.induce {v | ¬ outer v}).Connected) :
    boundaryOrderOn rotation.toRotationSystem outer
        (CommonWire rotation.toRotationSystem inner outer)
        (fun _ h => hsub _ h.1) (fun _ h => h.2) =
      boundaryOrderOn rotation.toRotationSystem inner
        (CommonWire rotation.toRotationSystem inner outer)
        (fun _ h => h.1) (fun _ h hv => h.2 (hsub _ hv)) := by
  rw [boundaryOrderOn_eq, boundaryOrderOn_eq]
  exact commonWire_order rotation hsphere htwo hconn hrot inner outer hsub hinner houter hcomp

end
end Mettapedia.GraphTheory.FourColor.SphericalNestedBoundaryOrder
