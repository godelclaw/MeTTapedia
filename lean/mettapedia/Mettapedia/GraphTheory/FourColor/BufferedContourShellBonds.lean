import Mettapedia.GraphTheory.FourColor.BufferedContourShell

/-!
# Complete ordered interfaces of the buffered shell

The two caps constructed by flooding give actual planar bonds. Their
interfaces include every original crossing edge; facial uniqueness and
opposite first-return orders follow from the existing planar-bond theorem.
The width used here is the actual cut size, not a uniform bound inferred
from the number of selected columns.

The large-map alternative constructs the shell rather than asking for one.
The unresolved branch remains a colour-compatible strict shortening of
that shell. Merely constructing its ordered interfaces does not shorten it.
-/

namespace Mettapedia.GraphTheory.FourColor.BufferedContourShell

open SimpleGraph SimpleGraphDartRotation VertexSeparatorBond ProtectedContourBand
open GoertzelV24FaceOrbitIncidence GoertzelV24PrimalCycleFacialBond
open GoertzelV24OrbitFaceTwoSided GoertzelV24TwoEdgeCutMinimality
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24DeletedRegionRotationSplice GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24RetainedRegionBoundaryOrder GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24PlanarBondBoundaryOrder GoertzelV24RotationCutDartDecomposition
open SphericalDistanceContours SphericalContourSeparators SphericalProtectedLinkedBand
open GoertzelV24ConnectedVertexSideEdgeShore
open GoertzelV24ConnectedShoreLiteralNode
open GoertzelV24RotationMultigraphAdapter GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24MajorityShorePhysicalReplacement SphericalMeshFreeSeam MarkedCotreeSeam

noncomputable section
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Connect an already constructed connected cap to the full planar-bond API.
The output shore is exactly S, not a smaller selected-path subgraph. -/
def orderedBondOfConnected (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) (lo hi : Nat) (S : Set V)
    (hS : (G.induce S).Connected) (hSc : (G.induce Sᶜ).Connected)
    (hfirst : frontier data root far lo ⊆ S)
    (hlast : frontier data root far hi ⊆ Sᶜ) :
    OrderedContourBond data root far lo hi (edgeBoundary G S).card := by
  classical
  let deleted := Sᶜ.toFinset
  have hkeep : {v | deletedRegionKeep deleted v} = S := by
    ext v
    simp [deletedRegionKeep, deleted]
  have hnotkeep : {v | ¬ deletedRegionKeep deleted v} = Sᶜ := by
    change {v | deletedRegionKeep deleted v}ᶜ = Sᶜ
    rw [hkeep]
  have hret : (G.induce {v | deletedRegionKeep deleted v}).Connected := hkeep ▸ hS
  have hdel : (G.induce {v | ¬ deletedRegionKeep deleted v}).Connected := hnotkeep ▸ hSc
  have hG : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using ambient.primalConnected
  refine ⟨deleted, hkeep ▸ hfirst, hnotkeep ▸ hlast, hret, hdel, ?_, ?_, ?_, ?_⟩
  · simp only [hkeep, le_refl]
  · exact (card_boundaryDart_le_edgeBoundary data {v | deletedRegionKeep deleted v}).trans
      (by rw [hkeep])
  · exact cutFacesHaveUniqueRetainedBoundaryDart_of_planar_bond data deleted
      ambient.spherical htwo hG ambient.vertexRotationCyclic hret hdel
  · exact retained_boundarySuccessor_eq_deleted_inverse_of_planar_bond data deleted
      ambient.spherical htwo hG ambient.vertexRotationCyclic hret hdel

@[simp] theorem orderedBondOfConnected_keep (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) (lo hi : Nat) (S : Set V)
    (hS : (G.induce S).Connected) (hSc : (G.induce Sᶜ).Connected)
    (hfirst : frontier data root far lo ⊆ S)
    (hlast : frontier data root far hi ⊆ Sᶜ) :
    {v | deletedRegionKeep
      (orderedBondOfConnected data ambient htwo root far lo hi S hS hSc hfirst hlast).deleted v} = S := by
  classical
  ext v
  simp [orderedBondOfConnected, deletedRegionKeep]

/-- Both complete shell interfaces have their actual cyclic order. The shores
are strictly nested as vertex sets and as full incident-edge shores. -/
theorem ShellOf.exists_ordered_bonds (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    {marks : Finset V} {a n : Nat} {B : LinkedBand data marks a n}
    (C : ShellOf data B) (ha : 4 ≤ a) :
    ∃ outer : OrderedContourBond data B.root B.far B.lo (B.lo + 1)
        (edgeBoundary G C.outer).card,
      ∃ inner : OrderedContourBond data B.root B.far (B.lo + a - 2) (B.lo + a - 1)
          (edgeBoundary G C.innerᶜ).card,
        {v | deletedRegionKeep outer.deleted v} = C.outer ∧
        {v | deletedRegionKeep inner.deleted v} = C.innerᶜ ∧
        C.outer ⊂ C.innerᶜ ∧
        incidentEdgeShore G (deletedRegionKeep outer.deleted) ⊂
          incidentEdgeShore G (deletedRegionKeep inner.deleted) := by
  classical
  have hmid (d : Nat) (hd : B.lo + 1 ≤ d) (hd' : d ≤ B.lo + a - 2) :
      frontier data B.root B.far d ⊆ (C.outer ∪ C.inner)ᶜ :=
    fun _ h => C.contains_middle (frontier_subset_band data B.root B.far hd hd' h)
  have hlast : frontier data B.root B.far (B.lo + 1) ⊆ C.outerᶜ :=
    fun _ h ho => hmid _ (by omega) (by omega) h (Or.inl ho)
  have hfirst : frontier data B.root B.far (B.lo + a - 2) ⊆ C.innerᶜ :=
    fun _ h hi => hmid _ (by omega) (by omega) h (Or.inr hi)
  have hlast' : frontier data B.root B.far (B.lo + a - 1) ⊆ C.innerᶜᶜ := by
    simpa using C.inner_contour
  have hcc : (G.induce C.innerᶜᶜ).Connected := by
    rw [compl_compl]
    exact C.inner_connected
  let outer := orderedBondOfConnected data ambient htwo B.root B.far B.lo (B.lo + 1)
    C.outer C.outer_connected C.outer_complement_connected C.outer_contour hlast
  let inner := orderedBondOfConnected data ambient htwo B.root B.far (B.lo + a - 2)
    (B.lo + a - 1) C.innerᶜ C.inner_complement_connected hcc hfirst hlast'
  have ho : {v | deletedRegionKeep outer.deleted v} = C.outer := by simp [outer]
  have hi : {v | deletedRegionKeep inner.deleted v} = C.innerᶜ := by simp [inner]
  have hstrict : {v | deletedRegionKeep outer.deleted v} ⊂
      {v | deletedRegionKeep inner.deleted v} :=
    contour_bonds_strict data ambient htwo B.root B.far
      (i := B.lo) (j := B.lo + 1) (p := B.lo + a - 2) (q := B.lo + a - 1)
      (by omega) (by omega) (by omega) (by have := B.depth; omega)
      outer.connected inner.complement_connected outer.first outer.last inner.first inner.last
  refine ⟨outer, inner, ho, hi, by simpa only [ho, hi] using hstrict, ?_⟩
  obtain ⟨x, hx, hxold⟩ := Set.exists_of_ssubset hstrict
  obtain ⟨y⟩ := inner.complement_connected.nonempty
  exact NestedCyclicCutStrictness.incidentEdgeShore_ssubset
    (fun _ h => hstrict.subset h) ⟨x, hx, hxold⟩ ⟨y, y.property⟩
    outer.complement_connected.preconnected

variable [G.LocallyFinite] {M : Type v} [Fintype M]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- The constructed interfaces reach the existing Count node type. Their
separate actual widths are retained; no repeated state is inferred. -/
theorem ShellOf.exists_connected_nodes (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    {marks : Finset V} {a n : Nat} {B : LinkedBand data marks a n}
    (C : ShellOf data B) (ha : 4 ≤ a) :
    ∃ outer : ConnectedShoreNode (G := G) (edgeBoundary G C.outer).card (edgeBoundary G C.outer).card,
      ∃ inner : ConnectedShoreNode (G := G) (edgeBoundary G C.innerᶜ).card (edgeBoundary G C.innerᶜ).card,
        outer.shore = incidentEdgeShore G (· ∈ C.outer) ∧
        inner.shore = incidentEdgeShore G (· ∈ C.innerᶜ) ∧ outer.shore ⊂ inner.shore := by
  obtain ⟨O, I, hO, hI, _, hstrict⟩ := C.exists_ordered_bonds data ambient htwo ha
  have ho : deletedRegionKeep O.deleted = (· ∈ C.outer) := by
    funext v
    exact congrArg (fun S : Set V => v ∈ S) hO
  have hi : deletedRegionKeep I.deleted = (· ∈ C.innerᶜ) := by
    funext v
    exact congrArg (fun S : Set V => v ∈ S) hI
  let outer := O.toConnectedNode data ambient htwo B.root B.far
    (by have := B.depth; omega) (by have := B.depth; omega)
  let inner := I.toConnectedNode data ambient htwo B.root B.far
    (by have := B.depth; omega) (by have := B.depth; omega)
  exact ⟨outer, inner, by simp [outer, ho], by simp [inner, hi], hstrict⟩

/-- Global largeness supplies the buffered shell or the already verified
strict replacement. No cap-connectedness or shell-supply hypothesis is added. -/
theorem exists_bufferedShell_or_marked_replacement (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (hzero : ¬ RotationSystemTaitColorable data.toRotationSystem)
    (a b : Nat) (ha : 4 ≤ a) (marks : Finset V) (mark : M → G.Dart)
    (hmarks : ∀ m, (mark m).fst ∈ marks)
    (hclosed : ∀ m, ∃ m', data.toRotationSystem.alpha (mark m) = mark m')
    (hlarge : sizeBound ((marks.card + 1) * a) b marks.card (Fintype.card M) < Fintype.card V) :
    (∃ B : LinkedBand data marks a (orderedLinkageSize ((marks.card + 1) * a) b),
      Nonempty (ShellOf data B)) ∨
      ∃ w, w ≤ widthBound ((marks.card + 1) * a) b marks.card (Fintype.card M) ∧
        ∃ pair : SeamPair data marks mark w,
          Nonempty (StrictPhysicalReplacementData data pair.outer.shore pair.inner.shore
            pair.outer.outsideOuter pair.inner.innerOuter pair.width pair.outerWidth pair.innerWidth) ∧
          ∀ m, ∃ d : pair.candidate.D, pair.ambientDart d = mark m ∧
            pair.ambientDart (pair.candidate.alpha d) = data.toRotationSystem.alpha (mark m) := by
  rcases exists_linkedBand_or_marked_replacement data ambient htwo hzero a b (by omega)
      marks mark hmarks hclosed hlarge with hB | h
  · obtain ⟨B⟩ := hB
    exact Or.inl ⟨B, exists_shell data ambient htwo B ha (by simp [orderedLinkageSize])⟩
  · exact Or.inr h

end
end Mettapedia.GraphTheory.FourColor.BufferedContourShell
