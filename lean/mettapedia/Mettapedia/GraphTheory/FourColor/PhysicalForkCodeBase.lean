import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFold
import Mettapedia.GraphTheory.FourColor.GoertzelV24ForkTaitBridge
import Mettapedia.GraphTheory.FourColor.GoertzelV24DecomposableFiniteBase

/-!
# The finite code consumed by the decomposable finite base

The root of an edge-leaf tree covering the whole map has no middle vertices.
Its code records exactly two things the finite base needs: whether the map has
a Tait colouring (the colour field is empty exactly when it has none), and
whether the map has a cut of size at most one (a record with both flags set).
A connected bridgeless map has no such record.

With the coverage theorem of `PhysicalForkCodeFold`, this instantiates the
existing `DecomposableBaseReflection` of the finite base: the state is a root
code, the reachable set is the finite set of root codes in the closure `Reach`
at interface bound `max w 2`, and the necessary condition is `Rejecting`.
The remaining input is the audit: no reachable root code is rejecting.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeBase

open Equiv Equiv.Perm
open GoertzelV24ForkInterfaceSupport GoertzelV24ForkProjection
open EdgeShoreFaceForkFold PhysicalForkCodeFaces PhysicalForkCodeColour PhysicalForkCodeCut
open PhysicalForkCodeEuler PhysicalForkCodeFold PhysicalForkCode
open GoertzelV24FaceDualConnectedness GoertzelV24RotationEdgeBridge GoertzelV24TwoEdgeCutMinimality

noncomputable section
attribute [local instance] Classical.propDecidable

section Root

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem V E}

theorem mid_univ : mid RS.endpoints (Finset.univ : Finset E) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro v hv
  obtain ⟨_, ⟨d, _, hd⟩⟩ := (mem_mid_iff RS Finset.univ v).mp hv
  exact hd (Finset.mem_univ _)

instance : IsEmpty (MidVertex RS (Finset.univ : Finset E)) :=
  ⟨fun v => (Finset.eq_empty_iff_forall_notMem.mp mid_univ) v.1 v.2⟩

/-- The labelling of the empty interface of a root. -/
def rootLabel : Fin 0 ≃ MidVertex RS (Finset.univ : Finset E) :=
  Equiv.equivOfIsEmpty _ _

/-- **Root colour adequacy.** -/
theorem root_colour_eq_empty_iff (hC : Cubic3 RS)
    (ℓ : Fin 0 ≃ MidVertex RS (Finset.univ : Finset E)) :
    (encode hC Finset.univ ℓ).colour = ∅ ↔ ¬ RotationSystemTaitColorable RS := by
  change labelledSupport RS.endpoints Finset.univ ℓ = ∅ ↔ _
  rw [← GoertzelV24ForkTaitBridge.support_univ_nonempty_iff_taitColorable,
    Finset.not_nonempty_iff_eq_empty, labelledSupport, Finset.image_eq_empty,
    boundarySupport, Finset.image_eq_empty]

/-- **Root cut adequacy.**  A connected bridgeless map has no nontrivial vertex
set crossed by at most one edge. -/
theorem root_not_hasSmallCut (hC : Cubic3 RS)
    (ℓ : Fin 0 ≃ MidVertex RS (Finset.univ : Finset E))
    (hconn : (rotationPrimalGraph RS).Connected) (hbf : EdgeBridgeFree RS) :
    ¬ HasSmallCut (encode hC Finset.univ ℓ) := by
  rintro ⟨r, hr, hin, hout⟩
  obtain ⟨U, hUmem, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨_, hcross⟩ := Finset.mem_filter.mp hUmem
  simp only [cutRecord, decide_eq_true_eq] at hin hout
  obtain ⟨u, hu⟩ := hin
  obtain ⟨w, hw⟩ := hout
  obtain ⟨_, hwU⟩ := Finset.mem_sdiff.mp hw
  obtain ⟨p⟩ := hconn.preconnected u w
  obtain ⟨dd, _, hx, hy⟩ := p.exists_boundary_dart {v | v ∈ U} hu hwU
  obtain ⟨d, hdx, hdy⟩ := dd.adj
  obtain ⟨q⟩ := hbf d
  obtain ⟨dd', _, hx', hy'⟩ := q.exists_boundary_dart {v | v ∈ U}
    (show RS.vertOf d ∈ U by rw [hdx]; exact hx) (show RS.vertOf (RS.alpha d) ∉ U by rw [hdy]; exact hy)
  obtain ⟨d', hd'e, hd'x, hd'y⟩ := dd'.adj
  have hcard : 1 < cross RS Finset.univ U := by
    rw [cross, Finset.one_lt_card]
    refine ⟨d, ?_, d', ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by rw [hdx]; exact hx, by rw [hdy]; exact hy⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by rw [hd'x]; exact hx', by rw [hd'y]; exact hy'⟩
    · intro h; exact hd'e (by rw [h])
  omega

end Root

section Structure

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem V E}

theorem endpoints_cubic (hCubic : RS.IsCubic) :
    ∀ v : V, (Finset.univ.filter fun e => v ∈ RS.endpoints e).card = 3 := by
  intro v
  have hinc : (Finset.univ.filter fun e => v ∈ RS.endpoints e) = RS.incidentEdges v := by
    ext e
    simp [RS.mem_endpoints_iff_mem_incidentEdges]
  rw [hinc]
  exact RS.incidentEdges_card_eq_three_of_isCubic hCubic v

theorem reachable_of_adj_reachable {G H : SimpleGraph V}
    (h : ∀ a b, G.Adj a b → H.Reachable a b) {u v : V} (p : G.Walk u v) : H.Reachable u v := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

/-- Deleting one edge of a connected bridgeless map leaves the remaining edges
connected. -/
theorem shoreConnected_erase (hconn : (rotationPrimalGraph RS).Connected)
    (hbf : EdgeBridgeFree RS) (e0 : E) :
    ShoreConnected RS (Finset.univ.erase e0) := by
  intro u v _ _
  have hle : edgeDeletedPrimalGraph RS e0 ≤ shoreGraph RS (Finset.univ.erase e0) := by
    rintro a b ⟨d, hd, ha, hb⟩
    exact ⟨d, Finset.mem_erase.mpr ⟨hd, Finset.mem_univ _⟩, ha, hb⟩
  obtain ⟨p⟩ := hconn.preconnected u v
  apply reachable_of_adj_reachable _ p
  rintro a b ⟨d, ha, hb⟩
  by_cases hd : RS.edgeOf d = e0
  · have h := hbf d
    rw [hd, ha, hb] at h
    exact h.mono hle
  · exact SimpleGraph.Adj.reachable ⟨d, Finset.mem_erase.mpr ⟨hd, Finset.mem_univ _⟩, ha, hb⟩

theorem card_mid_erase_le (e0 : E) : (mid RS.endpoints (Finset.univ.erase e0)).card ≤ 2 := by
  have hsub : mid RS.endpoints (Finset.univ.erase e0) ⊆ (RS.dartsOn e0).image RS.vertOf := by
    intro v hv
    obtain ⟨_, ⟨d, hdv, hd⟩⟩ := (mem_mid_iff RS _ v).mp hv
    have hde : RS.edgeOf d = e0 := by
      by_contra hne
      exact hd (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)
    exact Finset.mem_image.mpr ⟨d, RS.mem_dartsOn.mpr hde, hdv⟩
  calc (mid RS.endpoints (Finset.univ.erase e0)).card
      ≤ ((RS.dartsOn e0).image RS.vertOf).card := Finset.card_le_card hsub
    _ ≤ (RS.dartsOn e0).card := Finset.card_image_le
    _ = 2 := RS.edge_fiber_two e0

end Structure

section Graph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

open GoertzelV24ConnectedBranchDecompositionForest GoertzelV24DecomposableFiniteBase
open GoertzelV24ConnectedEdgeShoreMajority SimpleGraphDartRotation
open GoertzelV24SphericalReductiveAssembly

theorem mem_endpoints_graph (data : Data G) (e : G.edgeSet) (v : V) :
    v ∈ data.toRotationSystem.endpoints e ↔ v ∈ (e : Sym2 V) := by
  rw [RotationSystem.mem_endpoints_iff]
  constructor
  · rintro ⟨d, hd, rfl⟩
    have hde : (⟨d.edge, d.edge_mem⟩ : G.edgeSet) = e := (RotationSystem.mem_dartsOn _).mp hd
    rw [← hde]
    exact Sym2.mem_mk_left _ _
  · intro hv
    have hadj : G.Adj v (Sym2.Mem.other hv) := by
      rw [← SimpleGraph.mem_edgeSet, Sym2.other_spec hv]
      exact e.2
    let d : data.toRotationSystem.D := (⟨(v, Sym2.Mem.other hv), hadj⟩ : G.Dart)
    refine ⟨d, (RotationSystem.mem_dartsOn _).mpr ?_, rfl⟩
    apply Subtype.ext
    exact Sym2.other_spec hv

theorem edgeShoreMiddleVertices_eq_mid (data : Data G) (S : Finset G.edgeSet) :
    edgeShoreMiddleVertices G S = mid data.toRotationSystem.endpoints S := by
  ext v
  rw [edgeShoreMiddleVertices, GoertzelV24SphereCutMaterial.mem_middleVertices_iff]
  simp only [mid, Finset.mem_filter, Finset.mem_univ, true_and, Finset.Nonempty,
    Finset.mem_compl, mem_endpoints_graph]

theorem shoreConnected_of_edgeShoreConnected (data : Data G) (S : Finset G.edgeSet)
    (h : EdgeShoreConnected G S) : ShoreConnected data.toRotationSystem S := by
  intro u v hu hv
  have hu' : ∃ edge ∈ S, u ∈ (edge : Sym2 V) := by
    obtain ⟨d, hdu, hdS⟩ := mem_touched.mp hu
    exact ⟨_, hdS, (mem_endpoints_graph data _ u).mp
      (RotationSystem.mem_endpoints_iff _ |>.mpr ⟨d, (RotationSystem.mem_dartsOn _).mpr rfl, hdu⟩)⟩
  have hv' : ∃ edge ∈ S, v ∈ (edge : Sym2 V) := by
    obtain ⟨d, hdv, hdS⟩ := mem_touched.mp hv
    exact ⟨_, hdS, (mem_endpoints_graph data _ v).mp
      (RotationSystem.mem_endpoints_iff _ |>.mpr ⟨d, (RotationSystem.mem_dartsOn _).mpr rfl, hdv⟩)⟩
  obtain ⟨p, hp⟩ := h hu' hv'
  clear hu hv hu' hv'
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hadj q ih =>
      have hedge : (⟨s(a, b), hadj⟩ : G.edgeSet) ∈ S :=
        hp ⟨s(a, b), hadj⟩ (by simp)
      have hstep : (shoreGraph data.toRotationSystem S).Adj a b :=
        ⟨⟨(a, b), hadj⟩, hedge, rfl, rfl⟩
      refine hstep.reachable.trans (ih ?_)
      intro edge hedge'
      exact hp edge (by simp [hedge'])

theorem goodTree_of_geometry (data : Data G) (k w : ℕ) :
    ∀ t : EdgeLeafTree G.edgeSet, EveryForkGeometry (G := G) k w t →
      GoodTree (RS := data.toRotationSystem) (max w 2) t
  | .leaf _, _ => trivial
  | .fork l r, h => by
      refine ⟨?_, ?_, goodTree_of_geometry data k w l h.2.1,
        goodTree_of_geometry data k w r h.2.2⟩
      · rw [GoertzelV24ForkFold.computedShore_eq_shore]
        exact shoreConnected_of_edgeShoreConnected data _ h.1.shoreConnected
      · rw [GoertzelV24ForkFold.computedShore_eq_shore, ← edgeShoreMiddleVertices_eq_mid data]
        exact h.1.middleBound.trans (le_max_left _ _)

/-- The complete edge-leaf tree of a rooted connected decomposition. -/
def wholeTree {k w : ℕ} (d : RootedConnectedBranchDecomposition (G := G) k w) :
    EdgeLeafTree G.edgeSet :=
  .fork (.leaf d.rootEdge) (.fork d.left d.right)

theorem wholeTree_nodup {k w : ℕ} (d : RootedConnectedBranchDecomposition (G := G) k w) :
    (wholeTree d).leafList.Nodup := d.leavesNodup

theorem computedShore_wholeTree {k w : ℕ} (d : RootedConnectedBranchDecomposition (G := G) k w) :
    GoertzelV24ForkFold.computedShore
      (EdgeLeafTree.fork (EdgeLeafTree.leaf d.rootEdge) (EdgeLeafTree.fork d.left d.right)) =
        Finset.univ := by
  rw [GoertzelV24ForkFold.computedShore_eq_shore]
  exact d.leavesCover

theorem computedShore_body {k w : ℕ} (d : RootedConnectedBranchDecomposition (G := G) k w) :
    GoertzelV24ForkFold.computedShore (EdgeLeafTree.fork d.left d.right) =
      Finset.univ.erase d.rootEdge := by
  have hcover := d.leavesCover
  have hnodup := d.leavesNodup
  rw [GoertzelV24ForkFold.computedShore_eq_shore]
  ext e
  simp only [EdgeLeafTree.shore, Finset.mem_erase, Finset.mem_univ, and_true, List.mem_toFinset]
  constructor
  · intro he hroot
    subst hroot
    exact (List.nodup_cons.mp hnodup).1 he
  · intro hne
    have : e ∈ (d.rootEdge :: (d.left.leafList ++ d.right.leafList)).toFinset := by
      rw [hcover]; exact Finset.mem_univ _
    rw [List.mem_toFinset, List.mem_cons] at this
    exact this.resolve_left hne

theorem goodTree_wholeTree (data : Data G)
    (mapData : BridgelessSphericalCubicMapData data.toRotationSystem)
    {k w : ℕ} (d : RootedConnectedBranchDecomposition (G := G) k w) :
    GoodTree (RS := data.toRotationSystem) (max w 2) (wholeTree d) := by
  refine ⟨?_, ?_, trivial, ?_, ?_, goodTree_of_geometry data k w _ d.leftGeometry,
    goodTree_of_geometry data k w _ d.rightGeometry⟩
  · rw [computedShore_wholeTree]
    exact shoreConnected_univ mapData.primalConnected
  · rw [computedShore_wholeTree, mid_univ]
    simp
  · rw [computedShore_body]
    exact shoreConnected_erase mapData.primalConnected mapData.edgeBridgeFree _
  · rw [computedShore_body]
    exact (card_mid_erase_le _).trans (le_max_right _ _)

/-- **The finite code, consumed by the decomposable finite base.**  The state is
the root code; the trace uses the supplied decomposition; the reachable set is
the finite set of root codes in the closure at interface bound `max w 2`. -/
def reflection (k w : ℕ) :
    DecomposableBaseReflection.{u, 0} k w (Code 0) where
  Necessary := Rejecting
  reachable := reachableRoots (max w 2)
  trace := fun rotation mapData _ _ =>
    encode (cubic3_of rotation.toRotationSystem mapData.spherical.cubic
      mapData.vertexRotationCyclic) Finset.univ rootLabel
  trace_mem_reachable := by
    intro V _ _ G _ rotation mapData _ decomposition
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact reach_encode_of_eq mapData.spherical mapData.primalConnected
      mapData.vertexRotationCyclic (endpoints_cubic mapData.spherical.cubic)
      (le_max_right w 2) (wholeTree decomposition) (wholeTree_nodup decomposition)
      (goodTree_wholeTree rotation mapData decomposition)
      (computedShore_wholeTree decomposition) rootLabel
  necessary_of_not_colorable := by
    intro V _ _ G _ rotation mapData _ _ hnot
    exact ⟨(root_colour_eq_empty_iff _ rootLabel).mpr hnot,
      root_not_hasSmallCut _ rootLabel mapData.primalConnected mapData.edgeBridgeFree⟩

/-- **The finite base from the audit.**  An empty rejecting part of the finite
closure at interface bound `max w 2` discharges the restricted base obligation. -/
theorem taitBaseVerifiedOnDecomposable_of_audit (k w : ℕ) (haudit : Audit (max w 2)) :
    TaitBaseVerifiedOnDecomposable.{u} k w :=
  (reflection.{u} k w).taitBaseVerifiedOnDecomposable_of_filter_eq_empty
    ((audit_iff_filter_eq_empty _).mp haudit)

/-- **No least counterexample, from the width supply and the audit.**  The
supplied decomposition places the least counterexample's root code in the
closure, and noncolourability makes it rejecting.  No vertex bound is used:
the finite base is the closure itself, not an enumeration of small maps. -/
theorem noGraphBackedVertexMinimalTaitCounterexample_of_supply_and_audit (k w : ℕ)
    (supply : ConnectedDecompositionSupply.{u} k w) (haudit : Audit (max w 2)) :
    GoertzelV24SphericalMinimalCounterexampleSelection.NoGraphBackedVertexMinimalTaitCounterexample.{u} := by
  intro V _ _ G _ rotation minimal
  have mapData := minimal.toBridgelessSphericalCubicMapData
  have hreach := reach_encode_of_eq mapData.spherical mapData.primalConnected
    mapData.vertexRotationCyclic (endpoints_cubic mapData.spherical.cubic)
    (le_max_right w 2) (wholeTree (supply rotation minimal)) (wholeTree_nodup _)
    (goodTree_wholeTree rotation mapData _) (computedShore_wholeTree _) rootLabel
  exact haudit _ hreach
    ⟨(root_colour_eq_empty_iff _ rootLabel).mpr minimal.notColorable,
      root_not_hasSmallCut _ rootLabel mapData.primalConnected mapData.edgeBridgeFree⟩

/-- The combinatorial Four-Colour statement from a connected width supply and
the audit. -/
theorem combinatorialFourColorStatement_of_supply_and_audit (k w : ℕ)
    (supply : ConnectedDecompositionSupply.{u} k w) (haudit : Audit (max w 2)) :
    GoertzelV24SphericalGraphPresentation.CombinatorialFourColorStatement.{u} :=
  (GoertzelV24SphericalGraphPresentation.combinatorialFourColorStatement_iff_spherical.{u}).2
    (GoertzelV24SphericalMinimalCounterexampleSelection.sphericalFourColorStatement_of_no_minimal
      (noGraphBackedVertexMinimalTaitCounterexample_of_supply_and_audit k w supply haudit))

/-- **Consumer-facing assembly.**  A raw width-`w` decomposition supply and an
audited finite closure at interface bound `max w 2` give the combinatorial
Four-Colour statement.  The width-preserving connectedization is the checked
one; the vertex-count bound of the pumping argument is not used. -/
theorem combinatorialFourColorStatement_of_raw_and_audit (w : ℕ)
    (raw : RawBranchDecompositionSupply.{u} w) (haudit : Audit (max w 2)) :
    GoertzelV24SphericalGraphPresentation.CombinatorialFourColorStatement.{u} :=
  combinatorialFourColorStatement_of_supply_and_audit w w
    (connectedDecompositionSupply_of_raw w raw) haudit

end Graph

end

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeBase

