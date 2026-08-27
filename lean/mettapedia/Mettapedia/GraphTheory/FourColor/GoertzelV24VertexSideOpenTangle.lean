import Mettapedia.GraphTheory.FourColor.GoertzelV24CompositeSeamCubic
import Mettapedia.GraphTheory.FourColor.GoertzelV24CompositeStructuralData

/-!
# Local structure of a literal vertex-side open tangle

Opening a rotation system along a vertex predicate changes only whether a
retained dart is classified as internal or boundary.  It does not change the
darts based at a retained vertex, and its rotation is the ambient rotation
restricted to those darts and conjugated across that partition.

Consequently cubicity and cyclic vertex rotations pass literally from the
ambient rotation system to `OpenTangleData.ofVertexSide`.  This is the local,
non-topological part of the sphere-cut-to-open-tangle adapter.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24VertexSideOpenTangle

open GoertzelV24CompositeSeamCubic
open GoertzelV24CompositeSeamMultigraph
open GoertzelV24BoundaryEssentialGluing
open GoertzelV24FaceDualConnectedness
open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24MultigraphTransport
open GoertzelV24CompositeStructuralData
open GoertzelV24CompositeSphericity
open GoertzelV24SeamExchange
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24RetainedRegionBoundaryOrder

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- Darts based at one retained vertex, before and after the literal
internal/boundary partition. -/
def ambientDartsAtEquivOpenDartsAt
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep) (v : {vertex : V // keep vertex}) :
    {d : RS.D // d ∈ RS.dartsAt v.1} ≃
      {d : InternalDart RS keep ⊕ BoundaryDart RS keep //
        d ∈ openDartsAt (ofVertexSide RS keep outer) v} where
  toFun d := by
    let retained : RetainedDart RS keep := ⟨d.1, by
      have hdv := (Finset.mem_filter.1 d.2).2
      rw [hdv]
      exact v.2⟩
    refine ⟨retainedDartEquivInternalSumBoundary RS keep retained, ?_⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    change openTangleVertOf
        (fun internal : InternalDart RS keep => vertexSideVertex RS keep internal.1)
        (fun boundary : BoundaryDart RS keep => vertexSideVertex RS keep boundary.1)
        (retainedDartEquivInternalSumBoundary RS keep retained) = v
    rw [openTangleVertOf_vertexSide_partition_symm, Equiv.symm_apply_apply]
    apply Subtype.ext
    exact (Finset.mem_filter.1 d.2).2
  invFun d := by
    let retained :=
      (retainedDartEquivInternalSumBoundary RS keep).symm d.1
    refine ⟨retained.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    have hdv := (Finset.mem_filter.1 d.2).2
    change openTangleVertOf
        (fun internal : InternalDart RS keep => vertexSideVertex RS keep internal.1)
        (fun boundary : BoundaryDart RS keep => vertexSideVertex RS keep boundary.1)
        d.1 = v at hdv
    rw [openTangleVertOf_vertexSide_partition_symm] at hdv
    exact congrArg Subtype.val hdv
  left_inv d := by
    apply Subtype.ext
    simp
  right_inv d := by
    apply Subtype.ext
    simp

/-- The literal vertex-side partition preserves the number of darts at every
retained vertex. -/
theorem card_openDartsAt_ofVertexSide
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep) (v : {vertex : V // keep vertex}) :
    (openDartsAt (ofVertexSide RS keep outer) v).card =
      (RS.dartsAt v.1).card := by
  have hcard := Fintype.card_congr
    (ambientDartsAtEquivOpenDartsAt RS keep outer v)
  simpa using hcard.symm

/-- Cubicity passes to a literal vertex shore, with cut half-edges counted as
the boundary darts that replaced their old edge mates. -/
theorem openIsCubic_ofVertexSide
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep) (hcubic : RS.IsCubic) :
    OpenIsCubic (ofVertexSide RS keep outer) := by
  intro v
  rw [card_openDartsAt_ofVertexSide]
  exact hcubic v.1

/-- A cyclic ambient vertex rotation remains cyclic after restricting to one
literal vertex shore. -/
theorem openRotationCyclic_ofVertexSide
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep) (hrotation : VertexRotationCyclic RS) :
    OpenRotationCyclic (ofVertexSide RS keep outer) := by
  intro d d' hvertex
  let partition := retainedDartEquivInternalSumBoundary RS keep
  have hunderlying :
      RS.vertOf (partition.symm d).1 = RS.vertOf (partition.symm d').1 := by
    have hleft := openTangleVertOf_vertexSide_partition_symm RS keep d
    have hright := openTangleVertOf_vertexSide_partition_symm RS keep d'
    exact congrArg Subtype.val (hleft.symm.trans (hvertex.trans hright))
  have hambient := hrotation (partition.symm d).1 (partition.symm d').1 hunderlying
  have hretained :
      (retainedRho RS keep).SameCycle (partition.symm d) (partition.symm d') :=
    Equiv.Perm.SameCycle.subtypePerm hambient
  simpa [partition, ofVertexSide] using
    (sameCycle_conjEquiv partition (retainedRho RS keep) hretained)

/-- One adjacency inside the induced vertex shore is one step of the literal
open side multigraph. -/
theorem sideStep_of_induce_adj
    (RS : RotationSystem V E) (keep : V → Prop)
  (outer : RetainedDart RS keep)
    {u v : {vertex : V // keep vertex}}
    (hadj : ((rotationPrimalGraph RS).induce {vertex | keep vertex}).Adj u v) :
    (sideMultigraph (ofVertexSide RS keep outer)).Step u v := by
  change (rotationPrimalGraph RS).Adj u.1 v.1 at hadj
  have hambient : (rotationPrimalGraph RS).Adj u.1 v.1 := hadj
  obtain ⟨dart, hsource, htarget⟩ :=
    (rotationPrimalGraph_adj_iff RS).1 hambient
  let retained : RetainedDart RS keep := ⟨dart, hsource ▸ u.2⟩
  let internal : InternalDart RS keep := ⟨retained, htarget ▸ v.2⟩
  refine ⟨sideEdgeOf (ofVertexSide RS keep outer) internal, by simp,
    ?_⟩
  rcases sideMultigraph_ends (ofVertexSide RS keep outer) internal with
      hends | hends
  · exact Or.inl ⟨by
      rw [hends.1]
      apply Subtype.ext
      exact hsource, by
      rw [hends.2]
      apply Subtype.ext
      exact htarget⟩
  · exact Or.inr ⟨by
      rw [hends.1]
      apply Subtype.ext
      exact htarget, by
      rw [hends.2]
      apply Subtype.ext
      exact hsource⟩

/-- Connectedness of the induced ambient vertex shore is exactly enough for
connectedness of the interior-edge multigraph used by seam gluing. -/
theorem sideMultigraph_connected_of_induce_connected
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (hconnected :
      ((rotationPrimalGraph RS).induce {vertex | keep vertex}).Connected) :
    (sideMultigraph (ofVertexSide RS keep outer)).Connected := by
  intro u v
  obtain ⟨path⟩ := hconnected u v
  induction path with
  | nil => exact Relation.ReflTransGen.refl
  | cons hadj _ ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single
          (sideStep_of_induce_adj RS keep outer hadj)) ih

/-- The complete boundary-dart carrier is exactly a saturated port interface
for the ambient multigraph: every edge leaving the vertex side contributes
its retained orientation as a boundary port. -/
theorem boundaryDarts_saturate_toMultigraph
    (RS : RotationSystem V E) (keep : V → Prop) :
    ∀ e : E, ¬ Internal (toMultigraph RS) keep e →
      (keep ((toMultigraph RS).fst e) →
          ∃ p : BoundaryDart RS keep,
            RS.vertOf p.1.1 = (toMultigraph RS).fst e) ∧
        (keep ((toMultigraph RS).snd e) →
          ∃ p : BoundaryDart RS keep,
            RS.vertOf p.1.1 = (toMultigraph RS).snd e) := by
  intro e hnot
  constructor
  · intro hfst
    have hsnd : ¬ keep ((toMultigraph RS).snd e) := by
      intro hsnd
      exact hnot ⟨hfst, hsnd⟩
    let port : BoundaryDart RS keep :=
      ⟨⟨someDart RS e, hfst⟩, hsnd⟩
    exact ⟨port, rfl⟩
  · intro hsnd
    have hfst : ¬ keep ((toMultigraph RS).fst e) := by
      intro hfst
      exact hnot ⟨hfst, hsnd⟩
    let port : BoundaryDart RS keep :=
      ⟨⟨RS.alpha (someDart RS e), hsnd⟩, by
        rw [RS.alpha_involutive]
        exact hfst⟩
    exact ⟨port, rfl⟩

/-! ## Exact edge presentation of the vertex side -/

/-- An ambient edge known to lie wholly in the side, presented as an internal
dart of the literal open tangle. -/
def internalDartOfAmbientInternalEdge
    (RS : RotationSystem V E) (keep : V → Prop)
    (edge : {e : E // Internal (toMultigraph RS) keep e}) :
    InternalDart RS keep :=
  ⟨⟨someDart RS edge.1, edge.2.1⟩, edge.2.2⟩

/-- Send an internal ambient edge to its involution orbit in the open side. -/
def ambientInternalEdgeToSideEdge
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (edge : {e : E // Internal (toMultigraph RS) keep e}) :
    SideEdge (ofVertexSide RS keep outer) :=
  sideEdgeOf (ofVertexSide RS keep outer)
    (internalDartOfAmbientInternalEdge RS keep edge)

/-- Read the old ambient edge identifier carried by one open-side edge
orbit. -/
def sideEdgeToAmbientInternalEdge
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (edge : SideEdge (ofVertexSide RS keep outer)) :
    {e : E // Internal (toMultigraph RS) keep e} := by
  let dart := edge.2.choose
  refine ⟨RS.edgeOf dart.1.1, ?_⟩
  change
    keep (RS.vertOf (someDart RS (RS.edgeOf dart.1.1))) ∧
      keep (RS.vertOf (RS.alpha (someDart RS (RS.edgeOf dart.1.1))))
  rcases eq_someDart_or RS (RS.edgeOf dart.1.1) rfl with h | h
  · constructor
    · have hd : keep (RS.vertOf dart.1.1) := dart.1.2
      rw [h] at hd
      exact hd
    · have hd : keep (RS.vertOf (RS.alpha dart.1.1)) := dart.2
      rw [h] at hd
      exact hd
  · constructor
    · have hd : keep (RS.vertOf (RS.alpha dart.1.1)) := dart.2
      rw [h, RS.alpha_involutive] at hd
      exact hd
    · have hd : keep (RS.vertOf dart.1.1) := dart.1.2
      rw [h] at hd
      exact hd

@[simp]
theorem sideEdgeToAmbientInternalEdge_val
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (edge : SideEdge (ofVertexSide RS keep outer)) :
    (sideEdgeToAmbientInternalEdge RS keep outer edge).1 =
      RS.edgeOf edge.2.choose.1.1 :=
  rfl

/-- The old edge identifier of an open-side orbit generated by an internal
ambient edge is the original identifier. -/
theorem sideEdgeToAmbientInternalEdge_toSideEdge
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (edge : {e : E // Internal (toMultigraph RS) keep e}) :
    sideEdgeToAmbientInternalEdge RS keep outer
        (ambientInternalEdgeToSideEdge RS keep outer edge) = edge := by
  apply Subtype.ext
  change RS.edgeOf
      ((ambientInternalEdgeToSideEdge RS keep outer edge).2.choose).1.1 =
    edge.1
  rcases choose_sideEdgeOf (ofVertexSide RS keep outer)
      (internalDartOfAmbientInternalEdge RS keep edge) with h | h
  · calc
      RS.edgeOf
          ((ambientInternalEdgeToSideEdge RS keep outer edge).2.choose).1.1 =
          RS.edgeOf (internalDartOfAmbientInternalEdge RS keep edge).1.1 :=
        congrArg (fun d : InternalDart RS keep => RS.edgeOf d.1.1) h
      _ = edge.1 := edgeOf_someDart RS edge.1
  · calc
      RS.edgeOf
          ((ambientInternalEdgeToSideEdge RS keep outer edge).2.choose).1.1 =
          RS.edgeOf
            ((ofVertexSide RS keep outer).interiorAlpha
              (internalDartOfAmbientInternalEdge RS keep edge)).1.1 :=
        congrArg (fun d : InternalDart RS keep => RS.edgeOf d.1.1) h
      _ = RS.edgeOf
            (RS.alpha
              (internalDartOfAmbientInternalEdge RS keep edge).1.1) := by
        exact congrArg RS.edgeOf
          (internalAlpha_val RS keep
            (internalDartOfAmbientInternalEdge RS keep edge))
      _ = RS.edgeOf (internalDartOfAmbientInternalEdge RS keep edge).1.1 :=
        RS.edge_alpha _
      _ = edge.1 := edgeOf_someDart RS edge.1

/-- Reconstructing an open-side orbit from its old ambient edge identifier
returns the same orbit. -/
theorem ambientInternalEdgeToSideEdge_toAmbient
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (edge : SideEdge (ofVertexSide RS keep outer)) :
    ambientInternalEdgeToSideEdge RS keep outer
        (sideEdgeToAmbientInternalEdge RS keep outer edge) = edge := by
  let dart := edge.2.choose
  have hedge : sideEdgeOf (ofVertexSide RS keep outer) dart = edge :=
    sideEdgeOf_choose (ofVertexSide RS keep outer) edge
  change sideEdgeOf (ofVertexSide RS keep outer)
      (internalDartOfAmbientInternalEdge RS keep
        (sideEdgeToAmbientInternalEdge RS keep outer edge)) = edge
  rcases eq_someDart_or RS (RS.edgeOf dart.1.1) rfl with h | h
  · have hi :
        internalDartOfAmbientInternalEdge RS keep
            (sideEdgeToAmbientInternalEdge RS keep outer edge) = dart := by
      apply Subtype.ext
      apply Subtype.ext
      change someDart RS
          (sideEdgeToAmbientInternalEdge RS keep outer edge).1 = dart.1.1
      rw [sideEdgeToAmbientInternalEdge_val]
      exact h.symm
    rw [hi]
    exact hedge
  · have hs : someDart RS (RS.edgeOf dart.1.1) = RS.alpha dart.1.1 := by
      have ha := congrArg RS.alpha h
      rw [RS.alpha_involutive] at ha
      exact ha.symm
    have hi :
        internalDartOfAmbientInternalEdge RS keep
            (sideEdgeToAmbientInternalEdge RS keep outer edge) =
          (ofVertexSide RS keep outer).interiorAlpha dart := by
      apply Subtype.ext
      apply Subtype.ext
      change someDart RS
          (sideEdgeToAmbientInternalEdge RS keep outer edge).1 =
        RS.alpha dart.1.1
      rw [sideEdgeToAmbientInternalEdge_val]
      exact hs
    rw [hi, sideEdgeOf_alpha]
    exact hedge

/-- Internal ambient edge identifiers and literal open-side edge orbits are
equivalent. -/
def ambientInternalEdgeEquivSideEdge
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep) :
    {e : E // Internal (toMultigraph RS) keep e} ≃
      SideEdge (ofVertexSide RS keep outer) where
  toFun := ambientInternalEdgeToSideEdge RS keep outer
  invFun := sideEdgeToAmbientInternalEdge RS keep outer
  left_inv := sideEdgeToAmbientInternalEdge_toSideEdge RS keep outer
  right_inv := ambientInternalEdgeToSideEdge_toAmbient RS keep outer

/-- The induced ambient side and the literal open-tangle side are the same
multigraph, up to the harmless choice of a representative dart for each edge
orbit. -/
def inducedSideIsoSideMultigraph
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep) :
    GoertzelV24MultigraphTransport.Iso
      (inducedSideMultigraph (toMultigraph RS) keep)
      (sideMultigraph (ofVertexSide RS keep outer)) where
  vert := Equiv.refl _
  edge := ambientInternalEdgeEquivSideEdge RS keep outer
  ends := by
    intro edge
    have hends := sideMultigraph_ends (ofVertexSide RS keep outer)
      (internalDartOfAmbientInternalEdge RS keep edge)
    rcases hends with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
    · left
      constructor
      · exact hfst
      · exact hsnd
    · right
      constructor
      · exact hfst
      · exact hsnd

/-- A literal vertex shore of a bridgeless ambient rotation system is
boundary-essential for gluing.  This is the exact carrier-level adapter: the
ports are all and only the retained orientations of cut edges, while the old
side edges are the involution orbits of the retained internal darts. -/
theorem boundaryEssential_ofVertexSide
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (hbridgeless : (toMultigraph RS).Bridgeless) :
    BoundaryEssential
      (sideMultigraph (ofVertexSide RS keep outer))
      (ofVertexSide RS keep outer).boundaryVert := by
  have hinduced :
      BoundaryEssential
        (inducedSideMultigraph (toMultigraph RS) keep)
        (fun p : BoundaryDart RS keep =>
          ⟨RS.vertOf p.1.1, p.1.2⟩) :=
    inducedSide_boundaryEssential_of_saturated
      (G := toMultigraph RS) (side := keep)
      (fun p : BoundaryDart RS keep => RS.vertOf p.1.1)
      (fun p => p.1.2) hbridgeless
      (boundaryDarts_saturate_toMultigraph RS keep)
  exact
    (inducedSideIsoSideMultigraph RS keep outer).boundaryEssential_of
      (Equiv.refl (BoundaryDart RS keep))
      (fun p : BoundaryDart RS keep => ⟨RS.vertOf p.1.1, p.1.2⟩)
      (ofVertexSide RS keep outer).boundaryVert
      (fun _ => rfl) hinduced

/-! ## The canonical cap order -/

/-- The hub order which closes each boundary-return arc back to the port at
which it began. -/
def canonicalHubRotation (RS : RotationSystem V E) (keep : V → Prop) :
    Equiv.Perm (BoundaryDart RS keep) :=
  (retainedRegionBoundarySuccessor RS keep)⁻¹

/-- Opposite first-return orders on two shores are exactly the
orientation-reversing equation required by the seam face-count theorem. -/
theorem orientationReversing_canonicalHubRotation_of_opposite
    (RS : RotationSystem V E) (keepL keepR : V → Prop)
    (matching : BoundaryDart RS keepL ≃ BoundaryDart RS keepR)
    (hopposite : ∀ b : BoundaryDart RS keepL,
      retainedRegionBoundarySuccessor RS keepR
          (matching (retainedRegionBoundarySuccessor RS keepL b)) =
        matching b) :
    OrientationReversing matching
      (canonicalHubRotation RS keepL)
      (canonicalHubRotation RS keepR) := by
  intro b
  change
    (retainedRegionBoundarySuccessor RS keepR)⁻¹ (matching b) =
      matching (retainedRegionBoundarySuccessor RS keepL b)
  exact (Equiv.symm_apply_eq
    (retainedRegionBoundarySuccessor RS keepR)).2 (hopposite b).symm

/-! ## Two literal shores feed the structural seam theorem -/

/-- The already-proved composite structural theorem specialized to two
literal vertex shores of one ambient rotation system.  All non-topological
side obligations are discharged here; the remaining cap hypotheses say
exactly that the two shores are discs with oppositely oriented boundary
orders. -/
def bridgelessSphericalCubicMapData_ofVertexSides
    (RS : RotationSystem V E) (keepL keepR : V → Prop)
    (outerL : RetainedDart RS keepL) (outerR : RetainedDart RS keepR)
    (matching : BoundaryDart RS keepL ≃ BoundaryDart RS keepR)
    (ρL : Equiv.Perm (BoundaryDart RS keepL))
    (ρR : Equiv.Perm (BoundaryDart RS keepR))
    (hconnectedL :
      ((rotationPrimalGraph RS).induce {vertex | keepL vertex}).Connected)
    (hconnectedR :
      ((rotationPrimalGraph RS).induce {vertex | keepR vertex}).Connected)
    (hbridgeless : (toMultigraph RS).Bridgeless)
    (p₀ q₀ : BoundaryDart RS keepL) (hpq : p₀ ≠ q₀)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (hFacesL : HubFacesDistinct (ofVertexSide RS keepL outerL) ρL)
    (hFacesR : HubFacesDistinct (ofVertexSide RS keepR outerR) ρR)
    (hrev : OrientationReversing matching ρL ρR)
    (hSphereL : ClosedSideSpherical (ofVertexSide RS keepL outerL) ρL)
    (hSphereR : ClosedSideSpherical (ofVertexSide RS keepR outerR) ρR) :
    BridgelessSphericalCubicMapData
      ((ofVertexSide RS keepL outerL).composeRotationSystem
        (ofVertexSide RS keepR outerR) matching) := by
  letI : Nonempty {vertex : V // keepL vertex} :=
    ⟨vertexSideVertex RS keepL outerL⟩
  have hEssentialR₀ :=
    boundaryEssential_ofVertexSide RS keepR outerR hbridgeless
  have hEssentialR :
      BoundaryEssential
        (sideMultigraph (ofVertexSide RS keepR outerR))
        (fun port : BoundaryDart RS keepL =>
          (ofVertexSide RS keepR outerR).boundaryVert (matching port)) := by
    intro edge hbridge
    obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hEssentialR₀ edge hbridge
    constructor
    · refine ⟨matching.symm p, ?_⟩
      simpa using hp
    · refine ⟨matching.symm q, ?_⟩
      simpa using hq
  exact
    bridgelessSphericalCubicMapData_composeRotationSystem
      (ofVertexSide RS keepL outerL) (ofVertexSide RS keepR outerR)
      matching ρL ρR
      (sideMultigraph_connected_of_induce_connected RS keepL outerL hconnectedL)
      (sideMultigraph_connected_of_induce_connected RS keepR outerR hconnectedR)
      (boundaryEssential_ofVertexSide RS keepL outerL hbridgeless)
      hEssentialR p₀ q₀ hpq
      (openIsCubic_ofVertexSide RS keepL outerL hcubic)
      (openIsCubic_ofVertexSide RS keepR outerR hcubic)
      (openRotationCyclic_ofVertexSide RS keepL outerL hrotation)
      (openRotationCyclic_ofVertexSide RS keepR outerR hrotation)
      hFacesL hFacesR hrev hSphereL hSphereR

end

end GoertzelV24VertexSideOpenTangle

end Mettapedia.GraphTheory.FourColor
