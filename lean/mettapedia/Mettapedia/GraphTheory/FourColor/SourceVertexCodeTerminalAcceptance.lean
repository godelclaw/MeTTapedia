import Mettapedia.GraphTheory.FourColor.SourceVertexCodeBounds
import Mettapedia.GraphTheory.FourColor.VertexCodeTerminalAcceptance
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationDartColoring
import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSideOpenTangle

/-!
# Terminal acceptance of a complete source sweep

For a sweep containing every source vertex, the decoded closed tangle has
exactly the ambient darts.  This file transports Tait colourings across that
equivalence.  Together with the already-proved source planarity and
connectivity the result identifies terminal colour acceptance with the actual
rotation-system proposition.  Structural bridgelessness is kept as a separate
lemma below; no failure of the executable terminal predicate is confused with
non-colourability of a malformed run.
-/

namespace Mettapedia.GraphTheory.FourColor.SourceVertexCodeTerminalAcceptance

open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24FaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24RotationDartColoring
open GoertzelV24CompositeSeamMultigraph
open GoertzelV24MultigraphTransport
open GoertzelV24RotationMultigraphAdapter
open SerialTangleSmallCutTransfer
open TubeSlab.VertexTransfer
open VertexCodeDartGeometry VertexCodeSourceGeometry
open VertexCodeSourceSemantics SourceVertexCodeTrace

noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
variable {RS : RotationSystem.{u,u,u} V E} {inner : V → Prop}
variable {W I : Type*} [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I]
variable {T : TwoSidedOpenTangleData W I (Fin 0) (Fin 0)}
variable {mi : Fin 0 ≃ BoundaryDart RS inner} (M : Model T mi)

/-- When the swept side contains every vertex, forgetting the retention proof
is an equivalence onto all ambient darts. -/
def retainedFullEquiv (hcover : ∀ v, inner v) : RetainedDart RS inner ≃ RS.D where
  toFun d := d.1
  invFun d := ⟨d, hcover _⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

/-- The literal darts of a closed decoded trace are exactly the source darts. -/
def fullDartEquiv (hcover : ∀ v, inner v) :
    I ⊕ (Fin 0 ⊕ Fin 0) ≃ RS.D :=
  compact.symm.trans (M.dart.trans (retainedFullEquiv hcover))

@[simp]
theorem fullDartEquiv_internal (hcover : ∀ v, inner v) (i : I) :
    fullDartEquiv M hcover (.inl i) = (M.dart (.inl i)).1 := rfl

theorem fullDartEquiv_vert (hcover : ∀ v, inner v)
    (d : I ⊕ (Fin 0 ⊕ Fin 0)) :
    (M.vertex (T.vertOf d)).1 = RS.vertOf (fullDartEquiv M hcover d) := by
  obtain i | (e | e) := d
  · exact M.vert (.inl i)
  · exact e.elim0
  · exact e.elim0

theorem fullDartEquiv_alpha (hcover : ∀ v, inner v) (i : I) :
    fullDartEquiv M hcover (.inl (T.interiorAlpha i)) =
      RS.alpha (fullDartEquiv M hcover (.inl i)) :=
  M.mate i

/-! ## The full decoded side is the source multigraph -/

variable (outer : RetainedDart RS inner)

theorem internalEquiv_symm_alpha (j : InternalDart RS inner) :
    (internalEquiv M).symm (internalAlpha RS inner j) =
      T.interiorAlpha ((internalEquiv M).symm j) := by
  apply (internalEquiv M).injective
  rw [internalEquiv_alpha, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

def internalSym2Equiv : Sym2 I ≃ Sym2 (InternalDart RS inner) :=
  Equiv.ofBijective (Sym2.map (internalEquiv M))
    ⟨Sym2.map.injective (internalEquiv M).injective, by
      intro edge
      induction edge using Sym2.inductionOn with
      | _ left right =>
          exact ⟨s((internalEquiv M).symm left,
            (internalEquiv M).symm right), by simp⟩⟩

def sourceSideEdgeEquiv :
    SideEdge (asOpen T) ≃
      SideEdge (OpenTangleData.ofVertexSide RS inner outer) :=
  (internalSym2Equiv M).subtypeEquiv (fun edge => by
    constructor
    · rintro ⟨d, rfl⟩
      refine ⟨internalEquiv M d, ?_⟩
      change Sym2.map (internalEquiv M) s(d, T.interiorAlpha d) =
        s(internalEquiv M d,
          (OpenTangleData.ofVertexSide RS inner outer).interiorAlpha
            (internalEquiv M d))
      rw [Sym2.map_mk, internalEquiv_alpha]
      rfl
    · rintro ⟨j, hj⟩
      obtain ⟨d, rfl⟩ := (internalEquiv M).surjective j
      refine ⟨d, ?_⟩
      apply (internalSym2Equiv M).injective
      exact hj.trans (by
        change s(internalEquiv M d,
            (OpenTangleData.ofVertexSide RS inner outer).interiorAlpha
              (internalEquiv M d)) =
          Sym2.map (internalEquiv M) s(d, T.interiorAlpha d)
        rw [Sym2.map_mk, internalEquiv_alpha]
        rfl))

@[simp]
theorem sourceSideEdgeEquiv_val (e : SideEdge (asOpen T)) :
    (sourceSideEdgeEquiv M outer e).1 = Sym2.map (internalEquiv M) e.1 :=
  rfl

/-- The model's vertex and dart equivalences induce a genuine multigraph
isomorphism, including edge identity rather than reachability alone. -/
def sourceSideIso : Iso
    (sideMultigraph (asOpen T))
    (sideMultigraph (OpenTangleData.ofVertexSide RS inner outer)) where
  vert := M.vertex
  edge := sourceSideEdgeEquiv M outer
  ends := by
    intro e
    let d := e.2.choose
    have hs := sideMultigraph_ends (asOpen T) d
    have ht := sideMultigraph_ends
      (OpenTangleData.ofVertexSide RS inner outer) (internalEquiv M d)
    have hedge : sourceSideEdgeEquiv M outer e =
        sideEdgeOf _ (internalEquiv M d) := by
      apply Subtype.ext
      rw [sourceSideEdgeEquiv_val]
      rw [← sideEdgeOf_choose (asOpen T) e]
      change Sym2.map (internalEquiv M) s(d, T.interiorAlpha d) = _
      rw [Sym2.map_mk, internalEquiv_alpha]
      rfl
    rw [hedge]
    rw [sideEdgeOf_choose (asOpen T) e] at hs
    have hv₁ := internal_vertex M outer d
    have hv₂ := internal_vertex M outer (T.interiorAlpha d)
    rw [internalEquiv_alpha] at hv₂
    rcases hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩ <;>
      rcases ht with ⟨ht1, ht2⟩ | ⟨ht1, ht2⟩
    · exact Or.inl ⟨ht1.trans (hv₁.symm.trans (congrArg M.vertex hs1.symm)),
        ht2.trans (hv₂.symm.trans (congrArg M.vertex hs2.symm))⟩
    · exact Or.inr ⟨ht1.trans (hv₂.symm.trans (congrArg M.vertex hs2.symm)),
        ht2.trans (hv₁.symm.trans (congrArg M.vertex hs1.symm))⟩
    · exact Or.inr ⟨ht1.trans (hv₁.symm.trans (congrArg M.vertex hs2.symm)),
        ht2.trans (hv₂.symm.trans (congrArg M.vertex hs1.symm))⟩
    · exact Or.inl ⟨ht1.trans (hv₂.symm.trans (congrArg M.vertex hs1.symm)),
        ht2.trans (hv₁.symm.trans (congrArg M.vertex hs2.symm))⟩

/-- Pull an ambient edge colouring back to the literal closed tangle. -/
def tangleColoringOfEdgeColoring (hcover : ∀ v, inner v)
    (C : RS.EdgeColoring Color) : T.Coloring :=
  fun d => C (RS.edgeOf (fullDartEquiv M hcover d))

theorem tangleColoringOfEdgeColoring_isTait (hcover : ∀ v, inner v)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    T.IsTaitColoring (tangleColoringOfEdgeColoring M hcover C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp only [tangleColoringOfEdgeColoring]
    rw [fullDartEquiv_alpha, RS.edge_alpha]
  · intro first second hv hne
    apply C.valid
    apply RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
    · intro hedge
      let d₁ := fullDartEquiv M hcover first
      let d₂ := fullDartEquiv M hcover second
      have hv' : RS.vertOf d₁ = RS.vertOf d₂ := by
        rw [← fullDartEquiv_vert M hcover first,
          ← fullDartEquiv_vert M hcover second, hv]
      rcases RS.edge_fiber_two_cases (d := d₁) (y := d₂) rfl hedge.symm with hs | ha
      · exact hne ((fullDartEquiv M hcover).injective hs.symm)
      · exact RS.no_self_loops d₁ (hv'.trans (congrArg RS.vertOf ha))
    · exact (RS.mem_incidentEdges_iff).2
        ⟨fullDartEquiv M hcover first, rfl,
          (fullDartEquiv_vert M hcover first).symm⟩
    · exact (RS.mem_incidentEdges_iff).2
        ⟨fullDartEquiv M hcover second, rfl,
          (fullDartEquiv_vert M hcover second).symm.trans
            (congrArg (fun w => (M.vertex w).1) hv.symm)⟩
  · intro d
    exact hC _

/-- Push a literal closed-tangle colouring to the ambient dart carrier. -/
def ambientDartColorOfTangle (hcover : ∀ v, inner v)
    (c : T.Coloring) : RS.D → Color :=
  fun d => c ((fullDartEquiv M hcover).symm d)

theorem ambientDartColorOfTangle_alpha (hcover : ∀ v, inner v)
    (c : T.Coloring) (hc : T.IsTaitColoring c) (d : RS.D) :
    ambientDartColorOfTangle M hcover c (RS.alpha d) =
      ambientDartColorOfTangle M hcover c d := by
  change c ((fullDartEquiv M hcover).symm (RS.alpha d)) =
    c ((fullDartEquiv M hcover).symm d)
  let x := (fullDartEquiv M hcover).symm d
  have hx : (fullDartEquiv M hcover).symm d = x := rfl
  rw [hx]
  obtain i | (e | e) := x
  · have hd : fullDartEquiv M hcover (.inl i) = d :=
      by rw [← hx]; exact (fullDartEquiv M hcover).apply_symm_apply d
    have ha : (fullDartEquiv M hcover).symm (RS.alpha d) =
        .inl (T.interiorAlpha i) := by
      apply (fullDartEquiv M hcover).injective
      rw [Equiv.apply_symm_apply, fullDartEquiv_alpha, hd]
    rw [ha]
    exact hc.1 i
  · exact e.elim0
  · exact e.elim0

theorem ambientDartColorOfTangle_proper (hcover : ∀ v, inner v)
    (c : T.Coloring) (hc : T.IsTaitColoring c)
    {left right : RS.D} (hv : RS.vertOf left = RS.vertOf right)
    (hne : left ≠ right) :
    ambientDartColorOfTangle M hcover c left ≠
      ambientDartColorOfTangle M hcover c right := by
  apply hc.2.1
  · apply M.vertex.injective
    apply Subtype.ext
    rw [fullDartEquiv_vert M hcover, fullDartEquiv_vert M hcover,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply, hv]
  · exact fun h => hne ((fullDartEquiv M hcover).symm.injective h)

theorem ambientDartColorOfTangle_nonzero (hcover : ∀ v, inner v)
    (c : T.Coloring) (hc : T.IsTaitColoring c) (d : RS.D) :
    ambientDartColorOfTangle M hcover c d ≠ 0 :=
  hc.2.2 _

/-- Closed decoded Tait colourability is exactly source Tait colourability. -/
theorem tangle_taitColorable_iff (M : Model T mi) (hcover : ∀ v, inner v) :
    (∃ c, T.IsTaitColoring c) ↔ RotationSystemTaitColorable RS := by
  constructor
  · rintro ⟨c, hc⟩
    let dartColor := ambientDartColorOfTangle M hcover c
    let C := edgeColoringOfDartColor RS dartColor
      (ambientDartColorOfTangle_alpha M hcover c hc)
      (ambientDartColorOfTangle_proper M hcover c hc)
    exact ⟨C, edgeColoringOfDartColor_isTait RS dartColor
      (ambientDartColorOfTangle_alpha M hcover c hc)
      (ambientDartColorOfTangle_proper M hcover c hc)
      (ambientDartColorOfTangle_nonzero M hcover c hc)⟩
  · rintro ⟨C, hC⟩
    exact ⟨tangleColoringOfEdgeColoring M hcover C,
      tangleColoringOfEdgeColoring_isTait M hcover C hC⟩

/-- The executable colour clause on the complete source trace says exactly
that the source rotation system is Tait-colourable. -/
theorem encoded_colour_acceptance_iff
    (hc : RS.IsCubic) (hcyc : VertexRotationCyclic RS)
    (order : List V) (hn : order.Nodup) (he : order ≠ [])
    (hcover : ∀ v, TubeSlab.VertexTransfer.visited order v) :
    ExecutableVertexCode.accepts
        (encodeClosed hc hcyc order hn he hcover).trace = true ↔
      RotationSystemTaitColorable RS := by
  rw [ExecutableVertexCode.accepts_exact]
  exact tangle_taitColorable_iff (encodeClosed hc hcyc order hn he hcover).model hcover

/-! ## Structural terminal acceptance -/

/-- A full source side is bridgeless. The ambient bridge-free theorem first
makes the side boundary-essential. Since a full side has no boundary ports,
any alleged bridge would produce an inhabitant of the empty boundary type.
The model isomorphism then transports the conclusion to the decoded trace. -/
theorem model_bridgeless (M : Model T mi) (hcover : ∀ v, inner v)
    (hfree : GoertzelV24RotationEdgeBridge.EdgeBridgeFree RS) :
    (sideMultigraph (asOpen T)).Bridgeless := by
  let outer := M.dart (compact.symm T.outer)
  have hambient : (toMultigraph RS).Bridgeless :=
    (bridgeless_iff_edgeBridgeFree RS).2 hfree
  have hessential := GoertzelV24VertexSideOpenTangle.boundaryEssential_ofVertexSide
    RS inner outer hambient
  have hside :
      (sideMultigraph (OpenTangleData.ofVertexSide RS inner outer)).Bridgeless := by
    intro edge hbridge
    obtain ⟨⟨port, _⟩, _⟩ := hessential edge hbridge
    exact port.2 (hcover _)
  exact (sourceSideIso M outer).symm.bridgeless_of hside

/-- The executable terminal predicate on a complete source sweep is neither
weaker nor stronger than source Tait-colourability. Its structural clauses are
discharged from the source class, independently of any colouring. -/
theorem encoded_terminal_acceptance_iff
    (hclass : BridgelessSphericalCubicMapData RS)
    (order : List V) (hn : order.Nodup) (he : order ≠ [])
    (hcover : ∀ v, TubeSlab.VertexTransfer.visited order v) :
    VertexCodeTerminalAcceptance.Accepts
        (encodeClosed hclass.spherical.cubic hclass.vertexRotationCyclic
          order hn he hcover).trace = true ↔
      RotationSystemTaitColorable RS := by
  let e := encodeClosed hclass.spherical.cubic hclass.vertexRotationCyclic
    order hn he hcover
  change VertexCodeTerminalAcceptance.Accepts e.trace = true ↔ _
  rw [VertexCodeTerminalAcceptance.accepts_iff_planar_colouring]
  have hconnected := SourceVertexCodePlanar.model_connected e.model hcover
    hclass.primalConnected
  have hbridgeless := model_bridgeless e.model hcover hclass.edgeBridgeFree
  have hplanar := SourceVertexCodePlanar.model_planar e.model hclass.spherical
    hclass.primalConnected hclass.vertexRotationCyclic
  have hcolour := tangle_taitColorable_iff e.model hcover
  constructor
  · rintro ⟨_, _, hc⟩
    exact hcolour.mp hc
  · intro hc
    exact ⟨⟨hconnected, hbridgeless⟩, hplanar, hcolour.mpr hc⟩

/-- The source class supplies one viable, bounded, closed trace whose terminal
acceptance is exactly the source colourability proposition. -/
theorem class_terminal_covered
    (hclass : BridgelessSphericalCubicMapData RS) :
    ∃ t : VertexCodeTrace.Trace 0,
      Nonempty (Model t.realize
        (terminalCoordinates (RS := RS) completeOrder visited_complete)) ∧
      VertexCodeLosslessPruning.prefixesViable t = true ∧
      VertexCodeUnboundedMass.Within (3 * Fintype.card V) t ∧
      Fintype.card t.Vertex = Fintype.card V ∧
      (VertexCodeTerminalAcceptance.Accepts t = true ↔
        RotationSystemTaitColorable RS) := by
  have hn : (completeOrder (V := V)).Nodup := Finset.nodup_toList _
  have he : completeOrder (V := V) ≠ [] := by
    intro h
    have hm := (TubeSlab.VertexTransfer.visited_iff_mem _ _).mp
      (visited_complete (RS.vertOf RS.outer))
    rw [h] at hm
    exact List.not_mem_nil hm
  let e := encodeClosed hclass.spherical.cubic hclass.vertexRotationCyclic
    completeOrder hn he visited_complete
  refine ⟨e.trace, ⟨e.model⟩, ?_, ?_, ?_, ?_⟩
  · exact SourceVertexCodePlanar.source_prefixes_viable hclass.spherical
      hclass.primalConnected hclass.vertexRotationCyclic completeOrder hn he
      visited_complete
  · exact SourceVertexCodeBounds.encodeOrder_within_three_mul_vertices
      hclass.spherical.cubic hclass.vertexRotationCyclic completeOrder hn he
      (terminalCoordinates completeOrder visited_complete)
  · exact SourceVertexCodeBounds.model_vertex_card e.model visited_complete
  · exact encoded_terminal_acceptance_iff hclass completeOrder hn he
      visited_complete

/-- Uniform bounded-source package: a source with at most `N` vertices has a
semantics-preserving accepted trace of at most `N` vertices whose every
frontier has width at most `3N`. -/
theorem class_terminal_covered_within_vertex_bound {N : ℕ}
    (hclass : BridgelessSphericalCubicMapData RS)
    (hcard : Fintype.card V ≤ N) :
    ∃ t : VertexCodeTrace.Trace 0,
      Nonempty (Model t.realize
        (terminalCoordinates (RS := RS) completeOrder visited_complete)) ∧
      VertexCodeLosslessPruning.prefixesViable t = true ∧
      VertexCodeUnboundedMass.Within (3 * N) t ∧
      Fintype.card t.Vertex ≤ N ∧
      (VertexCodeTerminalAcceptance.Accepts t = true ↔
        RotationSystemTaitColorable RS) := by
  obtain ⟨t, hmodel, hv, hw, ht, haccept⟩ := class_terminal_covered hclass
  exact ⟨t, hmodel, hv,
    SourceVertexCodeBounds.within_mono hw (Nat.mul_le_mul_left 3 hcard),
    ht.le.trans hcard, haccept⟩

end
end Mettapedia.GraphTheory.FourColor.SourceVertexCodeTerminalAcceptance
