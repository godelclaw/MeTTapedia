import Mettapedia.GraphTheory.FourColor.GoertzelV24ComplementaryShoreBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationDartColoring

/-!
# Complementary vertex shores reassemble the ambient Tait problem

Cutting a rotation system along a literal vertex predicate partitions its
darts into two open tangles.  If the two exposed boundary carriers are sewn
back together by the old edge involution, the resulting dart system is merely
a relabeling of the ambient one.  This file records the exact coloring
consequence needed by physical equal-state replacement.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24VertexSideReassembly

open GoertzelV24ComplementaryShoreBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationDartColoring
open GoertzelV24TwoEdgeCutMinimality

noncomputable section

universe uV₁ uE₁ uV₂ uE₂

variable {V₁ : Type uV₁} {E₁ : Type uE₁}
  {V₂ : Type uV₂} {E₂ : Type uE₂}
  [Fintype V₁] [DecidableEq V₁] [Fintype E₁] [DecidableEq E₁]
  [Fintype V₂] [DecidableEq V₂] [Fintype E₂] [DecidableEq E₂]

/-! ## Generic transport through exact dart and vertex relabelings -/

/-- An equivalence of dart carriers which intertwines `alpha` and preserves
the displayed vertex partition transports a Tait coloring.  No compatibility
with `rho`, faces, or the distinguished outer dart is needed: Tait colorability
depends only on edge pairs and their common vertices. -/
theorem rotationSystemTaitColorable_of_dartEquiv
    (source : RotationSystem V₁ E₁) (target : RotationSystem V₂ E₂)
    (dartEquiv : source.D ≃ target.D) (vertexEquiv : V₁ ≃ V₂)
    (hAlpha : ∀ dart,
      dartEquiv (source.alpha dart) = target.alpha (dartEquiv dart))
    (hVert : ∀ dart,
      vertexEquiv (source.vertOf dart) = target.vertOf (dartEquiv dart))
    (hColorable : RotationSystemTaitColorable source) :
    RotationSystemTaitColorable target := by
  rcases hColorable with ⟨coloring, hTait⟩
  let dartColor : target.D → Color := fun dart =>
    coloring (source.edgeOf (dartEquiv.symm dart))
  have hinverseAlpha (dart : target.D) :
      dartEquiv.symm (target.alpha dart) =
        source.alpha (dartEquiv.symm dart) := by
    apply dartEquiv.injective
    rw [dartEquiv.apply_symm_apply, hAlpha, dartEquiv.apply_symm_apply]
  have hinverseVert (dart : target.D) :
      source.vertOf (dartEquiv.symm dart) =
        vertexEquiv.symm (target.vertOf dart) := by
    apply vertexEquiv.injective
    rw [vertexEquiv.apply_symm_apply, hVert, dartEquiv.apply_symm_apply]
  have hDartAlpha (dart : target.D) :
      dartColor (target.alpha dart) = dartColor dart := by
    dsimp [dartColor]
    rw [hinverseAlpha, source.edge_alpha]
  have hDartProper : ∀ {left right : target.D},
      target.vertOf left = target.vertOf right → left ≠ right →
        dartColor left ≠ dartColor right := by
    intro left right hvertex hdarts
    let sourceLeft := dartEquiv.symm left
    let sourceRight := dartEquiv.symm right
    have hsourceVertex : source.vertOf sourceLeft = source.vertOf sourceRight := by
      rw [hinverseVert, hinverseVert, hvertex]
    have hsourceDarts : sourceLeft ≠ sourceRight := by
      intro h
      apply hdarts
      simpa [sourceLeft, sourceRight] using congrArg dartEquiv h
    have hedges : source.edgeOf sourceLeft ≠ source.edgeOf sourceRight := by
      intro hedge
      apply hsourceDarts
      apply source.edgeOf_injOn_dartsAt (source.vertOf sourceLeft)
      · simp [RotationSystem.dartsAt]
      · simp [RotationSystem.dartsAt, hsourceVertex]
      · exact hedge
    change coloring (source.edgeOf sourceLeft) ≠
      coloring (source.edgeOf sourceRight)
    apply coloring.valid
    exact (source.edgeAdjacencyGraph_adj_iff).2
      ⟨hedges, source.vertOf sourceLeft,
        (source.mem_endpoints_iff).2
          ⟨sourceLeft, (source.mem_dartsOn).2 rfl, rfl⟩,
        (source.mem_endpoints_iff).2
          ⟨sourceRight, (source.mem_dartsOn).2 rfl,
            hsourceVertex.symm⟩⟩
  refine ⟨edgeColoringOfDartColor target dartColor hDartAlpha hDartProper, ?_⟩
  apply edgeColoringOfDartColor_isTait
  intro dart
  exact hTait _

/-- Exact dart and vertex relabelings preserve Tait colorability in both
directions. -/
theorem rotationSystemTaitColorable_iff_of_dartEquiv
    (source : RotationSystem V₁ E₁) (target : RotationSystem V₂ E₂)
    (dartEquiv : source.D ≃ target.D) (vertexEquiv : V₁ ≃ V₂)
    (hAlpha : ∀ dart,
      dartEquiv (source.alpha dart) = target.alpha (dartEquiv dart))
    (hVert : ∀ dart,
      vertexEquiv (source.vertOf dart) = target.vertOf (dartEquiv dart)) :
    RotationSystemTaitColorable source ↔
      RotationSystemTaitColorable target := by
  constructor
  · exact rotationSystemTaitColorable_of_dartEquiv source target
      dartEquiv vertexEquiv hAlpha hVert
  · apply rotationSystemTaitColorable_of_dartEquiv target source
      dartEquiv.symm vertexEquiv.symm
    · intro dart
      apply dartEquiv.injective
      rw [dartEquiv.apply_symm_apply, hAlpha, dartEquiv.apply_symm_apply]
    · intro dart
      apply vertexEquiv.injective
      rw [vertexEquiv.apply_symm_apply, hVert, dartEquiv.apply_symm_apply]

/-! ## Canonical reassembly of complementary literal shores -/

universe uV uE

variable {V : Type uV} {E : Type uE}
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The result of opening the two complementary vertex shores and sewing
their exposed darts by ambient `alpha`. -/
abbrev complementaryCompositeRS
    (RS : RotationSystem V E) (deleted : Finset V)
    (outerRetained : RetainedDart RS (deletedRegionKeep deleted))
    (outerDeleted : RetainedDart RS (deletedSideKeep deleted)) :=
  OpenTangleData.composeRotationSystem
    (ofVertexSide RS (deletedRegionKeep deleted) outerRetained)
    (ofVertexSide RS (deletedSideKeep deleted) outerDeleted)
    (complementBoundaryAlphaEquiv RS deleted)

/-- The tagged vertex carriers of two complementary literal shores are just
the ambient vertex carrier split by membership in the retained shore. -/
def complementaryVertexEquiv (deleted : Finset V) :
    {vertex : V // deletedRegionKeep deleted vertex} ⊕
        {vertex : V // deletedSideKeep deleted vertex} ≃ V := by
  classical
  exact Equiv.sumCompl (deletedRegionKeep deleted)

/-- Undo, in order, the composite reassociation, the internal/boundary
partitions on the two shores, and the complementary vertex-side partition of
the ambient dart carrier. -/
def complementaryDartEquiv
    (RS : RotationSystem V E) (deleted : Finset V)
    (outerRetained : RetainedDart RS (deletedRegionKeep deleted))
    (outerDeleted : RetainedDart RS (deletedSideKeep deleted)) :
    (complementaryCompositeRS RS deleted outerRetained outerDeleted).D ≃ RS.D :=
  by
  classical
  exact (composeDartEquiv
      (I := InternalDart RS (deletedRegionKeep deleted))
      (L := BoundaryDart RS (deletedRegionKeep deleted))
      (J := InternalDart RS (deletedSideKeep deleted))
      (R := BoundaryDart RS (deletedSideKeep deleted))).symm |>.trans
    ((Equiv.sumCongr
      (retainedDartEquivInternalSumBoundary RS
        (deletedRegionKeep deleted)).symm
      (retainedDartEquivInternalSumBoundary RS
        (deletedSideKeep deleted)).symm).trans
      (Equiv.sumCompl
        (fun dart : RS.D => deletedRegionKeep deleted (RS.vertOf dart))))

@[simp]
theorem complementaryDartEquiv_left_interior
    (RS : RotationSystem V E) (deleted : Finset V)
    (outerRetained : RetainedDart RS (deletedRegionKeep deleted))
    (outerDeleted : RetainedDart RS (deletedSideKeep deleted))
    (dart : InternalDart RS (deletedRegionKeep deleted)) :
    complementaryDartEquiv RS deleted outerRetained outerDeleted
        (Sum.inl (Sum.inl dart)) = dart.1.1 :=
  rfl

@[simp]
theorem complementaryDartEquiv_right_interior
    (RS : RotationSystem V E) (deleted : Finset V)
    (outerRetained : RetainedDart RS (deletedRegionKeep deleted))
    (outerDeleted : RetainedDart RS (deletedSideKeep deleted))
    (dart : InternalDart RS (deletedSideKeep deleted)) :
    complementaryDartEquiv RS deleted outerRetained outerDeleted
        (Sum.inl (Sum.inr dart)) = dart.1.1 :=
  rfl

@[simp]
theorem complementaryDartEquiv_left_boundary
    (RS : RotationSystem V E) (deleted : Finset V)
    (outerRetained : RetainedDart RS (deletedRegionKeep deleted))
    (outerDeleted : RetainedDart RS (deletedSideKeep deleted))
    (dart : BoundaryDart RS (deletedRegionKeep deleted)) :
    complementaryDartEquiv RS deleted outerRetained outerDeleted
        (Sum.inr (Sum.inl dart)) = dart.1.1 :=
  rfl

@[simp]
theorem complementaryDartEquiv_right_boundary
    (RS : RotationSystem V E) (deleted : Finset V)
    (outerRetained : RetainedDart RS (deletedRegionKeep deleted))
    (outerDeleted : RetainedDart RS (deletedSideKeep deleted))
    (dart : BoundaryDart RS (deletedSideKeep deleted)) :
    complementaryDartEquiv RS deleted outerRetained outerDeleted
        (Sum.inr (Sum.inr dart)) = dart.1.1 :=
  rfl

/-- The inverse boundary matching is also ambient `alpha` on underlying
darts.  This is the right-to-left orientation of the seam law. -/
@[simp]
theorem complementBoundaryAlphaEquiv_symm_val
    (RS : RotationSystem V E) (deleted : Finset V)
    (dart : BoundaryDart RS (deletedSideKeep deleted)) :
    ((complementBoundaryAlphaEquiv RS deleted).symm dart).1.1 =
      RS.alpha dart.1.1 := by
  let left := (complementBoundaryAlphaEquiv RS deleted).symm dart
  have hforward := complementBoundaryAlphaEquiv_val RS deleted left
  have hvalue : dart.1.1 = RS.alpha left.1.1 := by
    simpa [left] using hforward
  calc
    left.1.1 = RS.alpha (RS.alpha left.1.1) :=
      (RS.alpha_involutive left.1.1).symm
    _ = RS.alpha dart.1.1 := (congrArg RS.alpha hvalue).symm

/-- The canonical dart reassembly intertwines the sewn edge involution with
the ambient edge involution, including both orientations of every seam edge. -/
theorem complementaryDartEquiv_alpha
    (RS : RotationSystem V E) (deleted : Finset V)
    (outerRetained : RetainedDart RS (deletedRegionKeep deleted))
    (outerDeleted : RetainedDart RS (deletedSideKeep deleted))
    (dart : (complementaryCompositeRS RS deleted
      outerRetained outerDeleted).D) :
    complementaryDartEquiv RS deleted outerRetained outerDeleted
        ((complementaryCompositeRS RS deleted
          outerRetained outerDeleted).alpha dart) =
      RS.alpha
        (complementaryDartEquiv RS deleted
          outerRetained outerDeleted dart) := by
  rcases dart with (left | right) | (left | right)
  · rfl
  · rfl
  · exact complementBoundaryAlphaEquiv_val RS deleted left
  · exact complementBoundaryAlphaEquiv_symm_val RS deleted right

/-- The vertex reassembly reads the same ambient base vertex as the dart
reassembly. -/
theorem complementaryDartEquiv_vertOf
    (RS : RotationSystem V E) (deleted : Finset V)
    (outerRetained : RetainedDart RS (deletedRegionKeep deleted))
    (outerDeleted : RetainedDart RS (deletedSideKeep deleted))
    (dart : (complementaryCompositeRS RS deleted
      outerRetained outerDeleted).D) :
    complementaryVertexEquiv deleted
        ((complementaryCompositeRS RS deleted
          outerRetained outerDeleted).vertOf dart) =
      RS.vertOf
        (complementaryDartEquiv RS deleted
          outerRetained outerDeleted dart) := by
  rcases dart with (left | right) | (left | right) <;> rfl

/-- **Complementary-shore Tait reassembly.**  Cutting the ambient rotation
system into its two literal vertex shores and sewing their boundary darts by
ambient `alpha` neither creates nor destroys a Tait coloring. -/
theorem rotationSystemTaitColorable_complementaryComposite_iff
    (RS : RotationSystem V E) (deleted : Finset V)
    (outerRetained : RetainedDart RS (deletedRegionKeep deleted))
    (outerDeleted : RetainedDart RS (deletedSideKeep deleted)) :
    RotationSystemTaitColorable
        (complementaryCompositeRS RS deleted outerRetained outerDeleted) ↔
      RotationSystemTaitColorable RS :=
  rotationSystemTaitColorable_iff_of_dartEquiv
    (complementaryCompositeRS RS deleted outerRetained outerDeleted) RS
    (complementaryDartEquiv RS deleted outerRetained outerDeleted)
    (complementaryVertexEquiv deleted)
    (complementaryDartEquiv_alpha RS deleted outerRetained outerDeleted)
    (complementaryDartEquiv_vertOf RS deleted outerRetained outerDeleted)

/-! ## The same reassembly with the two sides displayed in the opposite order -/

/-- The outside shore may be displayed first, as required by the normalized
replacement theorem.  Its matching is the inverse ambient boundary flip. -/
abbrev swappedComplementaryCompositeRS
    (RS : RotationSystem V E) (deleted : Finset V)
    (outerDeleted : RetainedDart RS (deletedSideKeep deleted))
    (outerRetained : RetainedDart RS (deletedRegionKeep deleted)) :=
  OpenTangleData.composeRotationSystem
    (ofVertexSide RS (deletedSideKeep deleted) outerDeleted)
    (ofVertexSide RS (deletedRegionKeep deleted) outerRetained)
    (complementBoundaryAlphaEquiv RS deleted).symm

/-- Swap the two interior summands and the two seam summands. -/
def swappedCompositeDartEquiv
    (RS : RotationSystem V E) (deleted : Finset V)
    (outerDeleted : RetainedDart RS (deletedSideKeep deleted))
    (outerRetained : RetainedDart RS (deletedRegionKeep deleted)) :
    (swappedComplementaryCompositeRS RS deleted
      outerDeleted outerRetained).D ≃
      (complementaryCompositeRS RS deleted
        outerRetained outerDeleted).D :=
  Equiv.sumCongr
    (Equiv.sumComm
      (InternalDart RS (deletedSideKeep deleted))
      (InternalDart RS (deletedRegionKeep deleted)))
    (Equiv.sumComm
      (BoundaryDart RS (deletedSideKeep deleted))
      (BoundaryDart RS (deletedRegionKeep deleted)))

theorem swappedCompositeDartEquiv_alpha
    (RS : RotationSystem V E) (deleted : Finset V)
    (outerDeleted : RetainedDart RS (deletedSideKeep deleted))
    (outerRetained : RetainedDart RS (deletedRegionKeep deleted))
    (dart : (swappedComplementaryCompositeRS RS deleted
      outerDeleted outerRetained).D) :
    swappedCompositeDartEquiv RS deleted outerDeleted outerRetained
        ((swappedComplementaryCompositeRS RS deleted
          outerDeleted outerRetained).alpha dart) =
      (complementaryCompositeRS RS deleted
        outerRetained outerDeleted).alpha
        (swappedCompositeDartEquiv RS deleted
          outerDeleted outerRetained dart) := by
  rcases dart with (left | right) | (left | right) <;> rfl

theorem swappedCompositeDartEquiv_vertOf
    (RS : RotationSystem V E) (deleted : Finset V)
    (outerDeleted : RetainedDart RS (deletedSideKeep deleted))
    (outerRetained : RetainedDart RS (deletedRegionKeep deleted))
    (dart : (swappedComplementaryCompositeRS RS deleted
      outerDeleted outerRetained).D) :
    (Equiv.sumComm
      {vertex : V // deletedSideKeep deleted vertex}
      {vertex : V // deletedRegionKeep deleted vertex})
        ((swappedComplementaryCompositeRS RS deleted
          outerDeleted outerRetained).vertOf dart) =
      (complementaryCompositeRS RS deleted
        outerRetained outerDeleted).vertOf
        (swappedCompositeDartEquiv RS deleted
          outerDeleted outerRetained dart) := by
  rcases dart with (left | right) | (left | right) <;> rfl

/-- Reassembly is independent of which complementary shore is displayed as
the left input of the seam composite. -/
theorem rotationSystemTaitColorable_swappedComplementaryComposite_iff
    (RS : RotationSystem V E) (deleted : Finset V)
    (outerDeleted : RetainedDart RS (deletedSideKeep deleted))
    (outerRetained : RetainedDart RS (deletedRegionKeep deleted)) :
    RotationSystemTaitColorable
        (swappedComplementaryCompositeRS RS deleted
          outerDeleted outerRetained) ↔
      RotationSystemTaitColorable RS :=
  (rotationSystemTaitColorable_iff_of_dartEquiv
    (swappedComplementaryCompositeRS RS deleted
      outerDeleted outerRetained)
    (complementaryCompositeRS RS deleted outerRetained outerDeleted)
    (swappedCompositeDartEquiv RS deleted outerDeleted outerRetained)
    (Equiv.sumComm
      {vertex : V // deletedSideKeep deleted vertex}
      {vertex : V // deletedRegionKeep deleted vertex})
    (swappedCompositeDartEquiv_alpha RS deleted outerDeleted outerRetained)
    (swappedCompositeDartEquiv_vertOf RS deleted outerDeleted outerRetained)).trans
      (rotationSystemTaitColorable_complementaryComposite_iff
        RS deleted outerRetained outerDeleted)

end

end GoertzelV24VertexSideReassembly

end Mettapedia.GraphTheory.FourColor
