import Mettapedia.GraphTheory.FourColor.GoertzelV24ThreeEdgeCutCap

/-!
# The Y-cap of one side of an exact five-edge cut

One shore of an exact cyclic five-edge cut cannot be closed by a seam
pairing alone: five is odd.  The Y-cap closes it by joining the first two
exposed half-edges to each other (the seam) and attaching the remaining
three to one new cubic vertex (the star).  The boundary words this
replacement supports are exactly the `Y`-cap support of the word-level
five-cut heart: the seam forces equal colours at its two ports, and
properness at the star vertex forces a Tait triple on the rest.

This file constructs the capped rotation system.  The construction mirrors
the three-edge-cut star cap: the two seam darts join the interior carrier,
where their mutual swap extends the interior involution, and the star runs
through the matched-seam constructor.  The single degeneracy hypothesis is
that the two seam half-edges are based at distinct retained vertices —
otherwise the seam would be a loop.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor
open GoertzelV24RetainedVertexRotationSplice

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The swap of two seam darts indexed by `Bool`. -/
def seamPairSwap : Equiv.Perm Bool :=
  ⟨Bool.not, Bool.not, by decide, by decide⟩

/-- One rooted side of an exact ordered five-edge cut, with the data needed
to close it by a seam on the first two cut edges and a star on the last
three.  The endpoint condition excludes a loop seam. -/
structure FiveEdgeCutYCapData (RS : RotationSystem V E) where
  side : Finset V
  crossing : Fin 5 → E
  crossing_injective : Function.Injective crossing
  boundary_eq : RS.vertexSideEdgeBoundary side = orderedCut crossing
  anchor : RS.D
  anchor_mem : RS.vertOf anchor ∈ side
  seamEndpointsDistinct :
    ∀ (left right : BoundaryDart RS (fun vertex => vertex ∈ side)),
      RS.edgeOf left.1.1 = crossing 0 →
      RS.edgeOf right.1.1 = crossing 1 →
      RS.vertOf left.1.1 ≠ RS.vertOf right.1.1

namespace FiveEdgeCutYCapData

variable {RS : RotationSystem V E} (data : FiveEdgeCutYCapData RS)

/-- The retained vertex predicate. -/
def keep (vertex : V) : Prop :=
  vertex ∈ data.side

instance keepDecidablePred : DecidablePred data.keep :=
  fun vertex => Finset.decidableMem vertex data.side

theorem crossing_mem_boundary (step : Fin 5) :
    data.crossing step ∈ RS.vertexSideEdgeBoundary data.side := by
  rw [data.boundary_eq]
  exact Finset.mem_image.mpr ⟨step, Finset.mem_univ step, rfl⟩

/-- Every ordered cut edge has a unique outward-oriented retained dart. -/
theorem crosses (step : Fin 5) :
    ∃ dart : RS.D,
      RS.edgeOf dart = data.crossing step ∧
      data.keep (RS.vertOf dart) ∧
      ¬ data.keep (RS.vertOf (RS.alpha dart)) := by
  let dart := RS.boundaryDartOfCrossingEdge data.side
    (data.crossing step) (data.crossing_mem_boundary step)
  refine ⟨dart.1.1, ?_, ?_, ?_⟩
  · exact RS.boundaryDartOfCrossingEdge_edgeOf data.side
      (data.crossing step) (data.crossing_mem_boundary step)
  · exact dart.1.2
  · exact dart.2

/-- Exactness of the five-edge boundary covers every exposed retained
dart. -/
theorem boundaryCover (dart : BoundaryDart RS data.keep) :
    RS.edgeOf dart.1.1 ∈ orderedCut data.crossing := by
  have hmem :=
    RS.boundaryDart_edge_mem_vertexSideEdgeBoundary data.side dart
  rw [data.boundary_eq] at hmem
  exact hmem

/-- Forgetting the redundant support proof is an equivalence because the
ordered five-edge cut is the complete boundary. -/
def supportedBoundaryDartEquiv :
    BoundaryDartOn RS data.keep (orderedCut data.crossing) ≃
      BoundaryDart RS data.keep where
  toFun dart := dart.1
  invFun dart := ⟨dart, data.boundaryCover dart⟩
  left_inv dart := by
    apply Subtype.ext
    rfl
  right_inv _ := rfl

/-- The ordered cut positions enumerate all outward boundary darts. -/
def crossingBoundaryDartEquiv :
    Fin 5 ≃ BoundaryDart RS data.keep :=
  (orderedBoundaryDartEquiv RS data.keep data.crossing data.crosses
      data.crossing_injective).trans data.supportedBoundaryDartEquiv

@[simp]
theorem crossingBoundaryDartEquiv_edgeOf (step : Fin 5) :
    RS.edgeOf (data.crossingBoundaryDartEquiv step).1.1 =
      data.crossing step := by
  change RS.edgeOf
      (orderedBoundaryDart RS data.keep data.crossing data.crosses step).1.1.1 =
    data.crossing step
  exact orderedBoundaryDart_edgeOf RS data.keep data.crossing
    data.crosses step

/-! ## Positions: seam pair and star triple -/

/-- Boundary positions split into the two seam positions and the three star
positions. -/
def positionSplit : Fin 5 ≃ Bool ⊕ Fin 3 where
  toFun step :=
    if h0 : step = 0 then Sum.inl false
    else if h1 : step = 1 then Sum.inl true
    else Sum.inr ⟨step - 2, by omega⟩
  invFun part :=
    match part with
    | Sum.inl false => 0
    | Sum.inl true => 1
    | Sum.inr k => ⟨k + 2, by omega⟩
  left_inv := by decide
  right_inv := by decide

/-- The seam boundary darts, indexed by `Bool`. -/
def seamDart (part : Bool) : BoundaryDart RS data.keep :=
  data.crossingBoundaryDartEquiv (positionSplit.symm (Sum.inl part))

/-- The star boundary darts, indexed by `Fin 3`. -/
def starDart (spoke : Fin 3) : BoundaryDart RS data.keep :=
  data.crossingBoundaryDartEquiv (positionSplit.symm (Sum.inr spoke))

theorem seamDart_edgeOf_false :
    RS.edgeOf (data.seamDart false).1.1 = data.crossing 0 :=
  data.crossingBoundaryDartEquiv_edgeOf 0

theorem seamDart_edgeOf_true :
    RS.edgeOf (data.seamDart true).1.1 = data.crossing 1 :=
  data.crossingBoundaryDartEquiv_edgeOf 1

/-- The two seam darts are based at distinct retained vertices. -/
theorem seamDart_vert_ne :
    RS.vertOf (data.seamDart false).1.1 ≠
      RS.vertOf (data.seamDart true).1.1 :=
  data.seamEndpointsDistinct (data.seamDart false) (data.seamDart true)
    data.seamDart_edgeOf_false data.seamDart_edgeOf_true

/-! ## The cap carrier -/

/-- The honest vertex carrier of the capped side: all retained vertices and
one new star vertex. -/
abbrev CapVertex := RetainedVertex data.keep ⊕ Unit

/-- The interior dart carrier: old internal darts together with the two
seam darts, which are joined to each other. -/
abbrev SeamInterior := InternalDart RS data.keep ⊕ Bool

/-- The dart carrier of the capped side: interior darts, the three star
boundary darts, and the three new star spokes. -/
abbrev CapDart := MatchedSeam.Dart data.SeamInterior (Fin 3) (Fin 3)

/-- The boundary darts, reindexed as seam pair plus star triple. -/
def boundarySplitEquiv : BoundaryDart RS data.keep ≃ Bool ⊕ Fin 3 :=
  data.crossingBoundaryDartEquiv.symm.trans positionSplit

/-- Reassociate the cap dart carrier into old retained darts plus three new
star spokes. -/
def capDartEquiv : data.CapDart ≃ RetainedDart RS data.keep ⊕ Fin 3 :=
  (Equiv.sumAssoc data.SeamInterior (Fin 3) (Fin 3)).symm.trans
    (Equiv.sumCongr
      ((Equiv.sumAssoc (InternalDart RS data.keep) Bool (Fin 3)).trans
        ((Equiv.sumCongr (Equiv.refl (InternalDart RS data.keep))
            data.boundarySplitEquiv.symm).trans
          (retainedDartEquivInternalSumBoundary RS data.keep).symm))
      (Equiv.refl (Fin 3)))

/-- Vertex projection after reassociating the cap darts. -/
def capTargetVert : RetainedDart RS data.keep ⊕ Fin 3 → data.CapVertex
  | Sum.inl dart => Sum.inl ⟨RS.vertOf dart.1, dart.2⟩
  | Sum.inr _ => Sum.inr ()

/-- The old retained rotation together with a cyclic rotation at the new
star vertex. -/
def capTargetRho : Equiv.Perm (RetainedDart RS data.keep ⊕ Fin 3) :=
  Equiv.sumCongr (retainedRho RS data.keep) (finRotate 3)

/-- Transport the old-plus-star vertex rotation to the cap dart carrier. -/
def capRho : Equiv.Perm data.CapDart :=
  data.capDartEquiv.trans
    (data.capTargetRho.trans data.capDartEquiv.symm)

/-- Matched-seam data for the Y-cap: the seam pair swaps inside the
interior carrier, the star triple matches the three new spokes. -/
def capSeamData :
    MatchedSeam.Data data.CapVertex data.SeamInterior (Fin 3) (Fin 3) where
  interiorVert dart :=
    match dart with
    | Sum.inl internal => Sum.inl ⟨RS.vertOf internal.1.1, internal.1.2⟩
    | Sum.inr part =>
        Sum.inl ⟨RS.vertOf (data.seamDart part).1.1, (data.seamDart part).1.2⟩
  leftVert spoke :=
    Sum.inl ⟨RS.vertOf (data.starDart spoke).1.1, (data.starDart spoke).1.2⟩
  rightVert _ := Sum.inr ()
  interiorAlpha :=
    Equiv.sumCongr (internalAlpha RS data.keep) seamPairSwap
  matching := Equiv.refl (Fin 3)
  rho := data.capRho
  outer := data.capDartEquiv.symm
    (Sum.inl ⟨data.anchor, data.anchor_mem⟩)

@[simp]
theorem capDartEquiv_interior (dart : InternalDart RS data.keep) :
    data.capDartEquiv (Sum.inl (Sum.inl dart)) = Sum.inl dart.1 :=
  rfl

@[simp]
theorem capDartEquiv_seam (part : Bool) :
    data.capDartEquiv (Sum.inl (Sum.inr part)) =
      Sum.inl (data.seamDart part).1 := by
  simp [capDartEquiv, boundarySplitEquiv, seamDart,
    retainedDartEquivInternalSumBoundary]

@[simp]
theorem capDartEquiv_star (spoke : Fin 3) :
    data.capDartEquiv (Sum.inr (Sum.inl spoke)) =
      Sum.inl (data.starDart spoke).1 := by
  simp [capDartEquiv, boundarySplitEquiv, starDart,
    retainedDartEquivInternalSumBoundary]

@[simp]
theorem capDartEquiv_cap (spoke : Fin 3) :
    data.capDartEquiv (Sum.inr (Sum.inr spoke)) = Sum.inr spoke :=
  rfl

theorem capSeamData_vertOf_eq_capTargetVert (dart : data.CapDart) :
    data.capSeamData.vertOf dart =
      data.capTargetVert (data.capDartEquiv dart) := by
  rcases dart with interior | boundaryOrCap
  · rcases interior with internal | part
    · rfl
    · rw [data.capDartEquiv_seam]
      rfl
  · rcases boundaryOrCap with spoke | cap
    · rw [data.capDartEquiv_star]
      rfl
    · rfl

/-- The transported vertex rotation preserves the vertex projection. -/
theorem capTargetRho_vert (dart : RetainedDart RS data.keep ⊕ Fin 3) :
    data.capTargetVert (data.capTargetRho dart) =
      data.capTargetVert dart := by
  rcases dart with retained | cap
  · apply congrArg Sum.inl
    apply Subtype.ext
    exact RS.vert_rho retained.1
  · rfl

@[simp]
theorem capDartEquiv_capRho (dart : data.CapDart) :
    data.capDartEquiv (data.capRho dart) =
      data.capTargetRho (data.capDartEquiv dart) := by
  simp [capRho]

theorem capSeamData_rho_vert (dart : data.CapDart) :
    data.capSeamData.vertOf (data.capSeamData.rho dart) =
      data.capSeamData.vertOf dart := by
  rw [data.capSeamData_vertOf_eq_capTargetVert,
    data.capSeamData_vertOf_eq_capTargetVert]
  change data.capTargetVert (data.capDartEquiv (data.capRho dart)) =
    data.capTargetVert (data.capDartEquiv dart)
  rw [data.capDartEquiv_capRho, data.capTargetRho_vert]

/-- Rewired dart system obtained by seaming the first two exposed
half-edges to each other and starring the remaining three into one new
cubic vertex. -/
def capRewiredDartSystem :
    RewiredDartSystem data.CapVertex data.CapDart :=
  data.capSeamData.toRewiredDartSystem
    (by
      rintro (internal | part)
      · simp only [capSeamData, Equiv.sumCongr_apply, Sum.map_inl]
        rw [internalAlpha_involutive]
      · cases part <;>
          simp [capSeamData, seamPairSwap])
    (by
      rintro (internal | part)
      · simp only [capSeamData, Equiv.sumCongr_apply, Sum.map_inl, ne_eq,
          Sum.inl.injEq]
        exact internalAlpha_fixfree RS data.keep internal
      · cases part <;>
          simp [capSeamData, seamPairSwap])
    data.capSeamData_rho_vert
    (by
      rintro (internal | part)
      · simp only [capSeamData, Equiv.sumCongr_apply, Sum.map_inl, ne_eq,
          Sum.inl.injEq, Subtype.mk.injEq]
        exact fun h => RS.no_self_loops internal.1.1 (by
          simpa [internalAlpha] using h)
      · cases part
        · simp only [capSeamData, Equiv.sumCongr_apply, Sum.map_inr, ne_eq,
            Sum.inl.injEq, Subtype.mk.injEq, seamPairSwap,
            Equiv.coe_fn_mk, Bool.not_false]
          exact data.seamDart_vert_ne
        · simp only [capSeamData, Equiv.sumCongr_apply, Sum.map_inr, ne_eq,
            Sum.inl.injEq, Subtype.mk.injEq, seamPairSwap,
            Equiv.coe_fn_mk, Bool.not_true]
          exact fun h => data.seamDart_vert_ne h.symm)
    (by
      intro spoke
      simp [capSeamData])

/-- The rotation system of the Y-capped side. -/
def capRotationSystem :
    RotationSystem data.CapVertex data.capRewiredDartSystem.Edge :=
  data.capRewiredDartSystem.toRotationSystem

/-- The new dart based at the star vertex in a given spoke position. -/
def capDart (spoke : Fin 3) : data.CapDart :=
  Sum.inr (Sum.inr spoke)

/-- Embed an old retained dart in the cap dart carrier. -/
def capDartOfRetained (dart : RetainedDart RS data.keep) : data.CapDart :=
  data.capDartEquiv.symm (Sum.inl dart)

theorem capDartOfRetained_injective :
    Function.Injective data.capDartOfRetained := by
  intro left right hdarts
  unfold capDartOfRetained at hdarts
  exact Sum.inl.inj (data.capDartEquiv.symm.injective hdarts)

@[simp]
theorem capDartEquiv_capDartOfRetained
    (dart : RetainedDart RS data.keep) :
    data.capDartEquiv (data.capDartOfRetained dart) = Sum.inl dart :=
  data.capDartEquiv.apply_symm_apply (Sum.inl dart)

@[simp]
theorem capDartEquiv_capDart (spoke : Fin 3) :
    data.capDartEquiv (data.capDart spoke) = Sum.inr spoke :=
  rfl

end FiveEdgeCutYCapData

end

end Mettapedia.GraphTheory.FourColor
