import Mettapedia.GraphTheory.FourColor.GoertzelV24ThreeEdgeCutCap

/-!
# The pentagon cap of one side of an exact five-edge cut

The pentagon cap closes a five-port shore with a cycle of five new cubic
vertices: cap vertex `j` carries its spoke to boundary position `j` and
two cycle darts to its neighbours.  The boundary words this replacement
supports are exactly the pentagon support of the word-level five-cut
heart: words extending across an internal five-cycle.

The ten cycle darts live in the interior carrier of the matched-seam
constructor, paired by the cycle involution `(j, true) ↔ (j+1, false)`;
the five spokes run through the seam matching.  No degeneracy hypothesis
is needed — every new edge joins either two distinct cap vertices or a
cap vertex to a retained vertex.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor
open GoertzelV24RetainedVertexRotationSplice

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The pairing of the ten pentagon cycle darts: the outgoing dart of cap
vertex `j` meets the incoming dart of cap vertex `j + 1`. -/
def pentagonCyclePairing : Equiv.Perm (Fin 5 × Bool) where
  toFun dart :=
    match dart with
    | (j, false) => (j - 1, true)
    | (j, true) => (j + 1, false)
  invFun dart :=
    match dart with
    | (j, false) => (j - 1, true)
    | (j, true) => (j + 1, false)
  left_inv := by decide
  right_inv := by decide

/-- The rotation at the five new cap vertices: incoming cycle dart, spoke,
outgoing cycle dart. -/
def pentagonRho : Equiv.Perm ((Fin 5 × Bool) ⊕ Fin 5) where
  toFun dart :=
    match dart with
    | Sum.inl (j, false) => Sum.inr j
    | Sum.inl (j, true) => Sum.inl (j, false)
    | Sum.inr j => Sum.inl (j, true)
  invFun dart :=
    match dart with
    | Sum.inl (j, false) => Sum.inl (j, true)
    | Sum.inl (j, true) => Sum.inr j
    | Sum.inr j => Sum.inl (j, false)
  left_inv := by decide
  right_inv := by decide

/-- One rooted side of an exact ordered five-edge cut, ready for the
pentagon cap. -/
structure FiveEdgeCutPentagonCapData (RS : RotationSystem V E) where
  side : Finset V
  crossing : Fin 5 → E
  crossing_injective : Function.Injective crossing
  boundary_eq : RS.vertexSideEdgeBoundary side = orderedCut crossing
  anchor : RS.D
  anchor_mem : RS.vertOf anchor ∈ side

namespace FiveEdgeCutPentagonCapData

variable {RS : RotationSystem V E} (data : FiveEdgeCutPentagonCapData RS)

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

/-! ## The cap carrier -/

/-- The honest vertex carrier of the capped side: all retained vertices and
five new pentagon vertices. -/
abbrev CapVertex := RetainedVertex data.keep ⊕ Fin 5

/-- The interior dart carrier: old internal darts together with the ten
pentagon cycle darts. -/
abbrev PentagonInterior := InternalDart RS data.keep ⊕ (Fin 5 × Bool)

/-- The dart carrier of the capped side. -/
abbrev CapDart := MatchedSeam.Dart data.PentagonInterior (Fin 5) (Fin 5)

/-- Reassociate the cap dart carrier into old retained darts plus the new
pentagon darts. -/
def capDartEquiv :
    data.CapDart ≃ RetainedDart RS data.keep ⊕ ((Fin 5 × Bool) ⊕ Fin 5) :=
  (Equiv.sumAssoc data.PentagonInterior (Fin 5) (Fin 5)).symm.trans
    ((Equiv.sumCongr
        ((Equiv.sumAssoc (InternalDart RS data.keep) (Fin 5 × Bool)
            (Fin 5)).trans
          ((Equiv.sumCongr (Equiv.refl (InternalDart RS data.keep))
              (Equiv.sumComm (Fin 5 × Bool) (Fin 5))).trans
            ((Equiv.sumAssoc (InternalDart RS data.keep) (Fin 5)
                (Fin 5 × Bool)).symm.trans
              (Equiv.sumCongr
                ((Equiv.sumCongr (Equiv.refl (InternalDart RS data.keep))
                    data.crossingBoundaryDartEquiv).trans
                  (retainedDartEquivInternalSumBoundary
                    RS data.keep).symm)
                (Equiv.refl (Fin 5 × Bool))))))
        (Equiv.refl (Fin 5))).trans
      ((Equiv.sumAssoc (RetainedDart RS data.keep) (Fin 5 × Bool)
          (Fin 5))))

/-- Vertex projection after reassociating the cap darts. -/
def capTargetVert :
    RetainedDart RS data.keep ⊕ ((Fin 5 × Bool) ⊕ Fin 5) → data.CapVertex
  | Sum.inl dart => Sum.inl ⟨RS.vertOf dart.1, dart.2⟩
  | Sum.inr (Sum.inl (j, _)) => Sum.inr j
  | Sum.inr (Sum.inr j) => Sum.inr j

/-- The old retained rotation together with the pentagon rotation. -/
def capTargetRho :
    Equiv.Perm (RetainedDart RS data.keep ⊕ ((Fin 5 × Bool) ⊕ Fin 5)) :=
  Equiv.sumCongr (retainedRho RS data.keep) pentagonRho

/-- Transport the vertex rotation to the cap dart carrier. -/
def capRho : Equiv.Perm data.CapDart :=
  data.capDartEquiv.trans
    (data.capTargetRho.trans data.capDartEquiv.symm)

/-- Matched-seam data for the pentagon cap. -/
def capSeamData :
    MatchedSeam.Data data.CapVertex data.PentagonInterior (Fin 5) (Fin 5) where
  interiorVert dart :=
    match dart with
    | Sum.inl internal => Sum.inl ⟨RS.vertOf internal.1.1, internal.1.2⟩
    | Sum.inr (j, _) => Sum.inr j
  leftVert position :=
    Sum.inl
      ⟨RS.vertOf (data.crossingBoundaryDartEquiv position).1.1,
        (data.crossingBoundaryDartEquiv position).1.2⟩
  rightVert j := Sum.inr j
  interiorAlpha :=
    Equiv.sumCongr (internalAlpha RS data.keep) pentagonCyclePairing
  matching := Equiv.refl (Fin 5)
  rho := data.capRho
  outer := data.capDartEquiv.symm
    (Sum.inl ⟨data.anchor, data.anchor_mem⟩)

@[simp]
theorem capDartEquiv_interior (dart : InternalDart RS data.keep) :
    data.capDartEquiv (Sum.inl (Sum.inl dart)) = Sum.inl dart.1 :=
  rfl

@[simp]
theorem capDartEquiv_cycle (dart : Fin 5 × Bool) :
    data.capDartEquiv (Sum.inl (Sum.inr dart)) =
      Sum.inr (Sum.inl dart) :=
  rfl

@[simp]
theorem capDartEquiv_boundary (position : Fin 5) :
    data.capDartEquiv (Sum.inr (Sum.inl position)) =
      Sum.inl (data.crossingBoundaryDartEquiv position).1 := by
  simp [capDartEquiv, retainedDartEquivInternalSumBoundary]

@[simp]
theorem capDartEquiv_spoke (j : Fin 5) :
    data.capDartEquiv (Sum.inr (Sum.inr j)) = Sum.inr (Sum.inr j) :=
  rfl

theorem capSeamData_vertOf_eq_capTargetVert (dart : data.CapDart) :
    data.capSeamData.vertOf dart =
      data.capTargetVert (data.capDartEquiv dart) := by
  rcases dart with interior | boundaryOrSpoke
  · rcases interior with internal | cyc
    · rfl
    · rcases cyc with ⟨j, b⟩
      rfl
  · rcases boundaryOrSpoke with position | j
    · rw [data.capDartEquiv_boundary]
      rfl
    · rfl

/-- The transported vertex rotation preserves the vertex projection. -/
theorem capTargetRho_vert
    (dart : RetainedDart RS data.keep ⊕ ((Fin 5 × Bool) ⊕ Fin 5)) :
    data.capTargetVert (data.capTargetRho dart) =
      data.capTargetVert dart := by
  rcases dart with retained | pentagon
  · apply congrArg Sum.inl
    apply Subtype.ext
    exact RS.vert_rho retained.1
  · rcases pentagon with ⟨j, b⟩ | j
    · cases b <;> rfl
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

/-- Rewired dart system of the pentagon cap. -/
def capRewiredDartSystem :
    RewiredDartSystem data.CapVertex data.CapDart :=
  data.capSeamData.toRewiredDartSystem
    (by
      rintro (internal | cyc)
      · simp only [capSeamData, Equiv.sumCongr_apply, Sum.map_inl]
        rw [internalAlpha_involutive]
      · rcases cyc with ⟨j, b⟩
        cases b <;>
          simp [capSeamData, pentagonCyclePairing])
    (by
      rintro (internal | cyc)
      · simp only [capSeamData, Equiv.sumCongr_apply, Sum.map_inl, ne_eq,
          Sum.inl.injEq]
        exact internalAlpha_fixfree RS data.keep internal
      · rcases cyc with ⟨j, b⟩
        cases b <;>
          simp [capSeamData, pentagonCyclePairing, Prod.ext_iff] <;>
          decide +kernel)
    data.capSeamData_rho_vert
    (by
      rintro (internal | cyc)
      · simp only [capSeamData, Equiv.sumCongr_apply, Sum.map_inl, ne_eq,
          Sum.inl.injEq, Subtype.mk.injEq]
        exact fun h => RS.no_self_loops internal.1.1 (by
          simpa [internalAlpha] using h)
      · rcases cyc with ⟨j, b⟩
        cases b <;>
          simp only [capSeamData, Equiv.sumCongr_apply, Sum.map_inr, ne_eq,
            Sum.inr.injEq, pentagonCyclePairing, Equiv.coe_fn_mk] <;>
          revert j <;> decide)
    (by
      intro position
      simp [capSeamData])

/-- The rotation system of the pentagon-capped side. -/
def capRotationSystem :
    RotationSystem data.CapVertex data.capRewiredDartSystem.Edge :=
  data.capRewiredDartSystem.toRotationSystem

/-- The spoke dart at the cap vertex of one position. -/
def capDart (j : Fin 5) : data.CapDart :=
  Sum.inr (Sum.inr j)

/-- The cycle dart of one position and orientation. -/
def cycleDart (dart : Fin 5 × Bool) : data.CapDart :=
  Sum.inl (Sum.inr dart)

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

end FiveEdgeCutPentagonCapData

end

end Mettapedia.GraphTheory.FourColor
