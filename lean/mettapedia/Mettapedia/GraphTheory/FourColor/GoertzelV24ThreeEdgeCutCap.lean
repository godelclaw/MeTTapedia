import Mettapedia.GraphTheory.FourColor.GoertzelV24RewiredTaitColoring
import Mettapedia.GraphTheory.FourColor.GoertzelV24ThreeEdgeCutColor

namespace Mettapedia.GraphTheory.FourColor

namespace RotationSystem

open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor
open GoertzelV24ThreeEdgeCutColor

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- One rooted side of an exact ordered three-edge cut. The cap construction
retains the chosen vertices and attaches all three exposed half-edges to one
new cubic vertex. -/
structure ThreeEdgeCutSideData (RS : RotationSystem V E) where
  side : Finset V
  crossing : Fin 3 → E
  crossing_injective : Function.Injective crossing
  boundary_eq : RS.vertexSideEdgeBoundary side = orderedCut crossing
  outer_mem : RS.vertOf RS.outer ∈ side

namespace ThreeEdgeCutSideData

variable {RS : RotationSystem V E} (data : ThreeEdgeCutSideData RS)

/-- The retained vertex predicate. -/
def keep (vertex : V) : Prop :=
  vertex ∈ data.side

instance keepDecidablePred : DecidablePred data.keep :=
  fun vertex => Finset.decidableMem vertex data.side

theorem crossing_mem_boundary (step : Fin 3) :
    data.crossing step ∈ RS.vertexSideEdgeBoundary data.side := by
  rw [data.boundary_eq]
  exact Finset.mem_image.mpr ⟨step, Finset.mem_univ step, rfl⟩

/-- Every ordered cut edge has a unique outward-oriented retained dart. -/
theorem crosses (step : Fin 3) :
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

/-- Exactness of the three-edge boundary covers every exposed retained
dart. -/
theorem boundaryCover (dart : BoundaryDart RS data.keep) :
    RS.edgeOf dart.1.1 ∈ orderedCut data.crossing := by
  have hmem :=
    RS.boundaryDart_edge_mem_vertexSideEdgeBoundary data.side dart
  rw [data.boundary_eq] at hmem
  exact hmem

/-- Forgetting the redundant support proof is an equivalence because the
ordered three-edge cut is the complete boundary. -/
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
    Fin 3 ≃ BoundaryDart RS data.keep :=
  (orderedBoundaryDartEquiv RS data.keep data.crossing data.crosses
      data.crossing_injective).trans data.supportedBoundaryDartEquiv

@[simp]
theorem crossingBoundaryDartEquiv_edgeOf (step : Fin 3) :
    RS.edgeOf (data.crossingBoundaryDartEquiv step).1.1 =
      data.crossing step := by
  change RS.edgeOf
      (orderedBoundaryDart RS data.keep data.crossing data.crosses step).1.1.1 =
    data.crossing step
  exact orderedBoundaryDart_edgeOf RS data.keep data.crossing
    data.crosses step

/-- The honest vertex carrier of the capped side: all retained vertices and
one new cap vertex. -/
abbrev CapVertex := RetainedVertex data.keep ⊕ Unit

/-- The dart carrier of the capped side. Internal darts keep their old
partners, while each boundary dart is paired with one new cap dart. -/
abbrev CapDart :=
  MatchedSeam.Dart (InternalDart RS data.keep)
    (BoundaryDart RS data.keep) (Fin 3)

/-- Reassociate the cap dart carrier into old retained darts plus three new
cap darts. -/
def capDartEquiv :
    data.CapDart ≃ RetainedDart RS data.keep ⊕ Fin 3 :=
  (Equiv.sumAssoc (InternalDart RS data.keep)
      (BoundaryDart RS data.keep) (Fin 3)).symm |>.trans
    (Equiv.sumCongr
      (retainedDartEquivInternalSumBoundary RS data.keep).symm
      (Equiv.refl (Fin 3)))

/-- Vertex projection after reassociating the cap darts. -/
def capTargetVert : RetainedDart RS data.keep ⊕ Fin 3 → data.CapVertex
  | Sum.inl dart => Sum.inl ⟨RS.vertOf dart.1, dart.2⟩
  | Sum.inr _ => Sum.inr ()

/-- The old retained rotation together with a cyclic rotation at the new cap
vertex. -/
def capTargetRho : Equiv.Perm (RetainedDart RS data.keep ⊕ Fin 3) :=
  Equiv.sumCongr (retainedRho RS data.keep) (finRotate 3)

/-- Transport the old-plus-cap vertex rotation to the matched-seam dart
carrier. -/
def capRho : Equiv.Perm data.CapDart :=
  data.capDartEquiv.trans
    (data.capTargetRho.trans data.capDartEquiv.symm)

/-- Matched-seam data for the three-star cap. -/
def capSeamData :
    MatchedSeam.Data data.CapVertex
      (InternalDart RS data.keep)
      (BoundaryDart RS data.keep) (Fin 3) where
  interiorVert dart :=
    Sum.inl ⟨RS.vertOf dart.1.1, dart.1.2⟩
  leftVert dart :=
    Sum.inl ⟨RS.vertOf dart.1.1, dart.1.2⟩
  rightVert _ := Sum.inr ()
  interiorAlpha := internalAlpha RS data.keep
  matching := data.crossingBoundaryDartEquiv.symm
  rho := data.capRho
  outer := data.capDartEquiv.symm
    (Sum.inl ⟨RS.outer, data.outer_mem⟩)

@[simp]
theorem capDartEquiv_interior (dart : InternalDart RS data.keep) :
    data.capDartEquiv (Sum.inl dart) = Sum.inl dart.1 :=
  rfl

@[simp]
theorem capDartEquiv_boundary (dart : BoundaryDart RS data.keep) :
    data.capDartEquiv (Sum.inr (Sum.inl dart)) = Sum.inl dart.1 :=
  rfl

@[simp]
theorem capDartEquiv_cap (step : Fin 3) :
    data.capDartEquiv (Sum.inr (Sum.inr step)) = Sum.inr step :=
  rfl

theorem capSeamData_vertOf_eq_capTargetVert (dart : data.CapDart) :
    data.capSeamData.vertOf dart =
      data.capTargetVert (data.capDartEquiv dart) := by
  rcases dart with internal | boundaryOrCap
  · rfl
  · rcases boundaryOrCap with boundary | cap
    · rfl
    · rfl

/-- The transported vertex rotation preserves the cap vertex projection. -/
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

/-- Rewired dart system obtained by replacing the deleted side by one cubic
cap vertex. -/
def capRewiredDartSystem :
    RewiredDartSystem data.CapVertex data.CapDart :=
  data.capSeamData.toRewiredDartSystem
    (internalAlpha_involutive RS data.keep)
    (internalAlpha_fixfree RS data.keep)
    data.capSeamData_rho_vert
    (by
      intro internal
      simpa [capSeamData] using RS.no_self_loops internal.1.1)
    (by
      intro boundary
      simp [capSeamData])

/-- The rotation system of the capped side. -/
def capRotationSystem :
    RotationSystem data.CapVertex data.capRewiredDartSystem.Edge :=
  data.capRewiredDartSystem.toRotationSystem

/-- The new dart based at the cubic cap vertex in a given cut position. -/
def capDart (step : Fin 3) : data.CapDart :=
  Sum.inr (Sum.inr step)

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
theorem capDartEquiv_capDart (step : Fin 3) :
    data.capDartEquiv (data.capDart step) = Sum.inr step :=
  rfl

@[simp]
theorem capDartOfRetained_internal
    (dart : InternalDart RS data.keep) :
    data.capDartOfRetained dart.1 = Sum.inl dart := by
  apply data.capDartEquiv.injective
  simp

@[simp]
theorem capDartOfRetained_boundary
    (dart : BoundaryDart RS data.keep) :
    data.capDartOfRetained dart.1 = Sum.inr (Sum.inl dart) := by
  apply data.capDartEquiv.injective
  simp

@[simp]
theorem capRewiredDartSystem_alpha_internal
    (dart : InternalDart RS data.keep) :
    data.capRewiredDartSystem.alpha (Sum.inl dart) =
      Sum.inl (internalAlpha RS data.keep dart) :=
  rfl

@[simp]
theorem capRewiredDartSystem_alpha_boundary
    (dart : BoundaryDart RS data.keep) :
    data.capRewiredDartSystem.alpha (Sum.inr (Sum.inl dart)) =
      data.capDart (data.crossingBoundaryDartEquiv.symm dart) :=
  rfl

@[simp]
theorem capRewiredDartSystem_alpha_cap (step : Fin 3) :
    data.capRewiredDartSystem.alpha (data.capDart step) =
      Sum.inr (Sum.inl (data.crossingBoundaryDartEquiv step)) := by
  rfl

@[simp]
theorem capRotationSystem_vertOf_capDartOfRetained
    (dart : RetainedDart RS data.keep) :
    data.capRotationSystem.vertOf (data.capDartOfRetained dart) =
      Sum.inl ⟨RS.vertOf dart.1, dart.2⟩ := by
  change data.capSeamData.vertOf (data.capDartOfRetained dart) = _
  rw [data.capSeamData_vertOf_eq_capTargetVert]
  simp [capTargetVert]

@[simp]
theorem capRotationSystem_vertOf_capDart (step : Fin 3) :
    data.capRotationSystem.vertOf (data.capDart step) = Sum.inr () :=
  rfl

/-- The capped edge containing an old retained dart. -/
def capEdgeOfRetainedDart (dart : RetainedDart RS data.keep) :
    data.capRewiredDartSystem.Edge :=
  data.capRewiredDartSystem.edgeOf (data.capDartOfRetained dart)

/-- The cap edge at a given ordered cut position. -/
def capEdge (step : Fin 3) : data.capRewiredDartSystem.Edge :=
  data.capRewiredDartSystem.edgeOf (data.capDart step)

/-- An outward boundary dart and its corresponding new cap dart lie on the
same rewired edge. -/
theorem capEdgeOfRetainedDart_crossingBoundaryDartEquiv
    (step : Fin 3) :
    data.capEdgeOfRetainedDart
        (data.crossingBoundaryDartEquiv step).1 =
      data.capEdge step := by
  rw [capEdgeOfRetainedDart, data.capDartOfRetained_boundary]
  calc
    data.capRewiredDartSystem.edgeOf
        (Sum.inr (Sum.inl (data.crossingBoundaryDartEquiv step))) =
        data.capRewiredDartSystem.edgeOf
          (data.capRewiredDartSystem.alpha
            (Sum.inr (Sum.inl (data.crossingBoundaryDartEquiv step)))) :=
      (data.capRewiredDartSystem.edgeOf_alpha
        (Sum.inr (Sum.inl
          (data.crossingBoundaryDartEquiv step)))).symm
    _ = data.capEdge step := by
      rw [data.capRewiredDartSystem_alpha_boundary]
      rw [Equiv.symm_apply_apply]
      rfl

/-- Every exposed retained dart lies on the cap edge bearing its unique
ordered boundary position. -/
theorem capEdgeOfRetainedDart_eq_capEdge_of_boundary
    (dart : BoundaryDart RS data.keep) :
    data.capEdgeOfRetainedDart dart.1 =
      data.capEdge (data.crossingBoundaryDartEquiv.symm dart) := by
  simpa using data.capEdgeOfRetainedDart_crossingBoundaryDartEquiv
    (data.crossingBoundaryDartEquiv.symm dart)

/-- If both ends of an old edge are retained, its two old darts determine the
same internal cap edge. -/
theorem capEdgeOfRetainedDart_alpha_of_internal
    (dart : RS.D) (hkeep : data.keep (RS.vertOf dart))
    (hkeepAlpha : data.keep (RS.vertOf (RS.alpha dart))) :
    data.capEdgeOfRetainedDart ⟨RS.alpha dart, hkeepAlpha⟩ =
      data.capEdgeOfRetainedDart ⟨dart, hkeep⟩ := by
  let retained : RetainedDart RS data.keep := ⟨dart, hkeep⟩
  let internal : InternalDart RS data.keep := ⟨retained, hkeepAlpha⟩
  have hretainedAlpha :
      (⟨RS.alpha dart, hkeepAlpha⟩ : RetainedDart RS data.keep) =
        (internalAlpha RS data.keep internal).1 := by
    apply Subtype.ext
    rfl
  have hcap : data.capDartOfRetained
      (⟨dart, hkeep⟩ : RetainedDart RS data.keep) = Sum.inl internal := by
    change data.capDartOfRetained retained = Sum.inl internal
    exact data.capDartOfRetained_internal internal
  have hcapAlpha : data.capDartOfRetained
      (⟨RS.alpha dart, hkeepAlpha⟩ : RetainedDart RS data.keep) =
        Sum.inl (internalAlpha RS data.keep internal) := by
    rw [hretainedAlpha]
    exact data.capDartOfRetained_internal
      (internalAlpha RS data.keep internal)
  unfold capEdgeOfRetainedDart
  rw [hcapAlpha, hcap]
  exact data.capRewiredDartSystem.edgeOf_alpha (Sum.inl internal)

/-- Distinct retained darts based at one old vertex determine adjacent,
distinct edges of the capped rotation system. -/
theorem capEdgeAdj_of_retainedDarts
    (left right : RetainedDart RS data.keep)
    (hvertex : RS.vertOf left.1 = RS.vertOf right.1)
    (hne : left.1 ≠ right.1) :
    data.capRotationSystem.edgeAdjacencyGraph.Adj
      (data.capEdgeOfRetainedDart left)
      (data.capEdgeOfRetainedDart right) := by
  let vertex : data.CapVertex :=
    Sum.inl ⟨RS.vertOf left.1, left.2⟩
  have hleftAt : data.capDartOfRetained left ∈
      data.capRotationSystem.dartsAt vertex := by
    unfold RotationSystem.dartsAt
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,
        data.capRotationSystem_vertOf_capDartOfRetained left⟩
  have hrightAt : data.capDartOfRetained right ∈
      data.capRotationSystem.dartsAt vertex := by
    have hvertices :
        (Sum.inl ⟨RS.vertOf right.1, right.2⟩ : data.CapVertex) =
          vertex := by
      apply congrArg
        (fun retained : RetainedVertex data.keep =>
          (Sum.inl retained : data.CapVertex))
      exact Subtype.ext hvertex.symm
    unfold RotationSystem.dartsAt
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,
        (data.capRotationSystem_vertOf_capDartOfRetained right).trans
          hvertices⟩
  have hedgeNe : data.capEdgeOfRetainedDart left ≠
      data.capEdgeOfRetainedDart right := by
    intro hedges
    have hdarts := data.capRotationSystem.edgeOf_injOn_dartsAt vertex
      hleftAt hrightAt hedges
    exact hne (congrArg Subtype.val
      (data.capDartOfRetained_injective hdarts))
  apply data.capRotationSystem.edgeAdjacencyGraph_adj_of_mem_incidentEdges
    hedgeNe
  · exact (data.capRotationSystem.mem_incidentEdges_iff).2
      ⟨data.capDartOfRetained left, rfl,
        data.capRotationSystem_vertOf_capDartOfRetained left⟩
  · exact (data.capRotationSystem.mem_incidentEdges_iff).2
      ⟨data.capDartOfRetained right, rfl,
        (data.capRotationSystem_vertOf_capDartOfRetained right).trans
          (by
            apply congrArg
              (fun retained : RetainedVertex data.keep =>
                (Sum.inl retained : data.CapVertex))
            exact Subtype.ext hvertex.symm)⟩

/-- The three new cap edges are distinct. -/
theorem capEdge_injective : Function.Injective data.capEdge := by
  intro first second hedges
  rcases (data.capRewiredDartSystem.edgeOf_eq_edgeOf_iff
      (data.capDart first) (data.capDart second)).1 hedges with
    hdarts | hdarts
  · exact Sum.inr.inj (Sum.inr.inj hdarts)
  · exfalso
    rw [data.capRewiredDartSystem_alpha_cap] at hdarts
    change Sum.inr (Sum.inr first) =
      Sum.inr (Sum.inl (data.crossingBoundaryDartEquiv second)) at hdarts
    simp at hdarts

/-- Distinct cap positions determine adjacent edges at the new cubic cap
vertex. -/
theorem capEdgeAdj_of_ne {first second : Fin 3}
    (hne : first ≠ second) :
    data.capRotationSystem.edgeAdjacencyGraph.Adj
      (data.capEdge first) (data.capEdge second) := by
  rw [data.capRotationSystem.edgeAdjacencyGraph_adj_iff]
  refine ⟨data.capEdge_injective.ne hne, Sum.inr (), ?_, ?_⟩
  · exact (data.capRotationSystem.mem_endpoints_iff).2
      ⟨data.capDart first,
        (data.capRotationSystem.mem_dartsOn).2 rfl, rfl⟩
  · exact (data.capRotationSystem.mem_endpoints_iff).2
      ⟨data.capDart second,
        (data.capRotationSystem.mem_dartsOn).2 rfl, rfl⟩

/-- Expanding the image of an ordered three-edge cut. -/
theorem orderedCut_crossing_eq_triple :
    orderedCut data.crossing =
      {data.crossing 0, data.crossing 1, data.crossing 2} := by
  ext edge
  constructor
  · intro hedge
    rcases Finset.mem_image.mp hedge with ⟨step, _, rfl⟩
    fin_cases step <;> simp
  · intro hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with hfirst | hsecond | hthird
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, hfirst.symm⟩
    · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ 1, hsecond.symm⟩
    · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ 2, hthird.symm⟩

theorem crossing_zero_ne_one : data.crossing 0 ≠ data.crossing 1 :=
  data.crossing_injective.ne (by decide)

theorem crossing_zero_ne_two : data.crossing 0 ≠ data.crossing 2 :=
  data.crossing_injective.ne (by decide)

theorem crossing_one_ne_two : data.crossing 1 ≠ data.crossing 2 :=
  data.crossing_injective.ne (by decide)

/-- Cut parity makes the ambient colors on the ordered boundary into a Tait
triple. -/
theorem ambientCrossing_isTaitColorTriple
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    IsTaitColorTriple (C (data.crossing 0))
      (C (data.crossing 1)) (C (data.crossing 2)) := by
  apply threeEdgeCut_isTaitColorTriple RS hCubic C hC data.side
    data.crossing_zero_ne_one data.crossing_zero_ne_two
    data.crossing_one_ne_two
  rw [data.boundary_eq, data.orderedCut_crossing_eq_triple]

/-- Consequently, the ordered ambient boundary-color word is injective. -/
theorem ambientCrossingColor_injective
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    Function.Injective (fun step => C (data.crossing step)) := by
  have htriple := data.ambientCrossing_isTaitColorTriple hCubic C hC
  intro first second hcolors
  fin_cases first <;> fin_cases second
  all_goals simp_all [IsTaitColorTriple]

/-- Read the ambient edge color on retained darts and use the ordered cut
color on the three new cap darts. -/
def ambientCapDartColor (C : RS.EdgeColoring Color)
    (dart : data.CapDart) : Color :=
  match data.capDartEquiv dart with
  | Sum.inl retained => C (RS.edgeOf retained.1)
  | Sum.inr step => C (data.crossing step)

@[simp]
theorem ambientCapDartColor_capDartOfRetained
    (C : RS.EdgeColoring Color) (dart : RetainedDart RS data.keep) :
    data.ambientCapDartColor C (data.capDartOfRetained dart) =
      C (RS.edgeOf dart.1) := by
  simp [ambientCapDartColor]

@[simp]
theorem ambientCapDartColor_capDart
    (C : RS.EdgeColoring Color) (step : Fin 3) :
    data.ambientCapDartColor C (data.capDart step) =
      C (data.crossing step) := by
  rfl

/-- The ambient cap dart coloring is invariant under the rewired edge
involution. -/
theorem ambientCapDartColor_alpha
    (C : RS.EdgeColoring Color) (dart : data.CapDart) :
    data.ambientCapDartColor C (data.capRewiredDartSystem.alpha dart) =
      data.ambientCapDartColor C dart := by
  rcases dart with internal | boundaryOrCap
  · simp [ambientCapDartColor, RS.edge_alpha]
  · rcases boundaryOrCap with boundary | step
    · change C (data.crossing (data.crossingBoundaryDartEquiv.symm boundary)) =
        C (RS.edgeOf boundary.1.1)
      congr 1
      simpa using (data.crossingBoundaryDartEquiv_edgeOf
        (data.crossingBoundaryDartEquiv.symm boundary)).symm
    · change C (RS.edgeOf (data.crossingBoundaryDartEquiv step).1.1) =
        C (data.crossing step)
      rw [data.crossingBoundaryDartEquiv_edgeOf]

/-- Properness of an ambient coloring separates two distinct retained darts
based at the same old vertex. -/
theorem ambientColor_ne_of_retainedDarts
    (C : RS.EdgeColoring Color)
    {left right : RetainedDart RS data.keep}
    (hvertex : RS.vertOf left.1 = RS.vertOf right.1)
    (hne : left ≠ right) :
    C (RS.edgeOf left.1) ≠ C (RS.edgeOf right.1) := by
  apply C.valid
  rw [RS.edgeAdjacencyGraph_adj_iff]
  refine ⟨?_, RS.vertOf left.1, ?_, ?_⟩
  · intro hedges
    apply hne
    apply Subtype.ext
    apply RS.edgeOf_injOn_dartsAt (RS.vertOf left.1)
    · simp [dartsAt]
    · simpa [dartsAt] using hvertex.symm
    · exact hedges
  · exact (RS.mem_endpoints_iff).2
      ⟨left.1, (RS.mem_dartsOn).2 rfl, rfl⟩
  · exact (RS.mem_endpoints_iff).2
      ⟨right.1, (RS.mem_dartsOn).2 rfl, hvertex.symm⟩

/-- The ambient coloring remains locally proper after the three exposed
half-edges are attached to the new cap vertex. -/
theorem ambientCapDartColor_proper
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C)
    {left right : data.CapDart}
    (hvertex : data.capRewiredDartSystem.vertOf left =
      data.capRewiredDartSystem.vertOf right)
    (hne : left ≠ right) :
    data.ambientCapDartColor C left ≠
      data.ambientCapDartColor C right := by
  let leftTarget := data.capDartEquiv left
  let rightTarget := data.capDartEquiv right
  have htargetVertex :
      data.capTargetVert leftTarget = data.capTargetVert rightTarget := by
    rw [← data.capSeamData_vertOf_eq_capTargetVert,
      ← data.capSeamData_vertOf_eq_capTargetVert]
    exact hvertex
  have htargetNe : leftTarget ≠ rightTarget := by
    intro htargets
    exact hne (data.capDartEquiv.injective htargets)
  unfold ambientCapDartColor
  rw [show data.capDartEquiv left = leftTarget by rfl,
    show data.capDartEquiv right = rightTarget by rfl]
  rcases leftTarget with leftRetained | leftStep <;>
    rcases rightTarget with rightRetained | rightStep
  · apply data.ambientColor_ne_of_retainedDarts C
    · exact congrArg Subtype.val (Sum.inl.inj htargetVertex)
    · intro hretained
      exact htargetNe (congrArg Sum.inl hretained)
  · simp [capTargetVert] at htargetVertex
  · simp [capTargetVert] at htargetVertex
  · apply (data.ambientCrossingColor_injective hCubic C hC).ne
    intro hsteps
    exact htargetNe (congrArg Sum.inr hsteps)

/-- Descend the ambient coloring to a proper coloring of the capped side. -/
def capColoring (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    data.capRotationSystem.EdgeColoring Color :=
  data.capRewiredDartSystem.descendedColoring
    (data.ambientCapDartColor C)
    (data.ambientCapDartColor_alpha C)
    (data.ambientCapDartColor_proper hCubic C hC)

/-- The ambient Tait coloring restricts to a Tait coloring of the three-star
cap. -/
theorem capColoring_isTait
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    data.capRotationSystem.IsTaitEdgeColoring
      (data.capColoring hCubic C hC) := by
  apply data.capRewiredDartSystem.descendedColoring_isTait
    (data.ambientCapDartColor C)
    (data.ambientCapDartColor_alpha C)
    (data.ambientCapDartColor_proper hCubic C hC)
  intro dart
  unfold ambientCapDartColor
  rcases data.capDartEquiv dart with retained | step
  · exact hC (RS.edgeOf retained.1)
  · exact hC (data.crossing step)

/-- On an old retained dart, the induced cap coloring is the old ambient
edge color. -/
theorem capColoring_capEdgeOfRetainedDart
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C)
    (dart : RetainedDart RS data.keep) :
    data.capColoring hCubic C hC (data.capEdgeOfRetainedDart dart) =
      C (RS.edgeOf dart.1) := by
  change data.capRewiredDartSystem.descendedEdgeColor
      (data.ambientCapDartColor C)
      (data.capRewiredDartSystem.edgeOf (data.capDartOfRetained dart)) =
    C (RS.edgeOf dart.1)
  calc
    _ = data.ambientCapDartColor C (data.capDartOfRetained dart) :=
      data.capRewiredDartSystem.descendedEdgeColor_edgeOf
        (data.ambientCapDartColor C) (data.ambientCapDartColor_alpha C)
        (data.capDartOfRetained dart)
    _ = C (RS.edgeOf dart.1) :=
      data.ambientCapDartColor_capDartOfRetained C dart

/-- At each ordered cut position, the induced cap edge keeps the ambient
cut-edge color. -/
theorem capColoring_capEdge
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) (step : Fin 3) :
    data.capColoring hCubic C hC (data.capEdge step) =
      C (data.crossing step) := by
  change data.capRewiredDartSystem.descendedEdgeColor
      (data.ambientCapDartColor C)
      (data.capRewiredDartSystem.edgeOf (data.capDart step)) =
    C (data.crossing step)
  calc
    _ = data.ambientCapDartColor C (data.capDart step) :=
      data.capRewiredDartSystem.descendedEdgeColor_edgeOf
        (data.ambientCapDartColor C) (data.ambientCapDartColor_alpha C)
        (data.capDart step)
    _ = C (data.crossing step) :=
      data.ambientCapDartColor_capDart C step

/-- Any Tait coloring of the cap gives an ordered Tait triple on its three
cap edges. -/
theorem capEdge_isTaitColorTriple
    (C : data.capRotationSystem.EdgeColoring Color)
    (hC : data.capRotationSystem.IsTaitEdgeColoring C) :
    IsTaitColorTriple (C (data.capEdge 0))
      (C (data.capEdge 1)) (C (data.capEdge 2)) := by
  refine ⟨hC _, hC _, hC _, ?_, ?_, ?_⟩
  · exact C.valid (data.capEdgeAdj_of_ne (by decide))
  · exact C.valid (data.capEdgeAdj_of_ne (by decide))
  · exact C.valid (data.capEdgeAdj_of_ne (by decide))

/-- Darts over a retained cap vertex are exactly the old darts over its
ambient vertex. -/
def capTargetDartsAtRetainedEquiv (vertex : RetainedVertex data.keep) :
    { target : RetainedDart RS data.keep ⊕ Fin 3 //
      data.capTargetVert target = Sum.inl vertex } ≃
      { dart : RS.D // RS.vertOf dart = vertex.1 } where
  toFun target := by
    rcases target with ⟨retained | step, htarget⟩
    · have hvertices :
          (⟨RS.vertOf retained.1, retained.2⟩ :
            RetainedVertex data.keep) = vertex := by
        change (Sum.inl
          (⟨RS.vertOf retained.1, retained.2⟩ :
            RetainedVertex data.keep) : data.CapVertex) =
          Sum.inl vertex at htarget
        exact Sum.inl.inj htarget
      exact ⟨retained.1, congrArg Subtype.val hvertices⟩
    ·
      change (Sum.inr () : data.CapVertex) = Sum.inl vertex at htarget
      exact False.elim (by cases htarget)
  invFun dart :=
    ⟨Sum.inl ⟨dart.1, dart.2.symm ▸ vertex.2⟩, by
      change (Sum.inl
        (⟨RS.vertOf dart.1, _⟩ : RetainedVertex data.keep) :
          data.CapVertex) = Sum.inl vertex
      exact congrArg
        (fun retained : RetainedVertex data.keep =>
          (Sum.inl retained : data.CapVertex))
        (Subtype.ext dart.2)⟩
  left_inv target := by
    rcases target with ⟨retained | step, htarget⟩
    · apply Subtype.ext
      apply congrArg
        (fun retained : RetainedDart RS data.keep =>
          (Sum.inl retained : RetainedDart RS data.keep ⊕ Fin 3))
      apply Subtype.ext
      rfl
    ·
      change (Sum.inr () : data.CapVertex) = Sum.inl vertex at htarget
      exact False.elim (by cases htarget)
  right_inv dart := by
    apply Subtype.ext
    rfl

/-- The cap-dart equivalence restricted to one retained vertex. -/
def capRetainedVertexDartsEquiv (vertex : RetainedVertex data.keep) :
    { dart : data.CapDart //
      data.capRotationSystem.vertOf dart = Sum.inl vertex } ≃
      { dart : RS.D // RS.vertOf dart = vertex.1 } :=
  (data.capDartEquiv.subtypeEquiv (fun dart => by
      change data.capSeamData.vertOf dart = Sum.inl vertex ↔
        data.capTargetVert (data.capDartEquiv dart) = Sum.inl vertex
      rw [data.capSeamData_vertOf_eq_capTargetVert])).trans
    (data.capTargetDartsAtRetainedEquiv vertex)

/-- The local dart count at a retained vertex is unchanged. -/
theorem capRotationSystem_dartsAt_retained_card
    (vertex : RetainedVertex data.keep) :
    (data.capRotationSystem.dartsAt (Sum.inl vertex)).card =
      (RS.dartsAt vertex.1).card := by
  classical
  unfold RotationSystem.dartsAt
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (data.capRetainedVertexDartsEquiv vertex)

/-- The target darts based at the new cap vertex are exactly its three
ordered positions. -/
def capTargetDartsAtCapEquiv :
    { target : RetainedDart RS data.keep ⊕ Fin 3 //
      data.capTargetVert target = Sum.inr () } ≃ Fin 3 where
  toFun target := by
    rcases target with ⟨retained | step, htarget⟩
    ·
      change (Sum.inl
        (⟨RS.vertOf retained.1, retained.2⟩ : RetainedVertex data.keep) :
          data.CapVertex) = Sum.inr () at htarget
      exact False.elim (by cases htarget)
    · exact step
  invFun step := ⟨Sum.inr step, rfl⟩
  left_inv target := by
    rcases target with ⟨retained | step, htarget⟩
    ·
      change (Sum.inl
        (⟨RS.vertOf retained.1, retained.2⟩ : RetainedVertex data.keep) :
          data.CapVertex) = Sum.inr () at htarget
      exact False.elim (by cases htarget)
    · apply Subtype.ext
      rfl
  right_inv _ := rfl

/-- The cap-dart equivalence restricted to the new cap vertex. -/
def capVertexDartsEquiv :
    { dart : data.CapDart //
      data.capRotationSystem.vertOf dart = Sum.inr () } ≃ Fin 3 :=
  (data.capDartEquiv.subtypeEquiv (fun dart => by
      change data.capSeamData.vertOf dart = Sum.inr () ↔
        data.capTargetVert (data.capDartEquiv dart) = Sum.inr ()
      rw [data.capSeamData_vertOf_eq_capTargetVert])).trans
    data.capTargetDartsAtCapEquiv

/-- The new cap vertex has exactly three darts. -/
theorem capRotationSystem_dartsAt_cap_card :
    (data.capRotationSystem.dartsAt (Sum.inr ())).card = 3 := by
  classical
  unfold RotationSystem.dartsAt
  rw [← Fintype.card_subtype]
  calc
    Fintype.card { dart : data.CapDart //
        data.capRotationSystem.vertOf dart = Sum.inr () } =
        Fintype.card (Fin 3) :=
      Fintype.card_congr data.capVertexDartsEquiv
    _ = 3 := Fintype.card_fin 3

/-- Attaching the exact three-edge boundary to one new vertex preserves
cubicity. -/
theorem capRotationSystem_isCubic (hCubic : RS.IsCubic) :
    data.capRotationSystem.IsCubic := by
  intro vertex
  rcases vertex with retained | cap
  · rw [data.capRotationSystem_dartsAt_retained_card]
    exact hCubic retained.1
  · rcases cap with ⟨⟩
    exact data.capRotationSystem_dartsAt_cap_card

/-- Embed a capped-side vertex in the ambient carrier by using a deleted
vertex as the image of the new cap vertex. -/
def capVertexToAmbient (replacement : V) : data.CapVertex → V
  | Sum.inl retained => retained.1
  | Sum.inr _ => replacement

/-- The cap-vertex embedding is injective when its replacement really lies
outside the retained side. -/
theorem capVertexToAmbient_injective (replacement : V)
    (hreplacement : replacement ∉ data.side) :
    Function.Injective (data.capVertexToAmbient replacement) := by
  intro left right heq
  rcases left with retainedLeft | capLeft <;>
    rcases right with retainedRight | capRight
  · apply congrArg Sum.inl
    exact Subtype.ext heq
  · exfalso
    apply hreplacement
    change retainedLeft.1 = replacement at heq
    rw [← heq]
    exact retainedLeft.2
  · exfalso
    apply hreplacement
    change replacement = retainedRight.1 at heq
    rw [heq]
    exact retainedRight.2
  · rcases capLeft with ⟨⟩
    rcases capRight with ⟨⟩
    rfl

/-- Two distinct deleted vertices make the capped side strictly smaller than
the ambient vertex carrier: one receives the new cap vertex and the other is
still absent from the embedding. -/
theorem card_capVertex_lt_of_two_deleted
    (replacement omitted : V)
    (hreplacement : replacement ∉ data.side)
    (homitted : omitted ∉ data.side)
    (hne : omitted ≠ replacement) :
    Fintype.card data.CapVertex < Fintype.card V := by
  apply Fintype.card_lt_of_injective_of_notMem
    (data.capVertexToAmbient replacement)
    (data.capVertexToAmbient_injective replacement hreplacement)
    (b := omitted)
  rintro ⟨capVertex, hcapVertex⟩
  rcases capVertex with retained | cap
  · apply homitted
    rw [← hcapVertex]
    exact retained.2
  · apply hne
    simpa [capVertexToAmbient] using hcapVertex.symm

end ThreeEdgeCutSideData

end

end RotationSystem

end Mettapedia.GraphTheory.FourColor
