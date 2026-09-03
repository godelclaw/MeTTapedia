import Mettapedia.GraphTheory.FourColor.FiveEdgeCutYCapClass
import Mettapedia.GraphTheory.FourColor.Compositional.FiveCutShoreLanguage

/-!
# The Y-cap colours the shore inside the Y support

A Tait colouring of the Y-capped shore restricts to a proper colouring of
the shore port tangle.  Reading its boundary word in the cut coordinates:
the two seam ports carry the one seam-edge colour, and the three star
ports carry the three spoke colours — a Tait triple at the star vertex.
The word is therefore a member of the heart's `Y`-cap support at
position zero, inside the shore's boundary language.
-/

namespace Mettapedia.GraphTheory.FourColor

open Compositional.BoundaryKempeSwitch
open Compositional.FiveCutShoreLanguage
open GoertzelV24OpenTangleComposition
open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24VertexSidePrimalKempeTrail
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace FiveEdgeCutYCapData

variable (rotation : SimpleGraphDartRotation.Data G)
  (data : FiveEdgeCutYCapData rotation.toRotationSystem)

/-- The retained dart under a shore-tangle dart. -/
def retainedOfTangleDart :
    InternalDart rotation.toRotationSystem data.keep ⊕
        BoundaryDart rotation.toRotationSystem data.keep →
      RetainedDart rotation.toRotationSystem data.keep :=
  fun dart =>
    (retainedDartEquivInternalSumBoundary
      rotation.toRotationSystem data.keep).symm dart

/-- The cap edge read at a shore-tangle dart. -/
def capEdgeOfTangleDart
    (dart : InternalDart rotation.toRotationSystem data.keep ⊕
      BoundaryDart rotation.toRotationSystem data.keep) :
    data.capRewiredDartSystem.Edge :=
  data.capRewiredDartSystem.edgeOf
    (data.capDartOfRetained (data.retainedOfTangleDart rotation dart))

@[simp]
theorem retainedOfTangleDart_internal
    (internal : InternalDart rotation.toRotationSystem data.keep) :
    data.retainedOfTangleDart rotation (Sum.inl internal) = internal.1 := by
  simp [retainedOfTangleDart, retainedDartEquivInternalSumBoundary]

@[simp]
theorem retainedOfTangleDart_boundary
    (boundary : BoundaryDart rotation.toRotationSystem data.keep) :
    data.retainedOfTangleDart rotation (Sum.inr boundary) = boundary.1 := by
  simp [retainedOfTangleDart, retainedDartEquivInternalSumBoundary]

theorem capEdgeOfTangleDart_seam (part : Bool) :
    data.capEdgeOfTangleDart rotation (Sum.inr (data.seamDart part)) =
      data.seamEdge := by
  rw [capEdgeOfTangleDart, data.retainedOfTangleDart_boundary,
    data.capDartOfRetained_seam, data.seamEdge_eq]

theorem capEdgeOfTangleDart_star (spoke : Fin 3) :
    data.capEdgeOfTangleDart rotation (Sum.inr (data.starDart spoke)) =
      data.capSpokeEdge spoke := by
  rw [capEdgeOfTangleDart, data.retainedOfTangleDart_boundary,
    data.capDartOfRetained_star]
  calc
    data.capRewiredDartSystem.edgeOf (Sum.inr (Sum.inl spoke)) =
        data.capRewiredDartSystem.edgeOf
          (data.capRewiredDartSystem.alpha (Sum.inr (Sum.inl spoke))) :=
      (data.capRewiredDartSystem.edgeOf_alpha _).symm
    _ = data.capSpokeEdge spoke := by
      rw [data.capRewiredDartSystem_alpha_star]
      rfl

/-- Distinct spokes give adjacent cap edges at the star vertex. -/
theorem capSpokeEdgeAdj_of_ne {first second : Fin 3}
    (hne : first ≠ second) :
    data.capRotationSystem.edgeAdjacencyGraph.Adj
      (data.capSpokeEdge first) (data.capSpokeEdge second) := by
  rw [data.capRotationSystem.edgeAdjacencyGraph_adj_iff]
  refine ⟨data.capSpokeEdge_injective.ne hne, Sum.inr (), ?_, ?_⟩
  · exact (data.capRotationSystem.mem_endpoints_iff).2
      ⟨data.capDart first,
        (data.capRotationSystem.mem_dartsOn).2 rfl,
        data.capRotationSystem_vertOf_capDart first⟩
  · exact (data.capRotationSystem.mem_endpoints_iff).2
      ⟨data.capDart second,
        (data.capRotationSystem.mem_dartsOn).2 rfl,
        data.capRotationSystem_vertOf_capDart second⟩

/-- Embedded shore darts keep their vertex. -/
theorem capVertOf_retainedOfTangleDart
    (dart : InternalDart rotation.toRotationSystem data.keep ⊕
      BoundaryDart rotation.toRotationSystem data.keep) :
    data.capRotationSystem.vertOf
        (data.capDartOfRetained (data.retainedOfTangleDart rotation dart)) =
      Sum.inl
        ⟨rotation.toRotationSystem.vertOf
            (data.retainedOfTangleDart rotation dart).1,
          (data.retainedOfTangleDart rotation dart).2⟩ :=
  data.capRotationSystem_vertOf_capDartOfRetained _

/-- Two distinct shore darts at one vertex read distinct cap edges. -/
theorem capEdgeOfTangleDart_ne_of_ne
    {left right : InternalDart rotation.toRotationSystem data.keep ⊕
      BoundaryDart rotation.toRotationSystem data.keep}
    (hvert : rotation.toRotationSystem.vertOf
        (data.retainedOfTangleDart rotation left).1 =
      rotation.toRotationSystem.vertOf
        (data.retainedOfTangleDart rotation right).1)
    (hne : left ≠ right) :
    data.capEdgeOfTangleDart rotation left ≠
      data.capEdgeOfTangleDart rotation right := by
  set leftRetained := data.retainedOfTangleDart rotation left with hleftDef
  set rightRetained := data.retainedOfTangleDart rotation right with hrightDef
  have hretainedNe : leftRetained ≠ rightRetained := by
    intro heq
    exact hne ((retainedDartEquivInternalSumBoundary
      rotation.toRotationSystem data.keep).symm.injective heq)
  intro hedges
  rcases (data.capRewiredDartSystem.edgeOf_eq_edgeOf_iff
      (data.capDartOfRetained leftRetained)
      (data.capDartOfRetained rightRetained)).1 hedges with
    hsame | hopposite
  · exact hretainedNe (data.capDartOfRetained_injective hsame)
  · rcases hsplit : (retainedDartEquivInternalSumBoundary
        rotation.toRotationSystem data.keep) rightRetained with
      internal | boundary
    · -- internal partner: an ambient loop
      have hright : rightRetained = internal.1 := by
        have hsymm := (Equiv.eq_symm_apply _).mpr hsplit
        simpa [retainedDartEquivInternalSumBoundary] using hsymm
      rw [hright, data.capDartOfRetained_internal,
        data.capRewiredDartSystem_alpha_internal] at hopposite
      have hleft : leftRetained =
          (internalAlpha rotation.toRotationSystem data.keep internal).1 :=
        data.capDartOfRetained_injective
          (hopposite.trans (data.capDartOfRetained_internal _).symm)
      apply rotation.toRotationSystem.no_self_loops internal.1.1
      calc
        rotation.toRotationSystem.vertOf internal.1.1 =
            rotation.toRotationSystem.vertOf rightRetained.1 := by
          rw [hright]
        _ = rotation.toRotationSystem.vertOf leftRetained.1 := hvert.symm
        _ = rotation.toRotationSystem.vertOf
            (rotation.toRotationSystem.alpha internal.1.1) := by
          rw [hleft, internalAlpha_val]
    · -- boundary partner: seam mate or spoke
      have hright : rightRetained = boundary.1 := by
        have hsymm := (Equiv.eq_symm_apply _).mpr hsplit
        simpa [retainedDartEquivInternalSumBoundary] using hsymm
      rcases data.boundaryDart_eq_seam_or_star boundary with
        ⟨part, hpart⟩ | ⟨spoke, hspoke⟩
      · rw [hright, hpart, data.capDartOfRetained_seam,
          data.capRewiredDartSystem_alpha_seam] at hopposite
        have hleft : leftRetained = (data.seamDart (seamPairSwap part)).1 :=
          data.capDartOfRetained_injective
            (hopposite.trans (data.capDartOfRetained_seam _).symm)
        cases part
        · apply data.seamDart_vert_ne
          calc
            rotation.toRotationSystem.vertOf (data.seamDart false).1.1 =
                rotation.toRotationSystem.vertOf rightRetained.1 := by
              rw [hright, hpart]
            _ = rotation.toRotationSystem.vertOf leftRetained.1 :=
              hvert.symm
            _ = rotation.toRotationSystem.vertOf
                (data.seamDart true).1.1 := by
              rw [hleft]
              rfl
        · apply data.seamDart_vert_ne
          calc
            rotation.toRotationSystem.vertOf (data.seamDart false).1.1 =
                rotation.toRotationSystem.vertOf leftRetained.1 := by
              rw [hleft]
              rfl
            _ = rotation.toRotationSystem.vertOf rightRetained.1 := hvert
            _ = rotation.toRotationSystem.vertOf
                (data.seamDart true).1.1 := by
              rw [hright, hpart]
      · rw [hright, hspoke, data.capDartOfRetained_star,
          data.capRewiredDartSystem_alpha_star] at hopposite
        have hforms := data.capDartEquiv_capDartOfRetained leftRetained
        rw [hopposite] at hforms
        simp at hforms

/-- The shore-tangle vertex of a dart is its retained ambient vertex. -/
theorem tangleVert_eq
    (outer : RetainedDart rotation.toRotationSystem data.keep)
    (dart : InternalDart rotation.toRotationSystem data.keep ⊕
      BoundaryDart rotation.toRotationSystem data.keep) :
    (vertexSidePortTangle rotation data.keep outer).vert dart =
      ⟨rotation.toRotationSystem.vertOf
          (data.retainedOfTangleDart rotation dart).1,
        (data.retainedOfTangleDart rotation dart).2⟩ := by
  rcases dart with internal | boundary
  · apply Subtype.ext
    show rotation.toRotationSystem.vertOf internal.1.1 = _
    rw [data.retainedOfTangleDart_internal]
  · apply Subtype.ext
    show rotation.toRotationSystem.vertOf boundary.1.1 = _
    rw [data.retainedOfTangleDart_boundary]

/-- Restrict a cap edge colouring to the shore port tangle. -/
def shoreColoringOfCap
    (outer : RetainedDart rotation.toRotationSystem data.keep)
    (K : data.capRotationSystem.EdgeColoring Color) :
    Coloring (vertexSidePortTangle rotation data.keep outer) where
  color := fun dart => K (data.capEdgeOfTangleDart rotation dart)
  invariant := by
    intro d
    show K (data.capEdgeOfTangleDart rotation
        (Sum.inl (internalAlpha rotation.toRotationSystem data.keep d))) =
      K (data.capEdgeOfTangleDart rotation (Sum.inl d))
    congr 1
    rw [capEdgeOfTangleDart, capEdgeOfTangleDart,
      data.retainedOfTangleDart_internal,
      data.retainedOfTangleDart_internal,
      data.capDartOfRetained_internal, data.capDartOfRetained_internal]
    calc
      data.capRewiredDartSystem.edgeOf
          (Sum.inl (Sum.inl (internalAlpha
            rotation.toRotationSystem data.keep d))) =
          data.capRewiredDartSystem.edgeOf
            (data.capRewiredDartSystem.alpha (Sum.inl (Sum.inl d))) := by
        rw [data.capRewiredDartSystem_alpha_internal]
      _ = data.capRewiredDartSystem.edgeOf (Sum.inl (Sum.inl d)) :=
        data.capRewiredDartSystem.edgeOf_alpha _

/-- The restricted colouring is proper. -/
theorem shoreColoringOfCap_isProper
    (outer : RetainedDart rotation.toRotationSystem data.keep)
    (K : data.capRotationSystem.EdgeColoring Color)
    (hK : data.capRotationSystem.IsTaitEdgeColoring K) :
    IsProper (data.shoreColoringOfCap rotation outer K) := by
  constructor
  · intro dart
    exact hK _
  · intro left right hvert hne
    apply K.valid
    rw [data.capRotationSystem.edgeAdjacencyGraph_adj_iff]
    have hvertices : rotation.toRotationSystem.vertOf
        (data.retainedOfTangleDart rotation left).1 =
      rotation.toRotationSystem.vertOf
        (data.retainedOfTangleDart rotation right).1 := by
      have hchain := (data.tangleVert_eq rotation outer left).symm.trans
        (hvert.trans (data.tangleVert_eq rotation outer right))
      exact congrArg Subtype.val hchain
    refine ⟨data.capEdgeOfTangleDart_ne_of_ne rotation hvertices hne,
      data.capRotationSystem.vertOf
        (data.capDartOfRetained (data.retainedOfTangleDart rotation left)),
      ?_, ?_⟩
    · exact (data.capRotationSystem.mem_endpoints_iff).2
        ⟨data.capDartOfRetained (data.retainedOfTangleDart rotation left),
          (data.capRotationSystem.mem_dartsOn).2 rfl, rfl⟩
    · refine (data.capRotationSystem.mem_endpoints_iff).2
        ⟨data.capDartOfRetained (data.retainedOfTangleDart rotation right),
          (data.capRotationSystem.mem_dartsOn).2 rfl, ?_⟩
      rw [data.capVertOf_retainedOfTangleDart,
        data.capVertOf_retainedOfTangleDart]
      exact congrArg Sum.inl (Subtype.ext hvertices.symm)


/-! ## The boundary word lies in the Y support -/

theorem crossingBoundaryDartEquiv_zero :
    data.crossingBoundaryDartEquiv 0 = data.seamDart false := rfl

theorem crossingBoundaryDartEquiv_one :
    data.crossingBoundaryDartEquiv 1 = data.seamDart true := rfl

theorem crossingBoundaryDartEquiv_two :
    data.crossingBoundaryDartEquiv 2 = data.starDart 0 := rfl

theorem crossingBoundaryDartEquiv_three :
    data.crossingBoundaryDartEquiv 3 = data.starDart 1 := rfl

theorem crossingBoundaryDartEquiv_four :
    data.crossingBoundaryDartEquiv 4 = data.starDart 2 := rfl

/-- **The Y-capped shore's colouring lands the shore boundary word in the
heart's `Y` support at position zero.** -/
theorem exists_word_in_ySupport
    (outer : RetainedDart rotation.toRotationSystem data.keep)
    (K : data.capRotationSystem.EdgeColoring Color)
    (hK : data.capRotationSystem.IsTaitEdgeColoring K) :
    ∃ w : CAP5BoundaryWord,
      shoreLanguage data.crossingBoundaryDartEquiv
        (vertexSidePortTangle rotation data.keep outer) w ∧
      CAP5YCapSupport 0 w := by
  let coloring := data.shoreColoringOfCap rotation outer K
  have hproper := data.shoreColoringOfCap_isProper rotation outer K hK
  refine ⟨fun j => (properBoundaryWordInCoordinates
      data.crossingBoundaryDartEquiv coloring hproper j).1,
    shoreLanguage_of_coloring data.crossingBoundaryDartEquiv
      coloring hproper, ?_⟩
  have hvalue : ∀ j : Fin 5,
      (properBoundaryWordInCoordinates
        data.crossingBoundaryDartEquiv coloring hproper j).1 =
      K (data.capEdgeOfTangleDart rotation
        (Sum.inr (data.crossingBoundaryDartEquiv j))) := fun _ => rfl
  have h01 : ((0 : Fin 5) + 1) = 1 := by decide
  have h02 : ((0 : Fin 5) + 2) = 2 := by decide
  have h03 : ((0 : Fin 5) + 3) = 3 := by decide
  have h04 : ((0 : Fin 5) + 4) = 4 := by decide
  refine ⟨?_, ?_, ?_⟩
  · show (properBoundaryWordInCoordinates
        data.crossingBoundaryDartEquiv coloring hproper 0).1 =
      (properBoundaryWordInCoordinates
        data.crossingBoundaryDartEquiv coloring hproper (0 + 1)).1
    rw [h01, hvalue 0, hvalue 1,
      data.crossingBoundaryDartEquiv_zero,
      data.crossingBoundaryDartEquiv_one,
      data.capEdgeOfTangleDart_seam rotation false,
      data.capEdgeOfTangleDart_seam rotation true]
  · exact hK _
  · show IsTaitColorTriple
      (properBoundaryWordInCoordinates
        data.crossingBoundaryDartEquiv coloring hproper (0 + 2)).1
      (properBoundaryWordInCoordinates
        data.crossingBoundaryDartEquiv coloring hproper (0 + 3)).1
      (properBoundaryWordInCoordinates
        data.crossingBoundaryDartEquiv coloring hproper (0 + 4)).1
    rw [h02, h03, h04, hvalue 2, hvalue 3, hvalue 4,
      data.crossingBoundaryDartEquiv_two,
      data.crossingBoundaryDartEquiv_three,
      data.crossingBoundaryDartEquiv_four,
      data.capEdgeOfTangleDart_star rotation 0,
      data.capEdgeOfTangleDart_star rotation 1,
      data.capEdgeOfTangleDart_star rotation 2]
    refine ⟨hK _, hK _, hK _, ?_, ?_, ?_⟩
    · exact K.valid (data.capSpokeEdgeAdj_of_ne rotation
        (show (0 : Fin 3) ≠ 1 by decide))
    · exact K.valid (data.capSpokeEdgeAdj_of_ne rotation
        (show (0 : Fin 3) ≠ 2 by decide))
    · exact K.valid (data.capSpokeEdgeAdj_of_ne rotation
        (show (1 : Fin 3) ≠ 2 by decide))

end FiveEdgeCutYCapData

end

end Mettapedia.GraphTheory.FourColor
