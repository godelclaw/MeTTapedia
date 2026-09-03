import Mettapedia.GraphTheory.FourColor.FiveEdgeCutPentagonCapClass
import Mettapedia.GraphTheory.FourColor.Compositional.FiveCutShoreLanguage

/-!
# The pentagon cap colours the shore inside the pentagon support

A Tait colouring of the pentagon-capped shore restricts to a proper
colouring of the shore port tangle.  Its boundary word carries the five
spoke colours, and the five cap cycle colours witness an internal
five-cycle colouring extending it: the word lies in the heart's pentagon
support, inside the shore's boundary language.
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

namespace FiveEdgeCutPentagonCapData

variable (rotation : SimpleGraphDartRotation.Data G)
  (data : FiveEdgeCutPentagonCapData rotation.toRotationSystem)

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

theorem capEdgeOfTangleDart_boundary (position : Fin 5) :
    data.capEdgeOfTangleDart rotation
        (Sum.inr (data.crossingBoundaryDartEquiv position)) =
      data.capSpokeEdge position := by
  rw [capEdgeOfTangleDart, data.retainedOfTangleDart_boundary,
    data.capDartOfRetained_boundary]
  calc
    data.capRewiredDartSystem.edgeOf (Sum.inr (Sum.inl position)) =
        data.capRewiredDartSystem.edgeOf
          (data.capRewiredDartSystem.alpha (Sum.inr (Sum.inl position))) :=
      (data.capRewiredDartSystem.edgeOf_alpha _).symm
    _ = data.capSpokeEdge position := by
      rw [data.capRewiredDartSystem_alpha_boundary]
      rfl

/-- The three cap edges at cap vertex `j` are pairwise adjacent. -/
theorem capSpokeEdge_adj_capCycleEdge (j : Fin 5) :
    data.capRotationSystem.edgeAdjacencyGraph.Adj
      (data.capSpokeEdge j) (data.capCycleEdge j) := by
  rw [data.capRotationSystem.edgeAdjacencyGraph_adj_iff]
  refine ⟨data.capSpokeEdge_ne_capCycleEdge j j, Sum.inr j, ?_, ?_⟩
  · exact (data.capRotationSystem.mem_endpoints_iff).2
      ⟨data.capDart j,
        (data.capRotationSystem.mem_dartsOn).2 rfl,
        data.capRotationSystem_vertOf_capDart j⟩
  · exact (data.capRotationSystem.mem_endpoints_iff).2
      ⟨data.cycleDart (j, true),
        (data.capRotationSystem.mem_dartsOn).2 rfl,
        data.capRotationSystem_vertOf_cycleDart (j, true)⟩

theorem capSpokeEdge_adj_capCycleEdge_pred (j : Fin 5) :
    data.capRotationSystem.edgeAdjacencyGraph.Adj
      (data.capSpokeEdge j) (data.capCycleEdge (j - 1)) := by
  rw [data.capRotationSystem.edgeAdjacencyGraph_adj_iff]
  refine ⟨data.capSpokeEdge_ne_capCycleEdge j (j - 1), Sum.inr j, ?_, ?_⟩
  · exact (data.capRotationSystem.mem_endpoints_iff).2
      ⟨data.capDart j,
        (data.capRotationSystem.mem_dartsOn).2 rfl,
        data.capRotationSystem_vertOf_capDart j⟩
  · refine (data.capRotationSystem.mem_endpoints_iff).2
      ⟨data.cycleDart (j, false), ?_,
        data.capRotationSystem_vertOf_cycleDart (j, false)⟩
    exact (data.capRotationSystem.mem_dartsOn).2
      (data.capCycleEdge_eq_false j)

theorem capCycleEdge_pred_adj_capCycleEdge (j : Fin 5) :
    data.capRotationSystem.edgeAdjacencyGraph.Adj
      (data.capCycleEdge (j - 1)) (data.capCycleEdge j) := by
  rw [data.capRotationSystem.edgeAdjacencyGraph_adj_iff]
  refine ⟨data.capCycleEdge_injective.ne (by
      intro h
      have := congrArg (fun x : Fin 5 => x + 1) h
      simp at this), Sum.inr j, ?_, ?_⟩
  · refine (data.capRotationSystem.mem_endpoints_iff).2
      ⟨data.cycleDart (j, false), ?_,
        data.capRotationSystem_vertOf_cycleDart (j, false)⟩
    exact (data.capRotationSystem.mem_dartsOn).2
      (data.capCycleEdge_eq_false j)
  · exact (data.capRotationSystem.mem_endpoints_iff).2
      ⟨data.cycleDart (j, true),
        (data.capRotationSystem.mem_dartsOn).2 rfl,
        data.capRotationSystem_vertOf_cycleDart (j, true)⟩

/-- The three colours at one cap vertex form a Tait triple. -/
theorem capVertex_isTaitColorTriple
    (K : data.capRotationSystem.EdgeColoring Color)
    (hK : data.capRotationSystem.IsTaitEdgeColoring K) (j : Fin 5) :
    IsTaitColorTriple (K (data.capSpokeEdge j))
      (K (data.capCycleEdge (j - 1))) (K (data.capCycleEdge j)) :=
  ⟨hK _, hK _, hK _,
    K.valid (data.capSpokeEdge_adj_capCycleEdge_pred rotation j),
    K.valid (data.capSpokeEdge_adj_capCycleEdge rotation j),
    K.valid (data.capCycleEdge_pred_adj_capCycleEdge rotation j)⟩

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
      rcases data.crossingBoundaryDartEquiv.surjective boundary with
        ⟨position, hposition⟩
      rw [hright, ← hposition, data.capDartOfRetained_boundary,
        data.capRewiredDartSystem_alpha_boundary] at hopposite
      have hforms := data.capDartEquiv_capDartOfRetained leftRetained
      rw [hopposite] at hforms
      simp [capDartEquiv_spoke] at hforms

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


/-! ## The boundary word lies in the pentagon support -/

/-- **The pentagon-capped shore's colouring lands the shore boundary word
in the heart's pentagon support.** -/
theorem exists_word_in_pentagonSupport
    (outer : RetainedDart rotation.toRotationSystem data.keep)
    (K : data.capRotationSystem.EdgeColoring Color)
    (hK : data.capRotationSystem.IsTaitEdgeColoring K) :
    ∃ w : CAP5BoundaryWord,
      shoreLanguage data.crossingBoundaryDartEquiv
        (vertexSidePortTangle rotation data.keep outer) w ∧
      CAP5WordExtendsAcrossCycle w := by
  let coloring := data.shoreColoringOfCap rotation outer K
  have hproper := data.shoreColoringOfCap_isProper rotation outer K hK
  refine ⟨fun j => (properBoundaryWordInCoordinates
      data.crossingBoundaryDartEquiv coloring hproper j).1,
    shoreLanguage_of_coloring data.crossingBoundaryDartEquiv
      coloring hproper, ?_⟩
  have hvalue : ∀ j : Fin 5,
      (properBoundaryWordInCoordinates
        data.crossingBoundaryDartEquiv coloring hproper j).1 =
      K (data.capSpokeEdge j) := by
    intro j
    show K (data.capEdgeOfTangleDart rotation
      (Sum.inr (data.crossingBoundaryDartEquiv j))) = _
    rw [data.capEdgeOfTangleDart_boundary]
  refine ⟨fun j => K (data.capCycleEdge j), ?_, ?_, ?_, ?_, ?_⟩
  · have htriple := data.capVertex_isTaitColorTriple rotation K hK 0
    rw [show ((0 : Fin 5) - 1) = 4 from by decide] at htriple
    simpa only [hvalue] using htriple
  · have htriple := data.capVertex_isTaitColorTriple rotation K hK 1
    rw [show ((1 : Fin 5) - 1) = 0 from by decide] at htriple
    simpa only [hvalue] using htriple
  · have htriple := data.capVertex_isTaitColorTriple rotation K hK 2
    rw [show ((2 : Fin 5) - 1) = 1 from by decide] at htriple
    simpa only [hvalue] using htriple
  · have htriple := data.capVertex_isTaitColorTriple rotation K hK 3
    rw [show ((3 : Fin 5) - 1) = 2 from by decide] at htriple
    simpa only [hvalue] using htriple
  · have htriple := data.capVertex_isTaitColorTriple rotation K hK 4
    rw [show ((4 : Fin 5) - 1) = 3 from by decide] at htriple
    simpa only [hvalue] using htriple

end FiveEdgeCutPentagonCapData

end

end Mettapedia.GraphTheory.FourColor
