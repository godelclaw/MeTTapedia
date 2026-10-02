import MettapediaFourColor.ExceptionalRepairChecked
import MettapediaFourColor.ExceptionalBoundaryReconstruction
import MettapediaFourColor.GraphTraceAlignment

/-! # From exceptional boundary repair to actual colouring reconstruction

The exterior relation below retains one assignment on the actual punctured
map. Consequently all coincident boundary images receive the same colour.
Kempe closure and initial exterior colourability remain explicit hypotheses;
the finite repair certificate does not assert either geometric property.
-/

namespace FourColor.ExceptionalRepairReconstruction

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence ExceptionalCore ExceptionalBoundaryOccurrence
open ExceptionalBoundaryReconstruction KempeBoundarySplit

set_option maxRecDepth 32768

theorem source_boundary : input.boundary = (List.finRange 11).map (Fin.castAdd 8) := by
  decide +kernel

noncomputable section

variable {W : Type*} [Fintype W] [DecidableEq W]
  {H : SimpleGraph W} [DecidableRel H.Adj]
  (original : Data H)
  (minimal : GoertzelV24TwoEdgeCutMinimality.GraphBackedVertexMinimalTaitCounterexample original)
  (x y : ExceptionalPattern.Occurrence (MinimalExceptionalEmbedding.rotation original minimal))
  (aligned : y.vertex 0 = x.vertex 14)

def ProperExterior (outside : OrbitFace original.toRotationSystem → Color) : Prop :=
  ∀ {v w}, v ∉ Set.range (coreVertex x) → w ∉ Set.range (coreVertex x) →
    (MinimalExceptionalEmbedding.graph original minimal).Adj v w → outside v ≠ outside w

/-- Every boundary observation comes from the same actual exterior colouring. -/
def ExteriorTrace (et : List Color) : Prop :=
  ∃ outside : OrbitFace original.toRotationSystem → Color,
    ProperExterior original minimal x outside ∧
    et = trace (input.boundary.map fun p =>
      outside (sourceHom original minimal x y aligned p))

/-- Align the complete patch by one colour translation, then glue literally. -/
theorem reconstruct_trace (inside : input.graph.Coloring Color)
    (outside : OrbitFace original.toRotationSystem → Color)
    (proper : ProperExterior original minimal x outside)
    (ht : trace (input.boundary.map inside) =
      trace (input.boundary.map fun p => outside (sourceHom original minimal x y aligned p))) :
    ∃ k : (MinimalExceptionalEmbedding.graph original minimal).Coloring Color,
      ∀ v, v ∉ Set.range (coreVertex x) → k v = outside v := by
  obtain ⟨shifted, he⟩ := GraphTraceAlignment.align input.boundary inside
    (input.boundary.map fun p => outside (sourceHom original minimal x y aligned p))
    (by simp) ht
  have agree : ∀ p : Fin 11, shifted (p.castAdd 8) =
      outside (sourceHom original minimal x y aligned (p.castAdd 8)) := by
    intro p
    exact (List.map_eq_map_iff.mp he) _ (by rw [source_boundary]; simp)
  obtain ⟨k, _, hext⟩ := ExceptionalBoundaryReconstruction.reconstruct
    original minimal x y aligned shifted outside proper agree
  exact ⟨k, hext⟩

/-- A repair contract with actual exterior semantics reconstructs a full
colouring. The unresolved geometric closure hypothesis is visible here. -/
theorem reconstruct_of_repair
    (repair : Repairs ExceptionalRepairCertificate.Supports 11)
    (closed : KempeClosed (ExteriorTrace original minimal x y aligned))
    (et : List Color) (hlen : et.length = 11) (hzero : (0 : Color) ∉ et)
    (hsum : et.sum = 0) (initial : ExteriorTrace original minimal x y aligned et) :
    Nonempty ((MinimalExceptionalEmbedding.graph original minimal).Coloring Color) := by
  obtain ⟨es, ⟨inside, hins⟩, outside, proper, hout⟩ :=
    repair et hlen hzero hsum _ closed initial
  obtain ⟨k, _⟩ := reconstruct_trace original minimal x y aligned inside outside proper
    (hins.symm.trans hout)
  exact ⟨k⟩

/-- The checked source repair fills the finite repair premise. Actual exterior
closure and a proper initial trace remain explicit geometric obligations. -/
theorem reconstruct
    (closed : KempeClosed (ExteriorTrace original minimal x y aligned))
    (et : List Color) (hlen : et.length = 11) (hzero : (0 : Color) ∉ et)
    (hsum : et.sum = 0) (initial : ExteriorTrace original minimal x y aligned et) :
    Nonempty ((MinimalExceptionalEmbedding.graph original minimal).Coloring Color) :=
  reconstruct_of_repair original minimal x y aligned ExceptionalRepairCertificate.repair
    closed et hlen hzero hsum initial

end
end FourColor.ExceptionalRepairReconstruction
