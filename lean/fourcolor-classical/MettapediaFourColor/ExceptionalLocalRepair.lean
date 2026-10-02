import MettapediaFourColor.ExceptionalPreembedding
import MettapediaFourColor.ActualDualLocalGeometry
import MettapediaFourColor.ExceptionalConstructionRepair

/-!
# Closing the actual exceptional overlap by compatible repair

Two aligned exceptional occurrences determine one complete preembedding of
D1774. Its faithful kernel gives an injective disk. Vertex minimality supplies
the singleton contract colouring on that same embedding, and the checked
joint-chord repair reconstructs an ordinary colouring of the whole map.

This excludes the exceptional pair in the graph-backed minimality domain.
It does not classify zero-charge neighbourhoods or supply either occurrence.
The D1774 finite repair certificate is retained explicitly.
-/

namespace FourColor.ExceptionalLocalRepair

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalCore ExceptionalOverlap ExceptionalConstruction Hypermap
open GoertzelV24TwoEdgeCutMinimality

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

local instance : (MinimalExceptionalEmbedding.graph original minimal).LocallyFinite :=
  fun _ => Fintype.ofFinite _

/-- The complete disk is injected by the explicit joint reading. Coincident
boundary faces are permitted; off-perimeter darts remain distinct. -/
theorem disk_injective
    (r : JointReading (MinimalExceptionalEmbedding.rotation original minimal)) :
    Function.Injective (embdd (cfmap config).map
      (DualGraphQuery.map (MinimalExceptionalEmbedding.rotation original minimal))
      (cfring config) (ExceptionalPreembedding.reading r
        (MinimalExceptionalEmbedding.triangular original minimal)
        (MinimalExceptionalEmbedding.cyclic original minimal))) := by
  classical
  apply FaithfulKernelEmbedding.disk_injective embeddable
    (DualGraphQuery.plain _) (DualGraphQuery.cubic _
      (MinimalExceptionalEmbedding.triangular original minimal))
    (ExceptionalPreembedding.preembedding r _ _)
  exact ExceptionalPreembedding.faithful r _ _
    (ExceptionalDartReading.actual_faithful original minimal r)

/-- The starting contract, exterior closure and final patch colouring share
one actual embedding and one complete boundary relation. -/
theorem colorable
    (r : JointReading (MinimalExceptionalEmbedding.rotation original minimal)) :
    (DualGraphQuery.map (MinimalExceptionalEmbedding.rotation original minimal)).FourColorable := by
  classical
  let h := ExceptionalPreembedding.reading r
    (MinimalExceptionalEmbedding.triangular original minimal)
    (MinimalExceptionalEmbedding.cyclic original minimal)
  let M := DualGraphQuery.map (MinimalExceptionalEmbedding.rotation original minimal)
  obtain ⟨k, initial⟩ := ActualDualContract.singleton_colorable original minimal
    (embed (cfmap config).map M (cfring config) h ExceptionalConstructionRepair.contractDart)
  exact InjectiveEmbeddedRepair.colorable embeddable
    (ActualDualLocalGeometry.planar original minimal) (DualGraphQuery.plain _)
    (DualGraphQuery.cubic _ (MinimalExceptionalEmbedding.triangular original minimal))
    (ExceptionalPreembedding.preembedding r _ _) (disk_injective original minimal r)
    ExceptionalConstructionRepair.singleton_reducible initial

theorem not_in_minimal
    (r : JointReading (MinimalExceptionalEmbedding.rotation original minimal)) : False :=
  ActualDualContract.not_colorable original minimal (colorable original minimal r)

/-- Actual source occurrences suffice; neither an assumed embedding nor an
assumed compatible colouring is an additional input. -/
theorem aligned_not_in_minimal
    (x y : ExceptionalPattern.Occurrence (MinimalExceptionalEmbedding.rotation original minimal))
    (aligned : y.vertex 0 = x.vertex 14) : False := by
  classical
  exact not_in_minimal original minimal
    (jointReading x (MinimalExceptionalEmbedding.triangular original minimal)
      (MinimalExceptionalEmbedding.cyclic original minimal) y aligned)

/-- The exceptional closing field is now supplied in the actual minimal
map. Classifying a zero-charge neighbourhood remains an explicit input. -/
theorem overlap_supply {R : Type*}
    (support : R → Set (GoertzelV24FaceOrbitIncidence.OrbitFace original.toRotationSystem))
    (valid : R → Prop)
    (zero : GoertzelV24FaceOrbitIncidence.OrbitFace original.toRotationSystem → Prop)
    (classify : ∀ c, (MinimalExceptionalEmbedding.graph original minimal).degree c = 8 →
      LocalCoverageAssembly.OnBall (MinimalExceptionalEmbedding.graph original minimal) c 1 zero →
      LocalCoverageAssembly.OnBall (MinimalExceptionalEmbedding.graph original minimal) c 3
        (fun v => (MinimalExceptionalEmbedding.graph original minimal).degree v ≤ 8) →
      LocalCoverageAssembly.Occurs (MinimalExceptionalEmbedding.graph original minimal)
        support valid c 3 ∨
      Nonempty (Centered (MinimalExceptionalEmbedding.rotation original minimal) c)) :
    LocalCoverageAssembly.EightOverlapSupply (MinimalExceptionalEmbedding.graph original minimal)
      support valid zero (Centered (MinimalExceptionalEmbedding.rotation original minimal))
      (Mate (rotation := MinimalExceptionalEmbedding.rotation original minimal)) := by
  classical
  refine ⟨classify, ?_, ?_⟩
  · intro c x
    obtain ⟨u, hu, hd, hm⟩ := next_centered c x
    refine ⟨u, hu, ?_, hm⟩
    exact (SimpleGraph.degree_instance_independent u _ _).trans hd
  · intro c first u placed second
    exact False.elim (aligned_not_in_minimal original minimal first.val second.val
      (second.property.trans placed))

end
end FourColor.ExceptionalLocalRepair
