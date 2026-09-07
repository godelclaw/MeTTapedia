import Mettapedia.GraphTheory.FourColor.GoertzelV24SphericalReductiveAssembly

/-!
# Least-size selection is not an effective structural threshold

All globally vertex-minimal counterexamples have the same vertex count.
Consequently a uniform bound on their vertex counts exists by classical
least-size selection, independently of any corridor geometry. This must not
be credited as a construction of the route's effective threshold: verifying
the bounded base at this semantic threshold is already equivalent to the
entire cap-stable Tait statement.

The threshold below depends on the set of actual counterexamples. It is not
evaluated, and no explicit numeral, width supplier, or finite audit is given.
This module audits an ineffective shortcut; it is not used as a supplier in
the reductive assembly.
-/

namespace Mettapedia.GraphTheory.FourColor.LeastSizeBoundAudit

open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24SphericalMinimalCounterexampleSelection
open GoertzelV24SphericalReductiveAssembly
open GoertzelV24StellarTaitReduction
open SimpleGraphDartRotation

universe u

/-- The infimum of the actual bad-size set, not a computed threshold. -/
noncomputable def semanticThreshold : Nat := sInf (counterexampleVertexCounts.{u})

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- Minimality itself pins the size to the least bad size. -/
theorem card_eq_semanticThreshold (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) :
    Fintype.card V = semanticThreshold.{u} := by
  classical
  have hmem : Fintype.card V ∈ counterexampleVertexCounts.{u} :=
    ⟨V, G.edgeSet, inferInstance, inferInstance, inferInstance, inferInstance,
      rotation.toRotationSystem, ⟨minimal.toBridgelessSphericalCubicMapData⟩,
      minimal.notColorable, rfl⟩
  have hle : semanticThreshold.{u} ≤ Fintype.card V := Nat.sInf_le hmem
  obtain ⟨V', E', fV', dV', fE', dE', candidate, ⟨hclass⟩, hbad, hcard⟩ :=
    Nat.sInf_mem (show (counterexampleVertexCounts.{u}).Nonempty from ⟨_, hmem⟩)
  have hnotlt : ¬ Fintype.card V' < Fintype.card V := by
    intro hlt
    exact hbad (minimal.smallerColorable candidate hlt hclass)
  change Fintype.card V' = semanticThreshold.{u} at hcard
  omega

/-- Mere existence of a bound on globally minimal sizes is automatic. -/
theorem exists_uniform_minimal_size_bound :
    ∃ N : Nat,
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        {H : SimpleGraph W} [DecidableRel H.Adj] (rotation : Data H),
        GraphBackedVertexMinimalTaitCounterexample rotation → Fintype.card W ≤ N := by
  refine ⟨semanticThreshold.{u}, ?_⟩
  intro W _ _ H _ rotation minimal
  exact (card_eq_semanticThreshold rotation minimal).le

/-- The apparent finite base at the semantic threshold carries the whole
no-minimal-counterexample obligation. -/
theorem base_at_semanticThreshold_iff_no_minimal :
    TaitBaseVerifiedAt.{u} semanticThreshold.{u} ↔
      NoGraphBackedVertexMinimalTaitCounterexample.{u} := by
  constructor
  · intro hbase W _ _ H _ rotation minimal
    exact minimal.notColorable
      (hbase rotation minimal.toBridgelessSphericalCubicMapData
        (card_eq_semanticThreshold rotation minimal).le)
  · intro hnominimal W _ _ H _ rotation hclass _
    exact everyBridgelessSphericalCubicTaitColorable_of_no_minimal hnominimal
      rotation.toRotationSystem hclass

/-- The semantic base is equivalent to the target. Unlike a reduction with an
explicit threshold, this equivalence supplies no numerical base to check. -/
theorem base_at_semanticThreshold_iff_universal :
    TaitBaseVerifiedAt.{u} semanticThreshold.{u} ↔
      EveryBridgelessSphericalCubicTaitColorable.{u} := by
  constructor
  · intro hbase
    exact everyBridgelessSphericalCubicTaitColorable_of_no_minimal
      (base_at_semanticThreshold_iff_no_minimal.mp hbase)
  · intro hall W _ _ H _ rotation hclass _
    exact hall rotation.toRotationSystem hclass

end Mettapedia.GraphTheory.FourColor.LeastSizeBoundAudit
