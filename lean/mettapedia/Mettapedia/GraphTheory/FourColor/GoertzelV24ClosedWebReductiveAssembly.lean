import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebAtGoodWord
import Mettapedia.GraphTheory.FourColor.GoertzelV24ReductiveSpine

/-!
# Carrier-changing reductive assembly for closed webs at a good word

Addendum XXVII descends through closed-web-at-good-word instances whose graph
carrier changes after a splice.  This module packages that varying source
object in one universe-fixed type and proves the purely logical assembly from
a strict-reduction supplier to `ReductiveSystem` and `BaseVerified`.

The supplier is deliberately visible in every headline theorem.  This module
does not construct physical crosscuts (Lean-flag L1), prove the finite profile
audit, reconstruct the shortened closed-web instance, derive a threshold, or
verify the finite base.  In particular, it is a conditional assembly
interface, not the Cell-3 reduction itself.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebReductiveAssembly

open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ReductiveSpine

universe u

/-- One source Cell-3 object with its varying finite simple-graph carrier
hidden inside a universe-fixed package. -/
structure PackedInstance where
  Vertex : Type u
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  graph : SimpleGraph Vertex
  [adjDecidable : DecidableRel graph.Adj]
  boundary : AnnularBoundaryData graph 5
  coloring : graph.EdgeColoring Color
  web : GoertzelV24ClosedWebAtGoodWord.Instance boundary coloring

namespace PackedInstance

/-- The descent measure used in Addendum XXVII. -/
def size (object : PackedInstance.{u}) : Nat :=
  @Fintype.card object.Vertex object.vertexFintype

/-- GWCO says that no packed closed web at a good word exists.  This is the
Cell-3 middle theorem, not yet the trail-general Four-Color statement. -/
def target (_object : PackedInstance.{u}) : Prop := False

/-- The exact carrier-changing output contract of one source splice.  The
output contains a complete new closed-web-at-good-word witness, rather than
only the shortened rotation system. -/
structure StrictReductionCertificate (input : PackedInstance.{u}) where
  output : PackedInstance.{u}
  smaller : output.size < input.size

/-- The sole mathematical supplier consumed by the reductive assembly. -/
def StrictReductionSupplier (threshold : Nat) : Prop :=
  ∀ input : PackedInstance.{u}, threshold < input.size →
    Nonempty (StrictReductionCertificate input)

/-- Choose the certified smaller object above the threshold and leave a base
object unchanged. -/
noncomputable def reduceFrom
    (threshold : Nat) (supplier : StrictReductionSupplier threshold)
    (input : PackedInstance.{u}) : PackedInstance.{u} := by
  classical
  by_cases hlarge : threshold < input.size
  · exact (Classical.choice (supplier input hlarge)).output
  · exact input

theorem reduceFrom_smaller
    (threshold : Nat) (supplier : StrictReductionSupplier threshold)
    (input : PackedInstance.{u}) (_hcounterexample : ¬ input.target)
    (hlarge : threshold < input.size) :
    (reduceFrom threshold supplier input).size < input.size := by
  classical
  simp only [reduceFrom, hlarge, dite_true]
  exact (Classical.choice (supplier input hlarge)).smaller

/-- Counterexample preservation is definitional at the GWCO carrier: every
packed object is itself a forbidden witness, so the target predicate is
`False` on both input and output. -/
theorem reduceFrom_counterexample
    (threshold : Nat) (supplier : StrictReductionSupplier threshold)
    (input : PackedInstance.{u}) (_hcounterexample : ¬ input.target)
    (_hlarge : threshold < input.size) :
    ¬ (reduceFrom threshold supplier input).target := by
  exact not_false

/-- Once source geometry supplies one complete smaller packed witness for
every sufficiently large input, the carrier-changing reductive system has no
further logical field left open. -/
noncomputable def reductiveSystem
    (threshold : Nat) (supplier : StrictReductionSupplier threshold) :
    ReductiveSystem PackedInstance.{u} target where
  size := size
  threshold := threshold
  reduce := reduceFrom threshold supplier
  reduce_smaller := reduceFrom_smaller threshold supplier
  reduce_counterexample := reduceFrom_counterexample threshold supplier

/-- The GWCO universal statement is exactly the route-native bounded base
claim once the strict source reduction supplier is constructed. -/
theorem target_all_iff_baseVerified
    (threshold : Nat) (supplier : StrictReductionSupplier.{u} threshold) :
    (∀ input : PackedInstance.{u}, input.target) ↔
      (reductiveSystem threshold supplier).BaseVerified := by
  let system : ReductiveSystem PackedInstance.{u} target :=
    reductiveSystem threshold supplier
  exact system.target_all_iff_baseVerified

/-- A verified route-native base closes the GWCO descent.  The separate
trail-general assembly is still required for the headline theorem. -/
theorem target_all_of_baseVerified
    (threshold : Nat) (supplier : StrictReductionSupplier.{u} threshold)
    (base : (reductiveSystem threshold supplier).BaseVerified) :
    ∀ input : PackedInstance.{u}, input.target := by
  let system : ReductiveSystem PackedInstance.{u} target :=
    reductiveSystem threshold supplier
  exact system.target_all_of_baseVerified base

end PackedInstance

end GoertzelV24ClosedWebReductiveAssembly

end Mettapedia.GraphTheory.FourColor
