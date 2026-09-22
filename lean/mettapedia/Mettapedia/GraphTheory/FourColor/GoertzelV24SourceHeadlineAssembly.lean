import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mettapedia.GraphTheory.PlanarEmbedding
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebFragmentReindexReductionSupplier
import Mettapedia.GraphTheory.FourColor.GoertzelV24RouteNativeBaseReflection
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

/-!
# Historical closed-web headline assembly

This module states the Four-Color Theorem in the tree's own vocabulary and
proves a conditional implication from four named obligations. This is not
the active headline: see the route correction below. Every open pillar
appears as one explicit hypothesis, so the distance to the headline is
machine-checked rather than estimated.

The chain, from the inside out:

* **GWCO** (proved here from two hypotheses): the two geometric adapters of
  the fragment-reindexed radial dichotomy produce the strict reduction
  supplier at the checked threshold `845970`; a route-native base reflection
  with an empty reachable-good set verifies the base; the spine descent then
  shows **no packed closed web at a good word exists at all**.
* **Normalization** (named obligation, pillars A–C): a graph-backed
  vertex-minimal Tait counterexample yields some packed closed web.
* **Tait bridge** (named obligation, classical layer): if no graph-backed
  vertex-minimal Tait counterexample exists, every finite planar simple
  graph is 4-colorable.  This bundles two separately honest debts: the
  least-counterexample *selection* (a smallest non-Tait-colorable member of
  the bridgeless spherical cubic class must be presented with two-sided
  faces and a graph backing — neither is currently derived in this tree)
  and Tait's classical reduction of vertex 4-colorability to cubic
  3-edge-colorability.

No adapter, reflection datum, audit, normalization, or bridge is
constructed here; each is precisely the open work it names.

**Route correction (25 August 2026).**  The packed target `False` — the
good-word closed-web obstruction — is refuted by verified specimens: the
dodecahedron minus two non-adjacent pentagon caps carries totally closed webs
at good inner words, and so does C30 minus caps 4 and 12.  Consequently the
audit hypothesis below (an empty reachable-necessary set for the closed-web
system at threshold `845970`) is unsatisfiable, and no `V₀` or base
certificate for that system should be pursued.  The *shape* of this chain —
reductive descent to a route-native base, normalization, selection, Tait
bridge — survives unchanged; the reductive system it must be instantiated at
is the Cell-1 corridor-pumping system of the Seed Lemma, with the closed-web
obstruction's purpose recovered by "totally closed ⟹ all strands radial ⟹
menu B".  This module is retained as the template for that re-aim.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SourceHeadlineAssembly

open Mettapedia.GraphTheory
open GoertzelV24ClosedWebReductiveAssembly
open GoertzelV24ClosedWebFragmentReindexReductionSupplier
open GoertzelV24ReductiveSpine
open GoertzelV24ReductiveSpine.ReductiveSystem
open GoertzelV24TwoEdgeCutMinimality

universe u

/-- The headline statement in the tree's own planarity vocabulary: every
finite simple graph with a plane embedding is properly 4-colorable.  The
statement is universe-polymorphic so the headline is not silently weakened
to carriers in `Type 0`. -/
def FourColorStatement : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsPlanar G → G.Colorable 4

noncomputable section

/-- **GWCO from the two route hypotheses.**  Adapters give the strict
reduction supplier at the checked threshold; a route-native reflection with
an empty audit verifies the base; the spine closes the descent.  Since the
packed target is `False`, the conclusion is that no packed closed web at a
good word exists. -/
theorem isEmpty_packedInstance_of_adapters_and_audit
    (widthBound : Nat)
    (adapters : FragmentReindexRadialReductionAdapters.{u} widthBound)
    {State : Type*}
    (reflection :
      RouteNativeBaseReflection
        (PackedInstance.reductiveSystem 845970
          (strictReductionSupplier_845970_of_fragmentReindexRadialAdapters
            widthBound adapters))
        State)
    (haudit :
      ∀ state ∈ reflection.reachable, ¬ reflection.Necessary state) :
    IsEmpty PackedInstance.{u} := by
  refine ⟨fun input => ?_⟩
  exact reflection.target_all_of_audit haudit input

/-- **Normalization obligation** (pillars A–C): the literal formation work —
annulus, corridor, and good word — packages a graph-backed vertex-minimal
Tait counterexample as a packed closed web at a good word. -/
def NormalizationObligation : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (graphData : SimpleGraphDartRotation.Data G)
    (_minimal : GraphBackedVertexMinimalTaitCounterexample graphData),
    Nonempty PackedInstance.{u}

/-- With GWCO and normalization, no graph-backed vertex-minimal Tait
counterexample exists. -/
theorem no_vertexMinimalTaitCounterexample_of_adapters_and_audit
    (widthBound : Nat)
    (adapters : FragmentReindexRadialReductionAdapters.{u} widthBound)
    {State : Type*}
    (reflection :
      RouteNativeBaseReflection
        (PackedInstance.reductiveSystem 845970
          (strictReductionSupplier_845970_of_fragmentReindexRadialAdapters
            widthBound adapters))
        State)
    (haudit :
      ∀ state ∈ reflection.reachable, ¬ reflection.Necessary state)
    (normalization : NormalizationObligation.{u}) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj]
      (graphData : SimpleGraphDartRotation.Data G),
      GraphBackedVertexMinimalTaitCounterexample graphData → False := by
  intro V _ _ G _ graphData minimal
  have hempty :=
    isEmpty_packedInstance_of_adapters_and_audit
      widthBound adapters reflection haudit
  exact hempty.false (normalization graphData minimal).some

/-- **Tait bridge obligation** (classical layer): absence of a graph-backed
vertex-minimal Tait counterexample implies the headline statement.  Its two
honest sub-debts — least-counterexample selection with two-sided faces and
graph backing, and Tait's reduction of vertex coloring to cubic edge
coloring — are documented in the module header. -/
def TaitBridgeObligation : Prop :=
  (∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj]
      (graphData : SimpleGraphDartRotation.Data G),
      GraphBackedVertexMinimalTaitCounterexample graphData → False) →
    FourColorStatement.{u}

/-- **The headline.**  The Four-Color Theorem follows from exactly four named
obligations: the two geometric adapters (pillar C), the route-native base
reflection with its empty audit (pillar F), the normalization packaging
(pillars A–C), and the classical Tait bridge.  Everything else is proved. -/
theorem fourColorStatement_of_route
    (widthBound : Nat)
    (adapters : FragmentReindexRadialReductionAdapters.{u} widthBound)
    {State : Type*}
    (reflection :
      RouteNativeBaseReflection
        (PackedInstance.reductiveSystem 845970
          (strictReductionSupplier_845970_of_fragmentReindexRadialAdapters
            widthBound adapters))
        State)
    (haudit :
      ∀ state ∈ reflection.reachable, ¬ reflection.Necessary state)
    (normalization : NormalizationObligation.{u})
    (bridge : TaitBridgeObligation.{u}) :
    FourColorStatement.{u} := by
  refine bridge ?_
  intro V _ _ G _ graphData minimal
  exact no_vertexMinimalTaitCounterexample_of_adapters_and_audit
    widthBound adapters reflection haudit normalization graphData minimal

end

end GoertzelV24SourceHeadlineAssembly

end Mettapedia.GraphTheory.FourColor
