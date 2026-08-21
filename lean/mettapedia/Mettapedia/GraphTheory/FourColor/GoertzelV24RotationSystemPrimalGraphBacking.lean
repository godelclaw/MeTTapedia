import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationSystemPrimalEdgePresentation

/-!
# Graph backing for endpoint-simple rotation systems

The reductive splice is first constructed as an abstract rotation system whose
vertex and edge carriers change across the cut.  A closed-web reduction,
however, must return a rotation on an actual simple graph.  This file closes
the dart-and-rotation part of that representation junction.

For a rotation system with injective endpoint sets, its literal darts are
canonically equivalent to the darts of its computed primal simple graph.  The
equivalence preserves reversal, vertex rotation, and hence facial steps.  It
therefore supplies graph-backed rotation data without postulating a new cyclic
order.  Specializing the generic construction to an ordered-cut splice uses
the existing finite `OrderedCutEndpointSimple` test.

This is carrier plumbing, not the source construction of that finite test.  In
particular, it neither derives endpoint simplicity from arbitrary local
crosscuts nor transports the two named hole faces.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationSystemPrimalGraphBacking

open GoertzelV24FaceDualConnectedness
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RotationSystemPrimalEdgePresentation
open GoertzelV24RotationSystemPrimalEdgePresentation.OrderedCutSpliceData
open GoertzelV24SpliceUnification
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

local instance rotationPrimalGraphAdjDecidable (RS : RotationSystem V E) :
    DecidableRel (rotationPrimalGraph RS).Adj :=
  Classical.decRel _

/-- Send a literal rotation-system dart to the correspondingly oriented dart
of the computed primal simple graph. -/
def primalDart (RS : RotationSystem V E) (dart : RS.D) :
    (rotationPrimalGraph RS).Dart :=
  ⟨(RS.vertOf dart, RS.vertOf (RS.alpha dart)), ⟨dart, rfl, rfl⟩⟩

@[simp] theorem primalDart_fst (RS : RotationSystem V E) (dart : RS.D) :
    (primalDart RS dart).fst = RS.vertOf dart :=
  rfl

@[simp] theorem primalDart_snd (RS : RotationSystem V E) (dart : RS.D) :
    (primalDart RS dart).snd = RS.vertOf (RS.alpha dart) :=
  rfl

/-- Every oriented primal edge is represented by a literal dart. -/
theorem primalDart_surjective (RS : RotationSystem V E) :
    Function.Surjective (primalDart RS) := by
  intro dart
  rcases dart.adj with ⟨source, hsource, htarget⟩
  refine ⟨source, ?_⟩
  exact SimpleGraph.Dart.ext _ _ (Prod.ext hsource htarget)

/-- Endpoint injectivity rules out the only possible collision between two
literal darts representing the same oriented primal edge. -/
theorem primalDart_injective (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints) :
    Function.Injective (primalDart RS) := by
  intro left right heq
  have hfst : RS.vertOf left = RS.vertOf right :=
    congrArg (fun dart => dart.toProd.1) heq
  have hsnd : RS.vertOf (RS.alpha left) = RS.vertOf (RS.alpha right) :=
    congrArg (fun dart => dart.toProd.2) heq
  have hends : RS.endpoints (RS.edgeOf left) =
      RS.endpoints (RS.edgeOf right) := by
    rw [RS.endpoints_eq_pair_of_mem (RS.mem_dartsOn.2 rfl),
      RS.endpoints_eq_pair_of_mem (RS.mem_dartsOn.2 rfl)]
    simp [hfst, hsnd]
  have hedge : RS.edgeOf left = RS.edgeOf right := hinjective hends
  rcases RS.edge_fiber_two_cases
      (e := RS.edgeOf left) (d := left) (y := right) rfl hedge.symm with
    hsame | hreverse
  · exact hsame.symm
  · exfalso
    exact RS.no_self_loops left
      (hfst.trans (congrArg RS.vertOf hreverse))

/-- Literal darts and graph darts are canonically equivalent once parallel
endpoint pairs have been excluded. -/
def primalDartEquiv (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints) :
    RS.D ≃ (rotationPrimalGraph RS).Dart :=
  Equiv.ofBijective (primalDart RS)
    ⟨primalDart_injective RS hinjective, primalDart_surjective RS⟩

@[simp] theorem primalDartEquiv_apply (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints) (dart : RS.D) :
    primalDartEquiv RS hinjective dart = primalDart RS dart :=
  rfl

@[simp] theorem primalDartEquiv_fst (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints) (dart : RS.D) :
    (primalDartEquiv RS hinjective dart).fst = RS.vertOf dart :=
  rfl

@[simp] theorem primalDartEquiv_symm_fst (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (dart : (rotationPrimalGraph RS).Dart) :
    RS.vertOf ((primalDartEquiv RS hinjective).symm dart) = dart.fst := by
  rw [← primalDartEquiv_fst RS hinjective, Equiv.apply_symm_apply]

/-- Dart reversal is preserved definitionally at the endpoints. -/
@[simp] theorem primalDartEquiv_alpha (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints) (dart : RS.D) :
    primalDartEquiv RS hinjective (RS.alpha dart) =
      (primalDartEquiv RS hinjective dart).symm := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · rfl
  · exact congrArg RS.vertOf (RS.alpha_involutive dart)

/-- Transport the literal vertex rotation to the computed primal graph. -/
def graphData (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints) :
    SimpleGraphDartRotation.Data (rotationPrimalGraph RS) where
  vertexRotation := (primalDartEquiv RS hinjective).permCongr RS.rho
  vertexRotation_fst := by
    intro dart
    change (primalDartEquiv RS hinjective
      (RS.rho ((primalDartEquiv RS hinjective).symm dart))).fst = dart.fst
    rw [primalDartEquiv_fst, RS.vert_rho, primalDartEquiv_symm_fst]
  outer := primalDartEquiv RS hinjective RS.outer

/-- The graph-backed vertex rotation is the transported literal rotation. -/
@[simp] theorem primalDartEquiv_rho (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints) (dart : RS.D) :
    primalDartEquiv RS hinjective (RS.rho dart) =
      (graphData RS hinjective).vertexRotation
        (primalDartEquiv RS hinjective dart) := by
  change primalDartEquiv RS hinjective (RS.rho dart) =
    ((primalDartEquiv RS hinjective).permCongr RS.rho)
      (primalDartEquiv RS hinjective dart)
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]

/-- Facial steps are preserved.  The right-hand side is the graph-backed
formula `rho (alpha dart)`; spelling it this way avoids depending on a
particular decidable-adjacency instance. -/
@[simp] theorem primalDartEquiv_phi (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints) (dart : RS.D) :
    primalDartEquiv RS hinjective (RS.phi dart) =
      (graphData RS hinjective).vertexRotation
        (primalDartEquiv RS hinjective dart).symm := by
  change primalDartEquiv RS hinjective (RS.rho (RS.alpha dart)) =
    (graphData RS hinjective).vertexRotation
      (primalDartEquiv RS hinjective dart).symm
  rw [← primalDartEquiv_alpha RS hinjective,
    ← primalDartEquiv_rho RS hinjective]

namespace OrderedCutSpliceData

variable {RS : RotationSystem V E}
  {n terminalCount faceFragmentCount : Nat}

/-- The explicit finite endpoint test is sufficient to graph-back the entire
ordered-cut splice output, not merely to identify its edge carrier. -/
def outputGraphData
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (hambient : Function.Injective RS.endpoints)
    (hsimple : OrderedCutEndpointSimple RS data.keep
      data.left.crossingEdge data.right.crossingEdge
      data.leftCrosses data.rightCrosses) :
    SimpleGraphDartRotation.Data (rotationPrimalGraph data.output) :=
  graphData data.output
    (output_endpoints_injective data hambient hsimple)

end OrderedCutSpliceData

end

end GoertzelV24RotationSystemPrimalGraphBacking

end Mettapedia.GraphTheory.FourColor
