import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceEscapeStateOneZeroFlow

/-! Root-normalized facial coordinates for the canonical one-zero escape
flows and their reentry discrepancies. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InducedChainExtension
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}

namespace RotationOrderedFusionEscapeColorState

/-- A facial coefficient pair for an ambient color chain, normalized to
vanish at one chosen quotient face. -/
structure RootedFacialCoordinates
    (root : OrbitFace graphData.toRotationSystem)
    (chain : G.edgeSet → Color) where
  potential : OrbitFace graphData.toRotationSystem → Color
  root_zero : potential root = 0
  boundary_first :
    orbitFaceBoundaryLinearMap graphData.toRotationSystem
        (fun face => (potential face).1) =
      fun edge => (chain edge).1
  boundary_second :
    orbitFaceBoundaryLinearMap graphData.toRotationSystem
        (fun face => (potential face).2) =
      fun edge => (chain edge).2

/-- Add the value at the root to every binary face label.  In characteristic
two this makes the root label zero. -/
def normalizeFaceLabels
    (root : OrbitFace graphData.toRotationSystem)
    (labels : OrbitFace graphData.toRotationSystem → F2) :
    OrbitFace graphData.toRotationSystem → F2 :=
  fun face => labels face + labels root

@[simp]
theorem normalizeFaceLabels_root
    (root : OrbitFace graphData.toRotationSystem)
    (labels : OrbitFace graphData.toRotationSystem → F2) :
    normalizeFaceLabels root labels root = 0 :=
  zmod2_add_self _

/-- Root normalization does not change a facial boundary. -/
theorem orbitFaceBoundaryLinearMap_normalizeFaceLabels
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (root : OrbitFace graphData.toRotationSystem)
    (labels : OrbitFace graphData.toRotationSystem → F2) :
    orbitFaceBoundaryLinearMap graphData.toRotationSystem
        (normalizeFaceLabels root labels) =
      orbitFaceBoundaryLinearMap graphData.toRotationSystem labels := by
  let RS := graphData.toRotationSystem
  have hdual :
      (interiorDualGraph (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).Connected :=
    orbitFaceInteriorDual_connected RS minimal.spherical.cubic
      minimal.primalConnected minimal.vertexRotationCyclic
  have hconstant : (fun _ : OrbitFace RS => labels root) ∈
      LinearMap.ker (orbitFaceBoundaryLinearMap RS) :=
    (mem_ker_orbitFaceBoundaryLinearMap_iff_constant RS
      minimal.facesTwoSided hdual _).2 (fun _ _ => rfl)
  have hconstantBoundary :
      orbitFaceBoundaryLinearMap RS
          (fun _ : OrbitFace RS => labels root) = 0 :=
    (LinearMap.mem_ker).1 hconstant
  change orbitFaceBoundaryLinearMap RS
      (labels + fun _ : OrbitFace RS => labels root) =
    orbitFaceBoundaryLinearMap RS labels
  rw [map_add, hconstantBoundary, add_zero]

/-- Every ambient graph flow has root-normalized facial coordinates. -/
theorem exists_rootedFacialCoordinates
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (root : OrbitFace graphData.toRotationSystem)
    {chain : G.edgeSet → Color}
    (hflow : IsGraphFlow G chain) :
    Nonempty (RootedFacialCoordinates
      (graphData := graphData) root chain) := by
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  have hdual : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Connected :=
    orbitFaceInteriorDual_connected graphData.toRotationSystem
      minimal.spherical.cubic minimal.primalConnected
      minimal.vertexRotationCyclic
  rcases
      (isGraphFlow_iff_exists_orbitFaceBoundary_coefficients graphData
        minimal.facesTwoSided hdual hconnected minimal.spherical).1 hflow with
    ⟨first, second, hfirst, hsecond⟩
  refine ⟨⟨fun face =>
      (normalizeFaceLabels root first face,
        normalizeFaceLabels root second face), ?_, ?_, ?_⟩⟩
  · apply Prod.ext <;> simp
  · simpa only using
      (orbitFaceBoundaryLinearMap_normalizeFaceLabels
        (minimal := minimal) root first).trans hfirst
  · simpa only using
      (orbitFaceBoundaryLinearMap_normalizeFaceLabels
        (minimal := minimal) root second).trans hsecond

/-- Two binary facial label fields with equal boundary and equal zero root
are identical. -/
theorem faceLabels_eq_of_root_zero_of_boundary_eq
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (root : OrbitFace graphData.toRotationSystem)
    (first second : OrbitFace graphData.toRotationSystem → F2)
    (hfirstRoot : first root = 0)
    (hsecondRoot : second root = 0)
    (hboundary :
      orbitFaceBoundaryLinearMap graphData.toRotationSystem first =
        orbitFaceBoundaryLinearMap graphData.toRotationSystem second) :
    first = second := by
  let RS := graphData.toRotationSystem
  let difference := first + second
  have hkernel : difference ∈
      LinearMap.ker (orbitFaceBoundaryLinearMap RS) := by
    rw [LinearMap.mem_ker]
    change orbitFaceBoundaryLinearMap RS (first + second) = 0
    rw [map_add, hboundary]
    funext edge
    exact zmod2_add_self _
  have hdual :
      (interiorDualGraph (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).Connected :=
    orbitFaceInteriorDual_connected RS minimal.spherical.cubic
      minimal.primalConnected minimal.vertexRotationCyclic
  have hconstant :=
    (mem_ker_orbitFaceBoundaryLinearMap_iff_constant RS
      minimal.facesTwoSided hdual difference).1 hkernel
  funext face
  have hface := hconstant face root
  change first face + second face = first root + second root at hface
  rw [hfirstRoot, hsecondRoot, zero_add] at hface
  calc
    first face = first face + 0 := by simp
    _ = first face + (first face + second face) := by rw [hface]
    _ = second face := by
      rw [← add_assoc, zmod2_add_self, zero_add]

/-- Root-normalized facial coordinates of a fixed chain are unique. -/
theorem RootedFacialCoordinates.potential_eq
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {root : OrbitFace graphData.toRotationSystem}
    {chain : G.edgeSet → Color}
    (first second : RootedFacialCoordinates
      (graphData := graphData) root chain) :
    first.potential = second.potential := by
  apply funext
  intro face
  apply Prod.ext
  · have hfirstRoot := congrArg Prod.fst first.root_zero
    have hsecondRoot := congrArg Prod.fst second.root_zero
    have heq := faceLabels_eq_of_root_zero_of_boundary_eq
      (minimal := minimal) root
      (fun f => (first.potential f).1)
      (fun f => (second.potential f).1)
      (by simpa using hfirstRoot) (by simpa using hsecondRoot)
      (first.boundary_first.trans second.boundary_first.symm)
    exact congrFun heq face
  · have hfirstRoot := congrArg Prod.snd first.root_zero
    have hsecondRoot := congrArg Prod.snd second.root_zero
    have heq := faceLabels_eq_of_root_zero_of_boundary_eq
      (minimal := minimal) root
      (fun f => (first.potential f).2)
      (fun f => (second.potential f).2)
      (by simpa using hfirstRoot) (by simpa using hsecondRoot)
      (first.boundary_second.trans second.boundary_second.symm)
    exact congrFun heq face

/-- The canonical root-normalized facial coordinates of a graph flow. -/
noncomputable def rootedFacialCoordinates
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (root : OrbitFace graphData.toRotationSystem)
    {chain : G.edgeSet → Color}
    (hflow : IsGraphFlow G chain) :
    RootedFacialCoordinates (graphData := graphData) root chain :=
  Classical.choice (exists_rootedFacialCoordinates
    (minimal := minimal) root hflow)

@[simp]
theorem rootedFacialCoordinates_root
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (root : OrbitFace graphData.toRotationSystem)
    {chain : G.edgeSet → Color}
    (hflow : IsGraphFlow G chain) :
    (rootedFacialCoordinates
      (minimal := minimal) root hflow).potential root = 0 :=
  (rootedFacialCoordinates minimal root hflow).root_zero

/-- Pointwise addition of normalized potentials represents addition of their
ambient chains. -/
def RootedFacialCoordinates.add
    {root : OrbitFace graphData.toRotationSystem}
    {left right : G.edgeSet → Color}
    (leftCoordinates : RootedFacialCoordinates
      (graphData := graphData) root left)
    (rightCoordinates : RootedFacialCoordinates
      (graphData := graphData) root right) :
    RootedFacialCoordinates (graphData := graphData) root (left + right) where
  potential := leftCoordinates.potential + rightCoordinates.potential
  root_zero := by
    change leftCoordinates.potential root +
      rightCoordinates.potential root = 0
    rw [leftCoordinates.root_zero, rightCoordinates.root_zero, zero_add]
  boundary_first := by
    change orbitFaceBoundaryLinearMap graphData.toRotationSystem
        ((fun face => (leftCoordinates.potential face).1) +
          fun face => (rightCoordinates.potential face).1) =
      (fun edge => (left edge).1) + fun edge => (right edge).1
    rw [map_add, leftCoordinates.boundary_first,
      rightCoordinates.boundary_first]
  boundary_second := by
    change orbitFaceBoundaryLinearMap graphData.toRotationSystem
        ((fun face => (leftCoordinates.potential face).2) +
          fun face => (rightCoordinates.potential face).2) =
      (fun edge => (left edge).2) + fun edge => (right edge).2
    rw [map_add, leftCoordinates.boundary_second,
      rightCoordinates.boundary_second]

/-- Canonical normalized facial coordinates are exactly additive. -/
theorem rootedFacialCoordinates_add_potential
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (root : OrbitFace graphData.toRotationSystem)
    {left right : G.edgeSet → Color}
    (hleft : IsGraphFlow G left)
    (hright : IsGraphFlow G right) :
    (rootedFacialCoordinates (minimal := minimal) root
        (hleft.add hright)).potential =
      (rootedFacialCoordinates (minimal := minimal) root hleft).potential +
        (rootedFacialCoordinates (minimal := minimal) root hright).potential := by
  exact RootedFacialCoordinates.potential_eq
    (minimal := minimal)
    (rootedFacialCoordinates minimal root (hleft.add hright))
    ((rootedFacialCoordinates minimal root hleft).add
      (rootedFacialCoordinates minimal root hright))

/-- The distinguished quotient face used to remove the global constant
ambiguity from ambient facial coefficients. -/
def ambientRootFace : OrbitFace graphData.toRotationSystem :=
  dartOrbitFace graphData.toRotationSystem graphData.toRotationSystem.outer

/-- The unique root-normalized facial potential of an admissible state's
canonical singleton-zero ambient flow. -/
def AdmissibleState.oneZeroFacePotential
    (state : AdmissibleState
      (graphData := graphData) (minimal := minimal)) :
    OrbitFace graphData.toRotationSystem → Color :=
  (rootedFacialCoordinates (minimal := minimal)
    (ambientRootFace (graphData := graphData))
    state.oneZeroAmbientFlow_isCDLGoodFlow.1).potential

@[simp]
theorem AdmissibleState.oneZeroFacePotential_root
    (state : AdmissibleState
      (graphData := graphData) (minimal := minimal)) :
    state.oneZeroFacePotential
        (ambientRootFace (graphData := graphData)) = 0 :=
  rootedFacialCoordinates_root minimal
    (ambientRootFace (graphData := graphData))
    state.oneZeroAmbientFlow_isCDLGoodFlow.1

/-- The first coordinate of a state's normalized potential has exactly the
first coordinate of its singleton-zero ambient flow as boundary. -/
theorem AdmissibleState.oneZeroFacePotential_boundary_first
    (state : AdmissibleState
      (graphData := graphData) (minimal := minimal)) :
    orbitFaceBoundaryLinearMap graphData.toRotationSystem
        (fun face => (state.oneZeroFacePotential face).1) =
      fun edge => (state.oneZeroAmbientFlow edge).1 := by
  exact (rootedFacialCoordinates minimal
    (ambientRootFace (graphData := graphData))
    state.oneZeroAmbientFlow_isCDLGoodFlow.1).boundary_first

/-- The second coordinate of a state's normalized potential has exactly the
second coordinate of its singleton-zero ambient flow as boundary. -/
theorem AdmissibleState.oneZeroFacePotential_boundary_second
    (state : AdmissibleState
      (graphData := graphData) (minimal := minimal)) :
    orbitFaceBoundaryLinearMap graphData.toRotationSystem
        (fun face => (state.oneZeroFacePotential face).2) =
      fun edge => (state.oneZeroAmbientFlow edge).2 := by
  exact (rootedFacialCoordinates minimal
    (ambientRootFace (graphData := graphData))
    state.oneZeroAmbientFlow_isCDLGoodFlow.1).boundary_second

/-- The exact normalized coefficient pair of the canonical discrepancy
between two admissible states. -/
def oneZeroReentryFacePotential
    (source target : AdmissibleState
      (graphData := graphData) (minimal := minimal)) :
    OrbitFace graphData.toRotationSystem → Color :=
  source.oneZeroFacePotential + target.oneZeroFacePotential

@[simp]
theorem oneZeroReentryFacePotential_root
    (source target : AdmissibleState
      (graphData := graphData) (minimal := minimal)) :
    oneZeroReentryFacePotential source target
        (ambientRootFace (graphData := graphData)) = 0 := by
  change source.oneZeroFacePotential (ambientRootFace) +
    target.oneZeroFacePotential (ambientRootFace) = 0
  rw [source.oneZeroFacePotential_root, target.oneZeroFacePotential_root,
    zero_add]

/-- The first normalized facial coordinate has exactly the first coordinate
of the global one-zero reentry discrepancy as boundary. -/
theorem oneZeroReentryFacePotential_boundary_first
    (source target : AdmissibleState
      (graphData := graphData) (minimal := minimal)) :
    orbitFaceBoundaryLinearMap graphData.toRotationSystem
        (fun face => (oneZeroReentryFacePotential source target face).1) =
      fun edge => (oneZeroReentryDiscrepancy source target edge).1 := by
  let sourceFlow := source.oneZeroAmbientFlow_isCDLGoodFlow.1
  let targetFlow := target.oneZeroAmbientFlow_isCDLGoodFlow.1
  change orbitFaceBoundaryLinearMap graphData.toRotationSystem
      ((fun face =>
          ((rootedFacialCoordinates minimal ambientRootFace
            sourceFlow).potential face).1) +
        fun face =>
          ((rootedFacialCoordinates minimal ambientRootFace
            targetFlow).potential face).1) =
    (fun edge => (source.oneZeroAmbientFlow edge).1) +
      fun edge => (target.oneZeroAmbientFlow edge).1
  rw [map_add,
    (rootedFacialCoordinates minimal ambientRootFace
      sourceFlow).boundary_first,
    (rootedFacialCoordinates minimal ambientRootFace
      targetFlow).boundary_first]

/-- The second normalized facial coordinate has exactly the second coordinate
of the global one-zero reentry discrepancy as boundary. -/
theorem oneZeroReentryFacePotential_boundary_second
    (source target : AdmissibleState
      (graphData := graphData) (minimal := minimal)) :
    orbitFaceBoundaryLinearMap graphData.toRotationSystem
        (fun face => (oneZeroReentryFacePotential source target face).2) =
      fun edge => (oneZeroReentryDiscrepancy source target edge).2 := by
  let sourceFlow := source.oneZeroAmbientFlow_isCDLGoodFlow.1
  let targetFlow := target.oneZeroAmbientFlow_isCDLGoodFlow.1
  change orbitFaceBoundaryLinearMap graphData.toRotationSystem
      ((fun face =>
          ((rootedFacialCoordinates minimal ambientRootFace
            sourceFlow).potential face).2) +
        fun face =>
          ((rootedFacialCoordinates minimal ambientRootFace
            targetFlow).potential face).2) =
    (fun edge => (source.oneZeroAmbientFlow edge).2) +
      fun edge => (target.oneZeroAmbientFlow edge).2
  rw [map_add,
    (rootedFacialCoordinates minimal ambientRootFace
      sourceFlow).boundary_second,
    (rootedFacialCoordinates minimal ambientRootFace
      targetFlow).boundary_second]

/-- Every actual reentry has a nonzero normalized facial coefficient pair. -/
theorem AdmissibleReentry.oneZeroReentryFacePotential_ne_zero
    {source target : AdmissibleState
      (graphData := graphData) (minimal := minimal)}
    (step : AdmissibleReentry source target) :
    oneZeroReentryFacePotential source target ≠ 0 := by
  intro hzero
  apply step.oneZeroReentryDiscrepancy_ne_zeroChain
  funext edge
  apply Prod.ext
  · have hboundary := congrFun
      (oneZeroReentryFacePotential_boundary_first source target) edge
    rw [hzero] at hboundary
    simpa [zeroChain] using hboundary.symm
  · have hboundary := congrFun
      (oneZeroReentryFacePotential_boundary_second source target) edge
    rw [hzero] at hboundary
    simpa [zeroChain] using hboundary.symm

/-- A nonempty reentry chain together with the exact sum of its normalized
facial coefficient pairs. -/
inductive ReentryFacialCoordinateChain :
    AdmissibleState (graphData := graphData) (minimal := minimal) →
    AdmissibleState (graphData := graphData) (minimal := minimal) →
    (OrbitFace graphData.toRotationSystem → Color) → Prop
  | single {source target}
      (step : AdmissibleReentry source target) :
      ReentryFacialCoordinateChain source target
        (oneZeroReentryFacePotential source target)
  | tail {source middle target total}
      (path : ReentryFacialCoordinateChain source middle total)
      (step : AdmissibleReentry middle target) :
      ReentryFacialCoordinateChain source target
        (total + oneZeroReentryFacePotential middle target)

namespace ReentryFacialCoordinateChain

/-- Every nonempty stateful reentry path has an exact normalized facial
coordinate sum. -/
theorem exists_of_transGen
    {source target : AdmissibleState
      (graphData := graphData) (minimal := minimal)}
    (path : Relation.TransGen
      (AdmissibleReentry (graphData := graphData) (minimal := minimal))
      source target) :
    ∃ total : OrbitFace graphData.toRotationSystem → Color,
      ReentryFacialCoordinateChain source target total := by
  induction path with
  | single step =>
      exact ⟨oneZeroReentryFacePotential _ _, .single step⟩
  | tail _ step ih =>
      rcases ih with ⟨total, htotal⟩
      exact ⟨total + oneZeroReentryFacePotential _ _,
        .tail htotal step⟩

/-- Intermediate state potentials cancel exactly, leaving the sum of the
two endpoint potentials. -/
theorem eq_endpoint_potentials
    {source target : AdmissibleState
      (graphData := graphData) (minimal := minimal)}
    {total : OrbitFace graphData.toRotationSystem → Color}
    (path : ReentryFacialCoordinateChain source target total) :
    total = source.oneZeroFacePotential + target.oneZeroFacePotential := by
  induction path with
  | single _ => rfl
  | tail path _ ih =>
      rw [ih]
      simp only [oneZeroReentryFacePotential]
      rw [add_assoc, chain_add_self_add]

/-- The first boundary coordinate of an accumulated potential is exactly
the first coordinate of the endpoint one-zero flow difference. -/
theorem boundary_first_eq_endpoint_discrepancy
    {source target : AdmissibleState
      (graphData := graphData) (minimal := minimal)}
    {total : OrbitFace graphData.toRotationSystem → Color}
    (path : ReentryFacialCoordinateChain source target total) :
    orbitFaceBoundaryLinearMap graphData.toRotationSystem
        (fun face => (total face).1) =
      fun edge =>
        (source.oneZeroAmbientFlow edge +
          target.oneZeroAmbientFlow edge).1 := by
  rw [path.eq_endpoint_potentials]
  change orbitFaceBoundaryLinearMap graphData.toRotationSystem
      ((fun face => (source.oneZeroFacePotential face).1) +
        fun face => (target.oneZeroFacePotential face).1) =
    (fun edge => (source.oneZeroAmbientFlow edge).1) +
      fun edge => (target.oneZeroAmbientFlow edge).1
  rw [map_add, source.oneZeroFacePotential_boundary_first,
    target.oneZeroFacePotential_boundary_first]

/-- The second boundary coordinate of an accumulated potential is exactly
the second coordinate of the endpoint one-zero flow difference. -/
theorem boundary_second_eq_endpoint_discrepancy
    {source target : AdmissibleState
      (graphData := graphData) (minimal := minimal)}
    {total : OrbitFace graphData.toRotationSystem → Color}
    (path : ReentryFacialCoordinateChain source target total) :
    orbitFaceBoundaryLinearMap graphData.toRotationSystem
        (fun face => (total face).2) =
      fun edge =>
        (source.oneZeroAmbientFlow edge +
          target.oneZeroAmbientFlow edge).2 := by
  rw [path.eq_endpoint_potentials]
  change orbitFaceBoundaryLinearMap graphData.toRotationSystem
      ((fun face => (source.oneZeroFacePotential face).2) +
        fun face => (target.oneZeroFacePotential face).2) =
    (fun edge => (source.oneZeroAmbientFlow edge).2) +
      fun edge => (target.oneZeroAmbientFlow edge).2
  rw [map_add, source.oneZeroFacePotential_boundary_second,
    target.oneZeroFacePotential_boundary_second]

/-- Every accumulated facial-coordinate chain remains normalized at the
distinguished root face. -/
theorem apply_ambientRootFace_eq_zero
    {source target : AdmissibleState
      (graphData := graphData) (minimal := minimal)}
    {total : OrbitFace graphData.toRotationSystem → Color}
    (path : ReentryFacialCoordinateChain source target total) :
    total (ambientRootFace (graphData := graphData)) = 0 := by
  rw [path.eq_endpoint_potentials]
  change source.oneZeroFacePotential ambientRootFace +
    target.oneZeroFacePotential ambientRootFace = 0
  rw [source.oneZeroFacePotential_root, target.oneZeroFacePotential_root,
    zero_add]

/-- The accumulated normalized facial coefficient pair of every nonempty
closed reentry orbit is exactly zero. -/
theorem eq_zero_of_closed
    {state : AdmissibleState
      (graphData := graphData) (minimal := minimal)}
    {total : OrbitFace graphData.toRotationSystem → Color}
    (path : ReentryFacialCoordinateChain state state total) :
    total = 0 := by
  rw [path.eq_endpoint_potentials]
  funext face
  exact color_add_self _

/-- Every closed stateful reentry orbit admits an exact facial-coordinate
chain whose sum vanishes. -/
theorem exists_eq_zero_of_transGen_cycle
    {state : AdmissibleState
      (graphData := graphData) (minimal := minimal)}
    (cycle : Relation.TransGen
      (AdmissibleReentry (graphData := graphData) (minimal := minimal))
      state state) :
    ∃ total : OrbitFace graphData.toRotationSystem → Color,
      ReentryFacialCoordinateChain state state total ∧ total = 0 := by
  rcases exists_of_transGen cycle with ⟨total, path⟩
  exact ⟨total, path, path.eq_zero_of_closed⟩

end ReentryFacialCoordinateChain

end RotationOrderedFusionEscapeColorState

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
