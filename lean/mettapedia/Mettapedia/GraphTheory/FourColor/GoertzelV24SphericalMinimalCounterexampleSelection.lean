import Mettapedia.GraphTheory.FourColor.GoertzelV24BridgelessFaceTwoSided
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalGraphBackedPresentation
import Mettapedia.GraphTheory.FourColor.GoertzelV24StellarTaitReduction

/-!
# Minimal-counterexample selection for the genuine spherical headline

This is the M0 consumer used by the repaired compositional route.  It never
mentions the legacy `IsPlanar` predicate and it does not import the refuted
closed-web headline.  Instead it performs the ordinary least-counterexample
argument directly in the cap-stable rotation-system class.

Two facts that used to appear as hypotheses are now constructed internally:

* bridge-freeness plus the spherical Euler equation gives two-sided faces;
* minimality excludes parallel edges, so the least rotation-system
  counterexample has a canonical simple-graph backing.

Thus the only input exposed to the compositional core is the statement that
no graph-backed vertex-minimal Tait counterexample exists.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SphericalMinimalCounterexampleSelection

open GoertzelV24BridgelessFaceTwoSided
open GoertzelV24MinimalGraphBackedPresentation
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24StellarTaitReduction
open GoertzelV24TwoEdgeCutMinimality

noncomputable section

universe u

/-- The exact downstream proposition that the compositional M1--M3 core
must establish. -/
def NoGraphBackedVertexMinimalTaitCounterexample : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (graphData : SimpleGraphDartRotation.Data G),
    GraphBackedVertexMinimalTaitCounterexample graphData → False

/-- Vertex counts realized by counterexamples in the complete cap-stable
rotation-system class. -/
def counterexampleVertexCounts : Set Nat :=
  {count | ∃ (V E : Type u),
    ∃ (_ : Fintype V) (_ : DecidableEq V)
      (_ : Fintype E) (_ : DecidableEq E),
    ∃ RS : RotationSystem.{u, u, u} V E,
      Nonempty (BridgelessSphericalCubicMapData RS) ∧
        ¬ RotationSystemTaitColorable RS ∧ Fintype.card V = count}

/-- If the compositional core eliminates graph-backed vertex-minimal
counterexamples, every bridgeless spherical cubic rotation map is Tait
colourable.  Leastness, two-sidedness and graph backing are all constructed
inside this theorem. -/
theorem everyBridgelessSphericalCubicTaitColorable_of_no_minimal
    (hnominimal : NoGraphBackedVertexMinimalTaitCounterexample.{u}) :
    EveryBridgelessSphericalCubicTaitColorable.{u} := by
  intro V E _ _ _ _ RS hclass
  by_contra hnotColorable
  classical
  have hnonempty : (counterexampleVertexCounts.{u}).Nonempty :=
    ⟨Fintype.card V,
      V, E, inferInstance, inferInstance, inferInstance, inferInstance,
      RS, ⟨hclass⟩, hnotColorable, rfl⟩
  obtain ⟨Vmin, Emin, iVmin, iVminDec, iEmin, iEminDec,
      RSmin, ⟨hclassMin⟩, hnotMin, hcardMin⟩ :=
    Nat.sInf_mem hnonempty
  have hsmaller :
      ∀ {V' E' : Type u}
        [Fintype V'] [DecidableEq V'] [Fintype E'] [DecidableEq E']
        (candidate : RotationSystem.{u, u, u} V' E'),
        Fintype.card V' < Fintype.card Vmin →
        BridgelessSphericalCubicMapData candidate →
        RotationSystemTaitColorable candidate := by
    intro V' E' _ _ _ _ candidate hcard hcandidate
    by_contra hnotCandidate
    have hmember : Fintype.card V' ∈ counterexampleVertexCounts.{u} :=
      ⟨V', E', inferInstance, inferInstance, inferInstance, inferInstance,
        candidate, ⟨hcandidate⟩, hnotCandidate, rfl⟩
    have hleast := Nat.sInf_le hmember
    rw [hcardMin] at hcard
    omega
  have htwoSided : OrbitFacesTwoSided RSmin :=
    GoertzelV24BridgelessFaceTwoSided.BridgelessSphericalCubicMapData.orbitFacesTwoSided
      RSmin hclassMin
  let minimal := graphBackedVertexMinimalTaitCounterexample
    RSmin hclassMin htwoSided hnotMin hsmaller
  exact hnominimal _ minimal

/-- The sound connected-spherical Four-Colour headline follows from the
single compositional output proposition. -/
theorem connectedSphericalFourColorStatement_of_no_minimal
    (hnominimal : NoGraphBackedVertexMinimalTaitCounterexample.{u}) :
    GoertzelV24SphericalGraphPresentation.ConnectedSphericalFourColorStatement.{u} :=
  connectedSphericalFourColorStatement_of_tait
    (everyBridgelessSphericalCubicTaitColorable_of_no_minimal hnominimal)

/-- Conversely at the obstruction boundary, a non-four-colourable connected
spherical presentation rules out the assertion that no graph-backed minimal
Tait counterexample exists.  The least counterexample itself is constructed
inside `everyBridgelessSphericalCubicTaitColorable_of_no_minimal`; this theorem
packages the exact contrapositive consumed by the front end. -/
theorem not_noGraphBackedVertexMinimalTaitCounterexample_of_not_colorable
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (presentation :
      GoertzelV24SphericalGraphPresentation.ConnectedSphericalGraphPresentation G)
    (hcard : 3 ≤ Fintype.card V) (hnot : ¬ G.Colorable 4) :
    ¬ NoGraphBackedVertexMinimalTaitCounterexample.{u} := by
  intro hnominimal
  exact hnot
    (connectedSphericalFourColorStatement_of_no_minimal hnominimal
      G hcard ⟨presentation⟩)

/-- Componentwise form of the sound spherical Four-Colour headline.  The
separate classical plane-embedding representation theorem is the only
remaining adapter from abstract planarity to this statement. -/
theorem sphericalFourColorStatement_of_no_minimal
    (hnominimal : NoGraphBackedVertexMinimalTaitCounterexample.{u}) :
    GoertzelV24SphericalGraphPresentation.SphericalFourColorStatement.{u} :=
  sphericalFourColorStatement_of_tait
    (everyBridgelessSphericalCubicTaitColorable_of_no_minimal hnominimal)

end

end GoertzelV24SphericalMinimalCounterexampleSelection

end Mettapedia.GraphTheory.FourColor
