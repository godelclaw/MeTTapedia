import Mettapedia.GraphTheory.FourColor.GoertzelV24SourceHeadlineAssembly

/-!
# Minimal-counterexample selection

This is the selection argument for the historical headline assembly imported
above, retained with its explicit hypotheses. The status descriptions below
describe that interface, not a current audit of the active spherical assembly.

The headline assembly consumes one classical obligation: absence of a
graph-backed vertex-minimal Tait counterexample implies the Four-Color
statement.  This module proves the *selection* half of that obligation — the
least-counterexample extraction that informal mathematics performs silently —
and thereby decomposes the bridge into three single-lemma classical debts:

* `ClassFacesTwoSided` — every bridgeless spherical cubic map has two-sided
  faces (classically: a bridge is exactly an edge with one face on both
  sides; here it must be derived from the Euler datum and bridge-freeness);
* `MinimalCounterexampleGraphBacked` — a *least* counterexample is
  presentable, at equal vertex count, as the rotation system of a
  simple-graph dart rotation whose Tait colorings transfer back.  The
  unrestricted form over the whole class is FALSE: the spherical theta
  multigraph (two vertices joined by three parallel edges) is bridgeless,
  spherical, and cubic, yet no simple graph on two vertices is cubic.  At a
  least counterexample the classical normalization recovers simpleness — a
  loop would make the third edge at its vertex a bridge, and a parallel
  pair forms a two-edge cut discharged by the minimality reduction;
* `TaitReductionObligation` — Tait's classical reduction of planar vertex
  4-colorability to cubic 3-edge-colorability, proved in the source
  manuscript's Section 2 and not yet formalized here.

Given the first two, the selection theorem below is *proved*: if every
graph-backed vertex-minimal Tait counterexample is absurd, then every member
of the bridgeless spherical cubic class is Tait colorable.  The argument is
the honest form of "take a smallest counterexample": the set of
counterexample sizes is a set of naturals; a least element exists; the
witness at that size is presented as graph-backed data; leastness discharges
the `smallerColorable` field; the hypotheses supply the remaining fields; and
the assumed absurdity of minimal counterexamples closes the contradiction.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24MinimalCounterexampleSelection

open GoertzelV24SourceHeadlineAssembly
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality

universe u

/- The two retained-vertex decidability instances that used to shadow the
subtype instance here are now declared `local` at their defining sites, so no
erasure is needed. -/

/-- Classical debt one: two-sided faces across the bridgeless spherical
cubic class. -/
def ClassFacesTwoSided : Prop :=
  ∀ {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (RS : RotationSystem.{u, u, u} V E),
    BridgelessSphericalCubicMapData RS → OrbitFacesTwoSided RS

/-- A presentation of a rotation system as graph-backed dart-rotation data of
the same vertex count, remaining in the structural class, with Tait
colorings transferring back to the presented system. -/
structure GraphBackedPresentation
    {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (RS : RotationSystem.{u, u, u} V E) : Type (u + 1) where
  Vertex : Type u
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  graph : SimpleGraph Vertex
  [adjDecidable : DecidableRel graph.Adj]
  graphData : SimpleGraphDartRotation.Data graph
  card_eq : Fintype.card Vertex = Fintype.card V
  structural : BridgelessSphericalCubicMapData graphData.toRotationSystem
  colorable_transfer :
    RotationSystemTaitColorable graphData.toRotationSystem →
      RotationSystemTaitColorable RS

/-- Classical debt two, in its correct scope: a graph-backed presentation
is required only for a *least* counterexample — a class member that is not
Tait colorable while every smaller class member is.  The unrestricted form
over the whole class is false (spherical theta multigraph), so the
minimality data is a load-bearing hypothesis, not a convenience. -/
def MinimalCounterexampleGraphBacked : Prop :=
  ∀ {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (RS : RotationSystem.{u, u, u} V E),
    BridgelessSphericalCubicMapData RS →
    ¬ RotationSystemTaitColorable RS →
    (∀ {V' E' : Type u}
      [Fintype V'] [DecidableEq V'] [Fintype E'] [DecidableEq E']
      (candidate : RotationSystem.{u, u, u} V' E'),
      Fintype.card V' < Fintype.card V →
      BridgelessSphericalCubicMapData candidate →
      RotationSystemTaitColorable candidate) →
    Nonempty (GraphBackedPresentation RS)

/-- The set of vertex counts realized by class counterexamples. -/
def counterexampleSizes : Set ℕ :=
  {n | ∃ (V' E' : Type u),
    ∃ (_ : Fintype V') (_ : DecidableEq V')
      (_ : Fintype E') (_ : DecidableEq E'),
    ∃ RS' : RotationSystem.{u, u, u} V' E',
      Nonempty (BridgelessSphericalCubicMapData RS') ∧
        ¬ RotationSystemTaitColorable RS' ∧ Fintype.card V' = n}

/-- **The selection theorem.**  With the two classical debts supplied, the
absence of graph-backed vertex-minimal Tait counterexamples makes every
member of the bridgeless spherical cubic class Tait colorable. -/
theorem taitColorable_of_no_minimal
    (htwoSided : ClassFacesTwoSided.{u})
    (hpresent : MinimalCounterexampleGraphBacked.{u})
    (hnominimal :
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : SimpleGraph V} [DecidableRel G.Adj]
        (graphData : SimpleGraphDartRotation.Data G),
        GraphBackedVertexMinimalTaitCounterexample graphData → False) :
    ∀ {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (RS : RotationSystem.{u, u, u} V E),
      BridgelessSphericalCubicMapData RS →
      RotationSystemTaitColorable RS := by
  intro V E _ _ _ _ RS hclass
  by_contra hnotcolorable
  classical
  have hnonempty : (counterexampleSizes.{u}).Nonempty :=
    ⟨Fintype.card V,
      V, E, inferInstance, inferInstance, inferInstance, inferInstance,
      RS, ⟨hclass⟩, hnotcolorable, rfl⟩
  obtain ⟨V₀, E₀, iV₀, iV₀', iE₀, iE₀', RS₀, ⟨hclass₀⟩, hnotcol₀, hcard₀⟩ :=
    Nat.sInf_mem hnonempty
  -- leastness makes every smaller class member colorable
  have hminimal :
      ∀ {V' E' : Type u}
        [Fintype V'] [DecidableEq V'] [Fintype E'] [DecidableEq E']
        (candidate : RotationSystem.{u, u, u} V' E'),
        Fintype.card V' < Fintype.card V₀ →
        BridgelessSphericalCubicMapData candidate →
        RotationSystemTaitColorable candidate := by
    intro V' E' _ _ _ _ candidate hsmall hcandidate
    by_contra hnotcandidate
    have hmem : Fintype.card V' ∈ counterexampleSizes.{u} :=
      ⟨V', E', inferInstance, inferInstance, inferInstance, inferInstance,
        candidate, ⟨hcandidate⟩, hnotcandidate, rfl⟩
    have hle := Nat.sInf_le hmem
    rw [hcard₀] at hsmall
    omega
  obtain ⟨presentation⟩ := hpresent RS₀ hclass₀ hnotcol₀ hminimal
  letI := presentation.vertexFintype
  letI := presentation.vertexDecidableEq
  letI := presentation.adjDecidable
  refine hnominimal presentation.graphData
    { toBridgelessSphericalCubicMapData := presentation.structural
      facesTwoSided := htwoSided _ presentation.structural
      notColorable := fun hcolorable =>
        hnotcol₀ (presentation.colorable_transfer hcolorable)
      smallerColorable := ?_ }
  intro V' E' _ _ _ _ candidate hsmall hcandidate
  rw [presentation.card_eq] at hsmall
  exact hminimal candidate hsmall hcandidate

/-- Classical debt three: Tait's reduction of the headline statement to
cubic-class colorability, in the source's Section 2 form. -/
def TaitReductionObligation : Prop :=
  (∀ {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (RS : RotationSystem.{u, u, u} V E),
      BridgelessSphericalCubicMapData RS →
      RotationSystemTaitColorable RS) →
    FourColorStatement.{u}

/-- **The bridge, decomposed.**  The headline's monolithic Tait-bridge
obligation follows from the three single-lemma classical debts. -/
theorem taitBridgeObligation_of_classical_debts
    (htwoSided : ClassFacesTwoSided.{u})
    (hpresent : MinimalCounterexampleGraphBacked.{u})
    (hreduction : TaitReductionObligation.{u}) :
    TaitBridgeObligation.{u} := by
  intro hnominimal
  refine hreduction ?_
  intro V E _ _ _ _ RS hclass
  refine taitColorable_of_no_minimal htwoSided hpresent ?_ RS hclass
  intro V' _ _ G' _ graphData minimal
  exact hnominimal graphData minimal

/-- The headline with the bridge decomposed: the Four-Color statement from
the two route hypotheses, the normalization packaging, and the three
single-lemma classical debts. -/
theorem fourColorStatement_of_route_decomposed
    (widthBound : Nat)
    (adapters :
      GoertzelV24ClosedWebFragmentReindexReductionSupplier.FragmentReindexRadialReductionAdapters.{u}
        widthBound)
    {State : Type*}
    (reflection :
      GoertzelV24ReductiveSpine.ReductiveSystem.RouteNativeBaseReflection
        (GoertzelV24ClosedWebReductiveAssembly.PackedInstance.reductiveSystem 845970
          (GoertzelV24ClosedWebFragmentReindexReductionSupplier.strictReductionSupplier_845970_of_fragmentReindexRadialAdapters
            widthBound adapters))
        State)
    (haudit :
      ∀ state ∈ reflection.reachable, ¬ reflection.Necessary state)
    (normalization : NormalizationObligation.{u})
    (htwoSided : ClassFacesTwoSided.{u})
    (hpresent : MinimalCounterexampleGraphBacked.{u})
    (hreduction : TaitReductionObligation.{u}) :
    FourColorStatement.{u} :=
  fourColorStatement_of_route widthBound adapters reflection haudit
    normalization
    (taitBridgeObligation_of_classical_debts htwoSided hpresent hreduction)

end GoertzelV24MinimalCounterexampleSelection

end Mettapedia.GraphTheory.FourColor
