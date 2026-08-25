import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedCarrierGraphFamilyCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletionSensitivePortResidualFactorContraction

/-!
# A deletion-stable finite factor at a bounded interface

Deleting an interface vertex can split a component, so the component partition
before deletion is not a sufficient transition state.  It is also unnecessary
to store a separate component table for every deletion mask.

This file contracts only the part of a graph strictly outside the bounded
interface.  The finite code retains three Boolean relations on interface slots:
equality of represented vertices, literal adjacency inside the interface, and
attachment to one common exterior component.  For any deletion mask,
reachability between surviving interface slots is exactly the reflexive-
transitive closure of those three moves restricted to the surviving slots.

Thus one polynomial-size code serves every mask.  The theorem is graph-generic;
it does not assert that a particular corridor state already carries this code.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InterfaceDeletionComponentFactor

open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24BoundedCarrierGraphFamilyCode
open SimpleGraph

/-- A vertex is strictly outside the represented interface. -/
def OutsideInterface {N Interface : Type*}
    (interfaceVertex : Interface → N) (vertex : N) : Prop :=
  ∀ slot, vertex ≠ interfaceVertex slot

/-- The graph induced, on the original vertex type, strictly outside the
bounded interface. -/
def exteriorGraph {N Interface : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) : SimpleGraph N :=
  supportRestriction graph (OutsideInterface interfaceVertex)

/-- One primitive move in the interface contraction: two slots denote the
same vertex, their vertices are literally adjacent, or they attach to the same
component lying strictly outside the interface. -/
def InterfaceExteriorStep {N Interface : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (left right : Interface) : Prop :=
  interfaceVertex left = interfaceVertex right ∨
    graph.Adj (interfaceVertex left) (interfaceVertex right) ∨
    ∃ entry exit : N,
      OutsideInterface interfaceVertex entry ∧
      OutsideInterface interfaceVertex exit ∧
      graph.Adj (interfaceVertex left) entry ∧
      (exteriorGraph graph interfaceVertex).Reachable entry exit ∧
      graph.Adj exit (interfaceVertex right)

/-- Interface slots whose represented graph vertex survives the mask.  If two
slots alias the same vertex, removing either slot removes both aliases. -/
abbrev SurvivingInterfaceSlot {N Interface : Type*}
    (interfaceVertex : Interface → N) (removed : Interface → Bool) :=
  {slot : Interface // survivesMask interfaceVertex removed
    (interfaceVertex slot)}

/-- The primitive contraction move restricted to surviving interface slots. -/
def SurvivingInterfaceExteriorStep {N Interface : Type*}
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (removed : Interface → Bool)
    (left right : SurvivingInterfaceSlot interfaceVertex removed) : Prop :=
  InterfaceExteriorStep graph interfaceVertex left.1 right.1

private def InterfaceTraversalState {N Interface : Type*}
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (removed : Interface → Bool)
    (start : SurvivingInterfaceSlot interfaceVertex removed)
    (current : N) : Prop :=
  (∃ currentSlot : SurvivingInterfaceSlot interfaceVertex removed,
      interfaceVertex currentSlot.1 = current ∧
      Relation.ReflTransGen
        (SurvivingInterfaceExteriorStep graph interfaceVertex removed)
        start currentSlot) ∨
    ∃ lastSlot : SurvivingInterfaceSlot interfaceVertex removed,
      ∃ entry : N,
        Relation.ReflTransGen
          (SurvivingInterfaceExteriorStep graph interfaceVertex removed)
          start lastSlot ∧
        OutsideInterface interfaceVertex entry ∧
        OutsideInterface interfaceVertex current ∧
        graph.Adj (interfaceVertex lastSlot.1) entry ∧
        (exteriorGraph graph interfaceVertex).Reachable entry current

private theorem outsideInterface_survivesMask
    {N Interface : Type*} {interfaceVertex : Interface → N}
    {removed : Interface → Bool} {vertex : N}
    (houtside : OutsideInterface interfaceVertex vertex) :
    survivesMask interfaceVertex removed vertex := by
  intro slot _hremoved
  exact houtside slot

private theorem exteriorGraph_le_restrictedByMask
    {N Interface : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (removed : Interface → Bool) :
    exteriorGraph graph interfaceVertex ≤
      restrictedByMask graph interfaceVertex removed := by
  intro left right hadj
  exact ⟨hadj.1,
    outsideInterface_survivesMask hadj.2.1,
    outsideInterface_survivesMask hadj.2.2⟩

private theorem interfaceTraversalState_step
    {N Interface : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (removed : Interface → Bool)
    (start : SurvivingInterfaceSlot interfaceVertex removed)
    {current next : N}
    (hstate : InterfaceTraversalState graph interfaceVertex removed
      start current)
    (hstep : (restrictedByMask graph interfaceVertex removed).Adj
      current next) :
    InterfaceTraversalState graph interfaceVertex removed start next := by
  classical
  by_cases hnextOutside : OutsideInterface interfaceVertex next
  · rcases hstate with hboundary | hexterior
    · rcases hboundary with ⟨currentSlot, hcurrent, hclosure⟩
      right
      exact ⟨currentSlot, next, hclosure, hnextOutside, hnextOutside,
        by simpa [hcurrent] using hstep.1,
        SimpleGraph.Reachable.rfl⟩
    · rcases hexterior with
        ⟨lastSlot, entry, hclosure, hentryOutside, hcurrentOutside,
          hentry, hreach⟩
      right
      refine ⟨lastSlot, entry, hclosure, hentryOutside, hnextOutside,
        hentry, hreach.trans ?_⟩
      exact SimpleGraph.Adj.reachable
        ⟨hstep.1, hcurrentOutside, hnextOutside⟩
  · simp only [OutsideInterface, not_forall, not_not] at hnextOutside
    rcases hnextOutside with ⟨nextSlot, hnextSlot⟩
    have hnextSurvives : survivesMask interfaceVertex removed
        (interfaceVertex nextSlot) := by
      simpa [hnextSlot] using hstep.2.2
    let nextCoordinate : SurvivingInterfaceSlot interfaceVertex removed :=
      ⟨nextSlot, hnextSurvives⟩
    left
    refine ⟨nextCoordinate, hnextSlot.symm, ?_⟩
    rcases hstate with hboundary | hexterior
    · rcases hboundary with ⟨currentSlot, hcurrent, hclosure⟩
      apply hclosure.tail
      exact Or.inr (Or.inl (by
        simpa [hcurrent, hnextSlot] using hstep.1))
    · rcases hexterior with
        ⟨lastSlot, entry, hclosure, hentryOutside, hcurrentOutside,
          hentry, hreach⟩
      apply hclosure.tail
      exact Or.inr (Or.inr ⟨entry, current, hentryOutside,
        hcurrentOutside, hentry, hreach,
        by simpa [hnextSlot] using hstep.1⟩)

private theorem interfaceExteriorStep_reachable_restrictedByMask
    {N Interface : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (removed : Interface → Bool)
    (left right : SurvivingInterfaceSlot interfaceVertex removed)
    (hstep : SurvivingInterfaceExteriorStep graph interfaceVertex removed
      left right) :
    (restrictedByMask graph interfaceVertex removed).Reachable
      (interfaceVertex left.1) (interfaceVertex right.1) := by
  rcases hstep with heq | hadj | hexterior
  · simp [heq]
  · exact SimpleGraph.Adj.reachable ⟨hadj, left.2, right.2⟩
  · rcases hexterior with
      ⟨entry, exit, hentryOutside, hexitOutside, hentry, hreach, hexit⟩
    have hfirst :
        (restrictedByMask graph interfaceVertex removed).Reachable
          (interfaceVertex left.1) entry :=
      SimpleGraph.Adj.reachable
        ⟨hentry, left.2, outsideInterface_survivesMask hentryOutside⟩
    have hmiddle :
        (restrictedByMask graph interfaceVertex removed).Reachable entry exit :=
      hreach.mono
        (exteriorGraph_le_restrictedByMask graph interfaceVertex removed)
    have hlast :
        (restrictedByMask graph interfaceVertex removed).Reachable
          exit (interfaceVertex right.1) :=
      SimpleGraph.Adj.reachable
        ⟨hexit, outsideInterface_survivesMask hexitOutside, right.2⟩
    exact hfirst.trans (hmiddle.trans hlast)

/-- Reachability after any bounded interface deletion is exactly the closure
of equality, literal interface adjacency, and common-exterior-component moves
on the surviving slots.  The exterior component relation is independent of
the mask. -/
theorem restrictedByMask_reachable_iff_interfaceExteriorClosure
    {N Interface : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (removed : Interface → Bool)
    (left right : SurvivingInterfaceSlot interfaceVertex removed) :
    (restrictedByMask graph interfaceVertex removed).Reachable
        (interfaceVertex left.1) (interfaceVertex right.1) ↔
      Relation.ReflTransGen
        (SurvivingInterfaceExteriorStep graph interfaceVertex removed)
        left right := by
  constructor
  · intro hreachable
    have hpath := (SimpleGraph.reachable_iff_reflTransGen
      (interfaceVertex left.1) (interfaceVertex right.1)).mp hreachable
    have hstateOfPath : ∀ {current : N},
        Relation.ReflTransGen
            (restrictedByMask graph interfaceVertex removed).Adj
            (interfaceVertex left.1) current →
          InterfaceTraversalState graph interfaceVertex removed left current := by
      intro current hcurrent
      induction hcurrent with
      | refl =>
          exact Or.inl ⟨left, rfl, Relation.ReflTransGen.refl⟩
      | tail hprefix hstep ih =>
          exact interfaceTraversalState_step graph interfaceVertex removed
            left ih hstep
    have hstate : InterfaceTraversalState graph interfaceVertex removed left
        (interfaceVertex right.1) := hstateOfPath hpath
    rcases hstate with hboundary | hexterior
    · rcases hboundary with ⟨lastSlot, hlast, hclosure⟩
      exact hclosure.tail (Or.inl hlast)
    · rcases hexterior with
        ⟨_lastSlot, _entry, _hclosure, _hentryOutside, hrightOutside,
          _hentry, _hreach⟩
      exact (hrightOutside right.1 rfl).elim
  · intro hclosure
    induction hclosure with
    | refl => exact SimpleGraph.Reachable.rfl
    | tail hprefix hstep ih =>
        exact ih.trans
          (interfaceExteriorStep_reachable_restrictedByMask
            graph interfaceVertex removed _ _ hstep)

/-- The mask-independent finite interface code. -/
structure BoundedInterfaceExteriorCode (Interface : Type*) where
  vertexEq : Interface → Interface → Bool
  directAdj : Interface → Interface → Bool
  exteriorConnected : Interface → Interface → Bool

private def boundedInterfaceExteriorCodeEquiv (Interface : Type*) :
    BoundedInterfaceExteriorCode Interface ≃
      (Interface → Interface → Bool) ×
        (Interface → Interface → Bool) ×
        (Interface → Interface → Bool) where
  toFun code := ⟨code.vertexEq, code.directAdj, code.exteriorConnected⟩
  invFun data := ⟨data.1, data.2.1, data.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance {Interface : Type*} :
    DecidableEq (BoundedInterfaceExteriorCode Interface) :=
  Classical.decEq _

noncomputable instance {Interface : Type*} [Fintype Interface] :
    Fintype (BoundedInterfaceExteriorCode Interface) := by
  letI : Fintype (Interface → Interface → Bool) := Fintype.ofFinite _
  exact Fintype.ofEquiv _
    (boundedInterfaceExteriorCodeEquiv Interface).symm

/-- Interpret the three Boolean relations in a finite interface code. -/
def InterfaceExteriorFactoredStep {Interface : Type*}
    (code : BoundedInterfaceExteriorCode Interface)
    (left right : Interface) : Prop :=
  code.vertexEq left right = true ∨
    code.directAdj left right = true ∨
    code.exteriorConnected left right = true

/-- Canonical mask-independent finite code extracted from a graph. -/
noncomputable def exactInterfaceExteriorCode
    {N Interface : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) :
    BoundedInterfaceExteriorCode Interface where
  vertexEq left right := by
    classical
    exact decide (interfaceVertex left = interfaceVertex right)
  directAdj left right := by
    classical
    exact decide (graph.Adj (interfaceVertex left) (interfaceVertex right))
  exteriorConnected left right := by
    classical
    exact decide (∃ entry exit : N,
      OutsideInterface interfaceVertex entry ∧
      OutsideInterface interfaceVertex exit ∧
      graph.Adj (interfaceVertex left) entry ∧
      (exteriorGraph graph interfaceVertex).Reachable entry exit ∧
      graph.Adj exit (interfaceVertex right))

@[simp]
theorem exactInterfaceExteriorCode_step_iff
    {N Interface : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (left right : Interface) :
    InterfaceExteriorFactoredStep
        (exactInterfaceExteriorCode graph interfaceVertex) left right ↔
      InterfaceExteriorStep graph interfaceVertex left right := by
  classical
  simp [InterfaceExteriorFactoredStep, exactInterfaceExteriorCode,
    InterfaceExteriorStep]

/-- The canonical polynomial-size code reconstructs every deletion row.  A
mask changes only which interface slots participate in the closure; the code
itself is unchanged. -/
theorem restrictedByMask_reachable_iff_exactInterfaceExteriorFactoredClosure
    {N Interface : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (removed : Interface → Bool)
    (left right : SurvivingInterfaceSlot interfaceVertex removed) :
    (restrictedByMask graph interfaceVertex removed).Reachable
        (interfaceVertex left.1) (interfaceVertex right.1) ↔
      Relation.ReflTransGen
        (fun first second : SurvivingInterfaceSlot interfaceVertex removed =>
          InterfaceExteriorFactoredStep
            (exactInterfaceExteriorCode graph interfaceVertex)
            first.1 second.1)
        left right := by
  rw [restrictedByMask_reachable_iff_interfaceExteriorClosure]
  constructor
  · intro hclosure
    exact hclosure.mono fun first second hstep =>
      (exactInterfaceExteriorCode_step_iff graph interfaceVertex
        first.1 second.1).2 hstep
  · intro hclosure
    exact hclosure.mono fun first second hstep =>
      (exactInterfaceExteriorCode_step_iff graph interfaceVertex
        first.1 second.1).1 hstep

/-- A bounded family of deletion-stable interface codes sharing one literal
carrier.  The carrier cardinality is stored dependently, so no dummy vertices
or padded aliases are introduced. -/
structure BoundedInterfaceExteriorFamilyCode
    (bound : Nat) (Family : Type*) where
  vertexCount : Fin (bound + 1)
  code : Family → BoundedInterfaceExteriorCode (Fin vertexCount.val)

private def boundedInterfaceExteriorFamilyCodeEquiv
    (bound : Nat) (Family : Type*) :
    BoundedInterfaceExteriorFamilyCode bound Family ≃
      Σ vertexCount : Fin (bound + 1),
        Family → BoundedInterfaceExteriorCode (Fin vertexCount.val) where
  toFun code := ⟨code.vertexCount, code.code⟩
  invFun code := ⟨code.1, code.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance {bound : Nat} {Family : Type*} :
    DecidableEq (BoundedInterfaceExteriorFamilyCode bound Family) :=
  Classical.decEq _

noncomputable instance {bound : Nat} {Family : Type*} [Fintype Family] :
    Fintype (BoundedInterfaceExteriorFamilyCode bound Family) := by
  letI (vertexCount : Fin (bound + 1)) :
      Fintype (Family →
        BoundedInterfaceExteriorCode (Fin vertexCount.val)) :=
    Fintype.ofFinite _
  exact Fintype.ofEquiv _
    (boundedInterfaceExteriorFamilyCodeEquiv bound Family).symm

/-- Extract one mask-independent exterior-component code for every graph in a
family on the same bounded carrier. -/
noncomputable def boundedInterfaceExteriorFamilyCode
    {N Family : Type*} [Fintype N]
    (carrier : Finset N) (bound : Nat) (hcard : carrier.card ≤ bound)
    (graphs : Family → SimpleGraph N) :
    BoundedInterfaceExteriorFamilyCode bound Family where
  vertexCount := ⟨carrier.card, Nat.lt_succ_of_le hcard⟩
  code family :=
    exactInterfaceExteriorCode (graphs family)
      (fun slot : Fin carrier.card =>
        ((carrierCoordinate carrier).symm slot).1)

/-- The bounded-family extractor retains the literal carrier cardinality. -/
@[simp]
theorem boundedInterfaceExteriorFamilyCode_vertexCount
    {N Family : Type*} [Fintype N]
    (carrier : Finset N) (bound : Nat) (hcard : carrier.card ≤ bound)
    (graphs : Family → SimpleGraph N) :
    (boundedInterfaceExteriorFamilyCode carrier bound hcard graphs
      ).vertexCount.val = carrier.card :=
  rfl

/-- Each member of the canonical bounded family reconstructs reachability
after every deletion mask on the common carrier. -/
theorem boundedInterfaceExteriorFamilyCode_reachable_iff
    {N Family : Type*} [Fintype N]
    (carrier : Finset N) (bound : Nat) (hcard : carrier.card ≤ bound)
    (graphs : Family → SimpleGraph N) (family : Family)
    (removed : Fin carrier.card → Bool)
    (left right : SurvivingInterfaceSlot
      (fun slot : Fin carrier.card =>
        ((carrierCoordinate carrier).symm slot).1)
      removed) :
    (restrictedByMask (graphs family)
        (fun slot : Fin carrier.card =>
          ((carrierCoordinate carrier).symm slot).1)
        removed).Reachable
        ((carrierCoordinate carrier).symm left.1).1
        ((carrierCoordinate carrier).symm right.1).1 ↔
      Relation.ReflTransGen
        (fun first second : SurvivingInterfaceSlot
            (fun slot : Fin carrier.card =>
              ((carrierCoordinate carrier).symm slot).1) removed =>
          InterfaceExteriorFactoredStep
            ((boundedInterfaceExteriorFamilyCode carrier bound hcard graphs
              ).code family)
            first.1 second.1)
        left right := by
  exact restrictedByMask_reachable_iff_exactInterfaceExteriorFactoredClosure
    (graphs family)
    (fun slot : Fin carrier.card =>
      ((carrierCoordinate carrier).symm slot).1)
    removed left right

end GoertzelV24InterfaceDeletionComponentFactor

end Mettapedia.GraphTheory.FourColor
