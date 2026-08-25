import Mettapedia.GraphTheory.FourColor.GoertzelV24FiniteBoolRelationClosure
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorForget
import Mettapedia.GraphTheory.RelationExtras

/-!
# Executable exterior-row contraction under interface forgetting

Forgetting coordinates from a bounded interface does not merely restrict the
old exterior-connectivity table.  A forgotten coordinate becomes an interior
waypoint, and several old primitive interface moves may therefore compose into
one exterior connection of the smaller interface.

This file gives the finite executable contraction.  Between two retained
coordinates, the new exterior row holds either when the old exterior row holds
directly, or when one can enter a surviving forgotten coordinate, traverse the
finite closure of old primitive moves among forgotten coordinates, and leave
for the other retained coordinate.  Survival is computed from the code's
vertex-equality row, so aliased coordinate names are removed together.

The construction is generic finite-state infrastructure.  It does not choose
a source alphabet, claim that an encoded state is realizable, or perform a
bounded-base audit.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InterfaceDeletionComponentFactorForgetExterior

open GoertzelV24FiniteBoolRelationClosure
open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorForget
open SimpleGraph

/-- Executable Boolean presentation of one primitive exterior-factor move. -/
def interfaceExteriorFactoredStepBool {Interface : Type*}
    (code : BoundedInterfaceExteriorCode Interface)
    (left right : Interface) : Bool :=
  code.vertexEq left right ||
    code.directAdj left right ||
      code.exteriorConnected left right

@[simp]
theorem interfaceExteriorFactoredStepBool_eq_true_iff
    {Interface : Type*}
    (code : BoundedInterfaceExteriorCode Interface)
    (left right : Interface) :
    interfaceExteriorFactoredStepBool code left right = true ↔
      InterfaceExteriorFactoredStep code left right := by
  simp [interfaceExteriorFactoredStepBool, InterfaceExteriorFactoredStep,
    or_assoc]

/-- A larger coordinate survives the target interface exactly when it is not
vertex-equal, according to the code, to any mapped target coordinate. -/
def codeSurvivesPartialRetained
    {Larger Retained : Type*} [Fintype Retained]
    (code : BoundedInterfaceExteriorCode Larger)
    (retain : Retained → Option Larger) (slot : Larger) : Bool :=
  decide (∀ retained retainedSlot, retain retained = some retainedSlot →
    code.vertexEq slot retainedSlot = false)

/-- Finite carrier of the larger coordinates that become interior waypoints
after target-interface forgetting. -/
abbrev CodeSurvivingSlot
    {Larger Retained : Type*} [Fintype Retained]
    (code : BoundedInterfaceExteriorCode Larger)
    (retain : Retained → Option Larger) :=
  {slot : Larger // codeSurvivesPartialRetained code retain slot = true}

@[simp]
theorem codeSurvivesPartialRetained_eq_true_iff
    {Larger Retained : Type*} [Fintype Retained]
    (code : BoundedInterfaceExteriorCode Larger)
    (retain : Retained → Option Larger) (slot : Larger) :
    codeSurvivesPartialRetained code retain slot = true ↔
      ∀ retained retainedSlot, retain retained = some retainedSlot →
        code.vertexEq slot retainedSlot = false := by
  simp only [codeSurvivesPartialRetained, decide_eq_true_eq]

/-- For an exact graph code, code-level survival is literal mask survival.
This is the alias-sensitive bridge: two coordinate names for the same vertex
are deleted together. -/
theorem codeSurvivesPartialRetained_exact_iff
    {N Larger Retained : Type*} [Fintype Retained] [DecidableEq Larger]
    (graph : SimpleGraph N) (largerVertex : Larger → N)
    (retain : Retained → Option Larger) (slot : Larger) :
    codeSurvivesPartialRetained
        (exactInterfaceExteriorCode graph largerVertex) retain slot = true ↔
      survivesMask largerVertex (partialRetainedCoordinateMask retain)
        (largerVertex slot) := by
  classical
  rw [codeSurvivesPartialRetained_eq_true_iff]
  constructor
  · intro hall retainedSlot hremoved heq
    rw [partialRetainedCoordinateMask_eq_true_iff] at hremoved
    rcases hremoved with ⟨retained, hretained⟩
    have hfalse := hall retained retainedSlot hretained
    simp only [exactInterfaceExteriorCode, decide_eq_false_iff_not] at hfalse
    exact hfalse heq
  · intro hsurvives retained retainedSlot hretained
    simp only [exactInterfaceExteriorCode, decide_eq_false_iff_not]
    intro heq
    apply hsurvives retainedSlot
    · rw [partialRetainedCoordinateMask_eq_true_iff]
      exact ⟨retained, hretained⟩
    · exact heq

/-- Identity-on-coordinates equivalence between code-level and literal
graph-level surviving slots for an exact code. -/
noncomputable def codeSurvivingExactEquiv
    {N Larger Retained : Type*} [Fintype Retained] [DecidableEq Larger]
    (graph : SimpleGraph N) (largerVertex : Larger → N)
    (retain : Retained → Option Larger) :
    CodeSurvivingSlot (exactInterfaceExteriorCode graph largerVertex) retain ≃
      SurvivingInterfaceSlot largerVertex
        (partialRetainedCoordinateMask retain) where
  toFun slot := ⟨slot.1,
    (codeSurvivesPartialRetained_exact_iff graph largerVertex retain slot.1).1
      slot.2⟩
  invFun slot := ⟨slot.1,
    (codeSurvivesPartialRetained_exact_iff graph largerVertex retain slot.1).2
      slot.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem codeSurvivingExactEquiv_apply_val
    {N Larger Retained : Type*} [Fintype Retained] [DecidableEq Larger]
    (graph : SimpleGraph N) (largerVertex : Larger → N)
    (retain : Retained → Option Larger)
    (slot : CodeSurvivingSlot
      (exactInterfaceExteriorCode graph largerVertex) retain) :
    (codeSurvivingExactEquiv graph largerVertex retain slot).1 = slot.1 :=
  rfl

@[simp]
theorem codeSurvivingExactEquiv_symm_apply_val
    {N Larger Retained : Type*} [Fintype Retained] [DecidableEq Larger]
    (graph : SimpleGraph N) (largerVertex : Larger → N)
    (retain : Retained → Option Larger)
    (slot : SurvivingInterfaceSlot largerVertex
      (partialRetainedCoordinateMask retain)) :
    ((codeSurvivingExactEquiv graph largerVertex retain).symm slot).1 = slot.1 :=
  rfl

/-- Executable closure of the old primitive relation among exactly the larger
coordinates that survive forgetting the target interface. -/
def forgottenCoordinateReachable
    {Larger Retained : Type*} [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained]
    (code : BoundedInterfaceExteriorCode Larger)
    (retain : Retained → Option Larger)
    (left right : CodeSurvivingSlot code retain) : Bool :=
  boolRelationReachable
    (fun first second =>
      interfaceExteriorFactoredStepBool code first.1 second.1)
    left right

/-- On an exact graph code, the executable forgotten-coordinate closure is
literal reachability in the target exterior graph. -/
theorem forgottenCoordinateReachable_exact_eq_true_iff
    {N Larger Retained : Type*} [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    (hnone : ∀ retained, retain retained = none →
      retainedVertex retained ∉ graph.support)
    (left right : CodeSurvivingSlot
      (exactInterfaceExteriorCode graph largerVertex) retain) :
    forgottenCoordinateReachable
        (exactInterfaceExteriorCode graph largerVertex) retain left right =
          true ↔
      (exteriorGraph graph retainedVertex).Reachable
        (largerVertex left.1) (largerVertex right.1) := by
  let coordinateEquiv := codeSurvivingExactEquiv graph largerVertex retain
  rw [forgottenCoordinateReachable, boolRelationReachable_eq_true_iff]
  constructor
  · intro hclosure
    have hliteral : Relation.ReflTransGen
        (fun before after : SurvivingInterfaceSlot largerVertex
            (partialRetainedCoordinateMask retain) =>
          InterfaceExteriorFactoredStep
            (exactInterfaceExteriorCode graph largerVertex)
            before.1 after.1)
        (coordinateEquiv left) (coordinateEquiv right) := by
      apply Mettapedia.GraphTheory.ReflTransGen.map_rel coordinateEquiv
      · intro before after hstep
        exact hstep
      · exact hclosure.mono fun before after hstep =>
          (interfaceExteriorFactoredStepBool_eq_true_iff
            (exactInterfaceExteriorCode graph largerVertex)
            before.1 after.1).1 hstep
    exact (exteriorGraph_reachable_iff_exactClosure_partialRetained graph
      largerVertex retainedVertex retain hsome hnone
      (coordinateEquiv left) (coordinateEquiv right)).2 hliteral
  · intro hreach
    have hliteral :=
      (exteriorGraph_reachable_iff_exactClosure_partialRetained graph
        largerVertex retainedVertex retain hsome hnone
        (coordinateEquiv left) (coordinateEquiv right)).1 hreach
    have hcode : Relation.ReflTransGen
        (fun before after : CodeSurvivingSlot
            (exactInterfaceExteriorCode graph largerVertex) retain =>
          InterfaceExteriorFactoredStep
            (exactInterfaceExteriorCode graph largerVertex)
            before.1 after.1)
        left right := by
      have hmapped : Relation.ReflTransGen
          (fun before after : CodeSurvivingSlot
              (exactInterfaceExteriorCode graph largerVertex) retain =>
            InterfaceExteriorFactoredStep
              (exactInterfaceExteriorCode graph largerVertex)
              before.1 after.1)
          (coordinateEquiv.symm (coordinateEquiv left))
          (coordinateEquiv.symm (coordinateEquiv right)) := by
        apply Mettapedia.GraphTheory.ReflTransGen.map_rel coordinateEquiv.symm
        · intro before after hstep
          change InterfaceExteriorFactoredStep
            (exactInterfaceExteriorCode graph largerVertex)
            before.1 after.1 at hstep
          simpa only [coordinateEquiv,
            codeSurvivingExactEquiv_symm_apply_val] using hstep
        · exact hliteral
      simpa [coordinateEquiv] using hmapped
    exact hcode.mono fun before after hstep =>
      (interfaceExteriorFactoredStepBool_eq_true_iff
        (exactInterfaceExteriorCode graph largerVertex)
        before.1 after.1).2 hstep

private theorem exteriorGraph_larger_le_target
    {N Larger Retained : Type*}
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    (hnone : ∀ retained, retain retained = none →
      retainedVertex retained ∉ graph.support) :
    exteriorGraph graph largerVertex ≤ exteriorGraph graph retainedVertex := by
  intro left right hadj
  refine ⟨hadj.1, ?_, ?_⟩
  · exact outsideInterface_of_outsideLarger_partialRetained_of_mem_support
      graph largerVertex retainedVertex retain hsome hnone left hadj.2.1
      ⟨right, hadj.1⟩
  · exact outsideInterface_of_outsideLarger_partialRetained_of_mem_support
      graph largerVertex retainedVertex retain hsome hnone right hadj.2.2
      ⟨left, hadj.1.symm⟩

private theorem exactStep_to_surviving_targetExterior
    {N Larger Retained : Type*} [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    (hnone : ∀ retained, retain retained = none →
      retainedVertex retained ∉ graph.support)
    (left : Retained) (largerLeft : Larger)
    (hleft : retain left = some largerLeft)
    (first : CodeSurvivingSlot
      (exactInterfaceExteriorCode graph largerVertex) retain)
    (hstep : InterfaceExteriorFactoredStep
      (exactInterfaceExteriorCode graph largerVertex) largerLeft first.1) :
    ∃ entry,
      OutsideInterface retainedVertex entry ∧
      graph.Adj (retainedVertex left) entry ∧
      (exteriorGraph graph retainedVertex).Reachable
        entry (largerVertex first.1) := by
  have hsurvives : survivesMask largerVertex
      (partialRetainedCoordinateMask retain) (largerVertex first.1) :=
    (codeSurvivesPartialRetained_exact_iff graph largerVertex retain first.1).1
      first.2
  have hremoved : partialRetainedCoordinateMask retain largerLeft = true :=
    (partialRetainedCoordinateMask_eq_true_iff retain largerLeft).2
      ⟨left, hleft⟩
  have hliteral :=
    (exactInterfaceExteriorCode_step_iff graph largerVertex largerLeft
      first.1).1 hstep
  rcases hliteral with heq | hadj | hexterior
  · exact (hsurvives largerLeft hremoved heq.symm).elim
  · have hfirstSupport : largerVertex first.1 ∈ graph.support :=
      ⟨largerVertex largerLeft, hadj.symm⟩
    have hfirstOutside : OutsideInterface retainedVertex
        (largerVertex first.1) :=
      outsideInterface_of_survives_partialRetained_of_mem_support graph
        largerVertex retainedVertex retain hsome hnone first.1 hsurvives
        hfirstSupport
    refine ⟨largerVertex first.1, hfirstOutside, ?_,
      SimpleGraph.Reachable.rfl⟩
    rw [← hsome left largerLeft hleft]
    exact hadj
  · rcases hexterior with
      ⟨entry, exit, hentryLarger, hexitLarger, hentry, hreach, hexit⟩
    have hentryOutside : OutsideInterface retainedVertex entry :=
      outsideInterface_of_outsideLarger_partialRetained_of_mem_support graph
        largerVertex retainedVertex retain hsome hnone entry hentryLarger
        ⟨largerVertex largerLeft, hentry.symm⟩
    have hexitOutside : OutsideInterface retainedVertex exit :=
      outsideInterface_of_outsideLarger_partialRetained_of_mem_support graph
        largerVertex retainedVertex retain hsome hnone exit hexitLarger
        ⟨largerVertex first.1, hexit⟩
    have hfirstOutside : OutsideInterface retainedVertex
        (largerVertex first.1) :=
      outsideInterface_of_survives_partialRetained_of_mem_support graph
        largerVertex retainedVertex retain hsome hnone first.1 hsurvives
        ⟨exit, hexit.symm⟩
    refine ⟨entry, hentryOutside, ?_, ?_⟩
    · rw [← hsome left largerLeft hleft]
      exact hentry
    · exact (hreach.mono (exteriorGraph_larger_le_target graph largerVertex
          retainedVertex retain hsome hnone)).trans
        (SimpleGraph.Adj.reachable ⟨hexit, hexitOutside, hfirstOutside⟩)

private theorem exactStep_from_surviving_targetExterior
    {N Larger Retained : Type*} [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    (hnone : ∀ retained, retain retained = none →
      retainedVertex retained ∉ graph.support)
    (last : CodeSurvivingSlot
      (exactInterfaceExteriorCode graph largerVertex) retain)
    (right : Retained) (largerRight : Larger)
    (hright : retain right = some largerRight)
    (hstep : InterfaceExteriorFactoredStep
      (exactInterfaceExteriorCode graph largerVertex) last.1 largerRight) :
    ∃ exit,
      OutsideInterface retainedVertex exit ∧
      (exteriorGraph graph retainedVertex).Reachable
        (largerVertex last.1) exit ∧
      graph.Adj exit (retainedVertex right) := by
  have hsurvives : survivesMask largerVertex
      (partialRetainedCoordinateMask retain) (largerVertex last.1) :=
    (codeSurvivesPartialRetained_exact_iff graph largerVertex retain last.1).1
      last.2
  have hremoved : partialRetainedCoordinateMask retain largerRight = true :=
    (partialRetainedCoordinateMask_eq_true_iff retain largerRight).2
      ⟨right, hright⟩
  have hliteral :=
    (exactInterfaceExteriorCode_step_iff graph largerVertex last.1
      largerRight).1 hstep
  rcases hliteral with heq | hadj | hexterior
  · exact (hsurvives largerRight hremoved heq).elim
  · have hlastSupport : largerVertex last.1 ∈ graph.support :=
      ⟨largerVertex largerRight, hadj⟩
    have hlastOutside : OutsideInterface retainedVertex
        (largerVertex last.1) :=
      outsideInterface_of_survives_partialRetained_of_mem_support graph
        largerVertex retainedVertex retain hsome hnone last.1 hsurvives
        hlastSupport
    refine ⟨largerVertex last.1, hlastOutside,
      SimpleGraph.Reachable.rfl, ?_⟩
    rw [← hsome right largerRight hright]
    exact hadj
  · rcases hexterior with
      ⟨entry, exit, hentryLarger, hexitLarger, hentry, hreach, hexit⟩
    have hlastOutside : OutsideInterface retainedVertex
        (largerVertex last.1) :=
      outsideInterface_of_survives_partialRetained_of_mem_support graph
        largerVertex retainedVertex retain hsome hnone last.1 hsurvives
        ⟨entry, hentry⟩
    have hentryOutside : OutsideInterface retainedVertex entry :=
      outsideInterface_of_outsideLarger_partialRetained_of_mem_support graph
        largerVertex retainedVertex retain hsome hnone entry hentryLarger
        ⟨largerVertex last.1, hentry.symm⟩
    have hexitOutside : OutsideInterface retainedVertex exit :=
      outsideInterface_of_outsideLarger_partialRetained_of_mem_support graph
        largerVertex retainedVertex retain hsome hnone exit hexitLarger
        ⟨largerVertex largerRight, hexit⟩
    have hfirst : (exteriorGraph graph retainedVertex).Reachable
        (largerVertex last.1) entry :=
      SimpleGraph.Adj.reachable ⟨hentry, hlastOutside, hentryOutside⟩
    refine ⟨exit, hexitOutside, ?_, ?_⟩
    · exact hfirst.trans
        (hreach.mono (exteriorGraph_larger_le_target graph largerVertex
          retainedVertex retain hsome hnone))
    · rw [← hsome right largerRight hright]
      exact hexit

/-- Proof-facing relation computed by the executable forgotten-coordinate
closure. -/
def PartialExteriorConnection
    {Larger Retained : Type*} [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained]
    (code : BoundedInterfaceExteriorCode Larger)
    (retain : Retained → Option Larger)
    (largerLeft largerRight : Larger) : Prop :=
  code.exteriorConnected largerLeft largerRight = true ∨
    ∃ first last : CodeSurvivingSlot code retain,
      InterfaceExteriorFactoredStep code largerLeft first.1 ∧
      Relation.ReflTransGen
        (fun before after : CodeSurvivingSlot code retain =>
          InterfaceExteriorFactoredStep code before.1 after.1)
        first last ∧
      InterfaceExteriorFactoredStep code last.1 largerRight

/-- Soundness of the contracted exterior formula for an exact graph code. -/
theorem partialExteriorConnection_exact_sound
    {N Larger Retained : Type*} [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    (hnone : ∀ retained, retain retained = none →
      retainedVertex retained ∉ graph.support)
    (left right : Retained) (largerLeft largerRight : Larger)
    (hleft : retain left = some largerLeft)
    (hright : retain right = some largerRight)
    (hconnection : PartialExteriorConnection
      (exactInterfaceExteriorCode graph largerVertex) retain
      largerLeft largerRight) :
    ∃ entry exit : N,
      OutsideInterface retainedVertex entry ∧
      OutsideInterface retainedVertex exit ∧
      graph.Adj (retainedVertex left) entry ∧
      (exteriorGraph graph retainedVertex).Reachable entry exit ∧
      graph.Adj exit (retainedVertex right) := by
  rcases hconnection with hold | hforgotten
  · simp only [exactInterfaceExteriorCode, decide_eq_true_eq] at hold
    rcases hold with
      ⟨entry, exit, hentryLarger, hexitLarger, hentry, hreach, hexit⟩
    have hentryOutside : OutsideInterface retainedVertex entry :=
      outsideInterface_of_outsideLarger_partialRetained_of_mem_support graph
        largerVertex retainedVertex retain hsome hnone entry hentryLarger
        ⟨largerVertex largerLeft, hentry.symm⟩
    have hexitOutside : OutsideInterface retainedVertex exit :=
      outsideInterface_of_outsideLarger_partialRetained_of_mem_support graph
        largerVertex retainedVertex retain hsome hnone exit hexitLarger
        ⟨largerVertex largerRight, hexit⟩
    refine ⟨entry, exit, hentryOutside, hexitOutside, ?_, ?_, ?_⟩
    · rw [← hsome left largerLeft hleft]
      exact hentry
    · exact hreach.mono (exteriorGraph_larger_le_target graph largerVertex
        retainedVertex retain hsome hnone)
    · rw [← hsome right largerRight hright]
      exact hexit
  · rcases hforgotten with
      ⟨first, last, hfirst, hmiddle, hlast⟩
    rcases exactStep_to_surviving_targetExterior graph largerVertex
      retainedVertex retain hsome hnone left largerLeft hleft first hfirst with
      ⟨entry, hentryOutside, hentry, hentryReach⟩
    rcases exactStep_from_surviving_targetExterior graph largerVertex
      retainedVertex retain hsome hnone last right largerRight hright hlast with
      ⟨exit, hexitOutside, hexitReach, hexit⟩
    have hmiddleBool : forgottenCoordinateReachable
        (exactInterfaceExteriorCode graph largerVertex) retain first last =
          true := by
      unfold forgottenCoordinateReachable
      rw [boolRelationReachable_eq_true_iff]
      exact hmiddle.mono fun before after hstep =>
        (interfaceExteriorFactoredStepBool_eq_true_iff
          (exactInterfaceExteriorCode graph largerVertex)
          before.1 after.1).2 hstep
    have hmiddleReach : (exteriorGraph graph retainedVertex).Reachable
        (largerVertex first.1) (largerVertex last.1) :=
      (forgottenCoordinateReachable_exact_eq_true_iff graph largerVertex
        retainedVertex retain hsome hnone first last).1 hmiddleBool
    exact ⟨entry, exit, hentryOutside, hexitOutside, hentry,
      hentryReach.trans (hmiddleReach.trans hexitReach), hexit⟩

private theorem survivesMask_of_outside_partialTarget
    {N Larger Retained : Type*} [Fintype Retained] [DecidableEq Larger]
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    {vertex : N} (houtside : OutsideInterface retainedVertex vertex) :
    survivesMask largerVertex (partialRetainedCoordinateMask retain) vertex := by
  intro slot hremoved heq
  rw [partialRetainedCoordinateMask_eq_true_iff] at hremoved
  rcases hremoved with ⟨retained, hretained⟩
  exact houtside retained (heq.trans (hsome retained slot hretained))

/-- Traversal invariant for decomposing one literal target-exterior walk.
Before the first forgotten coordinate, the walk lies entirely in the old
exterior.  Afterwards it stores the first/last forgotten coordinates and an
optional trailing old-exterior segment. -/
private def PartialExteriorTraversalState
    {N Larger Retained : Type*} [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (largerLeft : Larger) (entry current : N) : Prop :=
  (OutsideInterface largerVertex entry ∧
    OutsideInterface largerVertex current ∧
    graph.Adj (largerVertex largerLeft) entry ∧
    (exteriorGraph graph largerVertex).Reachable entry current) ∨
  ∃ first last : CodeSurvivingSlot
      (exactInterfaceExteriorCode graph largerVertex) retain,
    InterfaceExteriorFactoredStep
      (exactInterfaceExteriorCode graph largerVertex) largerLeft first.1 ∧
    Relation.ReflTransGen
      (fun before after : CodeSurvivingSlot
          (exactInterfaceExteriorCode graph largerVertex) retain =>
        InterfaceExteriorFactoredStep
          (exactInterfaceExteriorCode graph largerVertex)
          before.1 after.1)
      first last ∧
    (largerVertex last.1 = current ∨
      ∃ trailingEntry,
        OutsideInterface largerVertex trailingEntry ∧
        OutsideInterface largerVertex current ∧
        graph.Adj (largerVertex last.1) trailingEntry ∧
        (exteriorGraph graph largerVertex).Reachable trailingEntry current)

private theorem partialExteriorTraversalState_start
    {N Larger Retained : Type*} [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    (left : Retained) (largerLeft : Larger)
    (hleft : retain left = some largerLeft)
    (entry : N) (hentryOutside : OutsideInterface retainedVertex entry)
    (hentry : graph.Adj (retainedVertex left) entry) :
    PartialExteriorTraversalState graph largerVertex retainedVertex retain
      largerLeft entry entry := by
  by_cases hentryLarger : OutsideInterface largerVertex entry
  · exact Or.inl ⟨hentryLarger, hentryLarger, by
      rw [hsome left largerLeft hleft]
      exact hentry, SimpleGraph.Reachable.rfl⟩
  · simp only [OutsideInterface, not_forall, not_not] at hentryLarger
    rcases hentryLarger with ⟨entrySlot, hentrySlot⟩
    have hsurvives : survivesMask largerVertex
        (partialRetainedCoordinateMask retain) (largerVertex entrySlot) := by
      rw [← hentrySlot]
      exact survivesMask_of_outside_partialTarget largerVertex retainedVertex
        retain hsome hentryOutside
    let first : CodeSurvivingSlot
        (exactInterfaceExteriorCode graph largerVertex) retain :=
      ⟨entrySlot,
        (codeSurvivesPartialRetained_exact_iff graph largerVertex retain
          entrySlot).2 hsurvives⟩
    have hfirst : InterfaceExteriorFactoredStep
        (exactInterfaceExteriorCode graph largerVertex) largerLeft first.1 :=
      (exactInterfaceExteriorCode_step_iff graph largerVertex largerLeft
        first.1).2 (Or.inr (Or.inl (by
          rw [hsome left largerLeft hleft, ← hentrySlot]
          exact hentry)))
    exact Or.inr ⟨first, first, hfirst, Relation.ReflTransGen.refl,
      Or.inl hentrySlot.symm⟩

private theorem partialExteriorTraversalState_step
    {N Larger Retained : Type*} [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    (largerLeft : Larger) (entry : N) {current next : N}
    (hstate : PartialExteriorTraversalState graph largerVertex retainedVertex
      retain largerLeft entry current)
    (hstep : (exteriorGraph graph retainedVertex).Adj current next) :
    PartialExteriorTraversalState graph largerVertex retainedVertex retain
      largerLeft entry next := by
  by_cases hnextLarger : OutsideInterface largerVertex next
  · rcases hstate with hold | hforgotten
    · rcases hold with
        ⟨hentryLarger, hcurrentLarger, hentry, hreach⟩
      have hnextReach : (exteriorGraph graph largerVertex).Reachable
          current next :=
        SimpleGraph.Adj.reachable
          ⟨hstep.1, hcurrentLarger, hnextLarger⟩
      exact Or.inl ⟨hentryLarger, hnextLarger, hentry,
        hreach.trans hnextReach⟩
    · rcases hforgotten with
        ⟨first, last, hfirst, hmiddle, htail⟩
      rcases htail with hcurrent | htrailing
      · refine Or.inr ⟨first, last, hfirst, hmiddle, Or.inr
          ⟨next, hnextLarger, hnextLarger, ?_,
            SimpleGraph.Reachable.rfl⟩⟩
        simpa [hcurrent] using hstep.1
      · rcases htrailing with
          ⟨trailingEntry, htrailingEntry, hcurrentLarger,
            htrailing, hreach⟩
        have hnextReach : (exteriorGraph graph largerVertex).Reachable
            current next :=
          SimpleGraph.Adj.reachable
            ⟨hstep.1, hcurrentLarger, hnextLarger⟩
        exact Or.inr ⟨first, last, hfirst, hmiddle, Or.inr
          ⟨trailingEntry, htrailingEntry, hnextLarger, htrailing,
            hreach.trans hnextReach⟩⟩
  · simp only [OutsideInterface, not_forall, not_not] at hnextLarger
    rcases hnextLarger with ⟨nextSlot, hnextSlot⟩
    have hsurvives : survivesMask largerVertex
        (partialRetainedCoordinateMask retain) (largerVertex nextSlot) := by
      rw [← hnextSlot]
      exact survivesMask_of_outside_partialTarget largerVertex retainedVertex
        retain hsome hstep.2.2
    let nextCoordinate : CodeSurvivingSlot
        (exactInterfaceExteriorCode graph largerVertex) retain :=
      ⟨nextSlot,
        (codeSurvivesPartialRetained_exact_iff graph largerVertex retain
          nextSlot).2 hsurvives⟩
    rcases hstate with hold | hforgotten
    · rcases hold with
        ⟨hentryLarger, hcurrentLarger, hentry, hreach⟩
      have hfirst : InterfaceExteriorFactoredStep
          (exactInterfaceExteriorCode graph largerVertex)
          largerLeft nextCoordinate.1 :=
        (exactInterfaceExteriorCode_step_iff graph largerVertex largerLeft
          nextCoordinate.1).2 (Or.inr (Or.inr
            ⟨entry, current, hentryLarger, hcurrentLarger, hentry, hreach,
              by simpa [nextCoordinate, hnextSlot] using hstep.1⟩))
      exact Or.inr ⟨nextCoordinate, nextCoordinate, hfirst,
        Relation.ReflTransGen.refl, Or.inl hnextSlot.symm⟩
    · rcases hforgotten with
        ⟨first, last, hfirst, hmiddle, htail⟩
      rcases htail with hcurrent | htrailing
      · have hnextStep : InterfaceExteriorFactoredStep
            (exactInterfaceExteriorCode graph largerVertex)
            last.1 nextCoordinate.1 :=
          (exactInterfaceExteriorCode_step_iff graph largerVertex last.1
            nextCoordinate.1).2 (Or.inr (Or.inl (by
              simpa [hcurrent, nextCoordinate, hnextSlot] using hstep.1)))
        exact Or.inr ⟨first, nextCoordinate, hfirst,
          hmiddle.tail hnextStep, Or.inl hnextSlot.symm⟩
      · rcases htrailing with
          ⟨trailingEntry, htrailingEntry, hcurrentLarger,
            htrailing, hreach⟩
        have hnextStep : InterfaceExteriorFactoredStep
            (exactInterfaceExteriorCode graph largerVertex)
            last.1 nextCoordinate.1 :=
          (exactInterfaceExteriorCode_step_iff graph largerVertex last.1
            nextCoordinate.1).2 (Or.inr (Or.inr
              ⟨trailingEntry, current, htrailingEntry, hcurrentLarger,
                htrailing, hreach,
                by simpa [nextCoordinate, hnextSlot] using hstep.1⟩))
        exact Or.inr ⟨first, nextCoordinate, hfirst,
          hmiddle.tail hnextStep, Or.inl hnextSlot.symm⟩

/-- Completeness of the contracted exterior formula for an exact graph code. -/
theorem partialExteriorConnection_exact_complete
    {N Larger Retained : Type*} [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    (_hnone : ∀ retained, retain retained = none →
      retainedVertex retained ∉ graph.support)
    (left right : Retained) (largerLeft largerRight : Larger)
    (hleft : retain left = some largerLeft)
    (hright : retain right = some largerRight)
    (hliteral : ∃ entry exit : N,
      OutsideInterface retainedVertex entry ∧
      OutsideInterface retainedVertex exit ∧
      graph.Adj (retainedVertex left) entry ∧
      (exteriorGraph graph retainedVertex).Reachable entry exit ∧
      graph.Adj exit (retainedVertex right)) :
    PartialExteriorConnection
      (exactInterfaceExteriorCode graph largerVertex) retain
      largerLeft largerRight := by
  rcases hliteral with
    ⟨entry, exit, hentryOutside, _hexitOutside, hentry, hreach, hexit⟩
  have hpath := (SimpleGraph.reachable_iff_reflTransGen entry exit).mp hreach
  have hstateOfPath : ∀ {current : N},
      Relation.ReflTransGen
          (exteriorGraph graph retainedVertex).Adj entry current →
        PartialExteriorTraversalState graph largerVertex retainedVertex retain
          largerLeft entry current := by
    intro current hcurrent
    induction hcurrent with
    | refl =>
        exact partialExteriorTraversalState_start graph largerVertex
          retainedVertex retain hsome left largerLeft hleft entry
          hentryOutside hentry
    | tail hprefix hstep ih =>
        exact partialExteriorTraversalState_step graph largerVertex
          retainedVertex retain hsome largerLeft entry ih hstep
  have hstate := hstateOfPath hpath
  rcases hstate with hold | hforgotten
  · rcases hold with
      ⟨hentryLarger, hexitLarger, hentryLargerAdj, hreachLarger⟩
    apply Or.inl
    simp only [exactInterfaceExteriorCode, decide_eq_true_eq]
    refine ⟨entry, exit, hentryLarger, hexitLarger, hentryLargerAdj,
      hreachLarger, ?_⟩
    rw [hsome right largerRight hright]
    exact hexit
  · rcases hforgotten with
      ⟨first, last, hfirst, hmiddle, htail⟩
    have hlast : InterfaceExteriorFactoredStep
        (exactInterfaceExteriorCode graph largerVertex)
        last.1 largerRight := by
      rcases htail with hexitAtLast | htrailing
      · exact (exactInterfaceExteriorCode_step_iff graph largerVertex last.1
          largerRight).2 (Or.inr (Or.inl (by
            rw [hexitAtLast, hsome right largerRight hright]
            exact hexit)))
      · rcases htrailing with
          ⟨trailingEntry, htrailingEntry, hexitLarger,
            htrailing, hreachLarger⟩
        exact (exactInterfaceExteriorCode_step_iff graph largerVertex last.1
          largerRight).2 (Or.inr (Or.inr
            ⟨trailingEntry, exit, htrailingEntry, hexitLarger,
              htrailing, hreachLarger, by
                rw [hsome right largerRight hright]
                exact hexit⟩))
    exact Or.inr ⟨first, last, hfirst, hmiddle, hlast⟩

/-- Exact contraction theorem: the finite formula is equivalent to the
literal exterior-connection row of the partially reindexed target interface. -/
theorem partialExteriorConnection_exact_iff
    {N Larger Retained : Type*} [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    (hnone : ∀ retained, retain retained = none →
      retainedVertex retained ∉ graph.support)
    (left right : Retained) (largerLeft largerRight : Larger)
    (hleft : retain left = some largerLeft)
    (hright : retain right = some largerRight) :
    PartialExteriorConnection
        (exactInterfaceExteriorCode graph largerVertex) retain
        largerLeft largerRight ↔
      ∃ entry exit : N,
        OutsideInterface retainedVertex entry ∧
        OutsideInterface retainedVertex exit ∧
        graph.Adj (retainedVertex left) entry ∧
        (exteriorGraph graph retainedVertex).Reachable entry exit ∧
        graph.Adj exit (retainedVertex right) := by
  exact ⟨partialExteriorConnection_exact_sound graph largerVertex
      retainedVertex retain hsome hnone left right largerLeft largerRight
      hleft hright,
    partialExteriorConnection_exact_complete graph largerVertex retainedVertex
      retain hsome hnone left right largerLeft largerRight hleft hright⟩

/-- The contracted exterior row.  This is executable: it enumerates the finite
forgotten-coordinate carrier and uses the verified Boolean closure algorithm.
Unmapped target coordinates are inactive and therefore have a false row. -/
def partialReindexedExteriorConnected
    {Larger Retained : Type*} [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained]
    (code : BoundedInterfaceExteriorCode Larger)
    (retain : Retained → Option Larger)
    (left right : Retained) : Bool :=
  match retain left, retain right with
  | some largerLeft, some largerRight =>
      decide
        (code.exteriorConnected largerLeft largerRight = true ∨
          ∃ first last : CodeSurvivingSlot code retain,
            interfaceExteriorFactoredStepBool code largerLeft first.1 = true ∧
            forgottenCoordinateReachable code retain first last = true ∧
            interfaceExteriorFactoredStepBool code last.1 largerRight = true)
  | _, _ => false

private theorem partialExteriorConnection_bool_iff
    {Larger Retained : Type*} [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained]
    (code : BoundedInterfaceExteriorCode Larger)
    (retain : Retained → Option Larger)
    (largerLeft largerRight : Larger) :
    (code.exteriorConnected largerLeft largerRight = true ∨
      ∃ first last : CodeSurvivingSlot code retain,
        interfaceExteriorFactoredStepBool code largerLeft first.1 = true ∧
        forgottenCoordinateReachable code retain first last = true ∧
        interfaceExteriorFactoredStepBool code last.1 largerRight = true) ↔
      PartialExteriorConnection code retain largerLeft largerRight := by
  constructor
  · rintro (hold | ⟨first, last, hfirst, hmiddle, hlast⟩)
    · exact Or.inl hold
    · exact Or.inr ⟨first, last,
        (interfaceExteriorFactoredStepBool_eq_true_iff
          code largerLeft first.1).1 hfirst,
        (boolRelationReachable_eq_true_iff
          (fun before after : CodeSurvivingSlot code retain =>
            interfaceExteriorFactoredStepBool code before.1 after.1)
          first last).1 hmiddle |>.mono fun before after hstep =>
            (interfaceExteriorFactoredStepBool_eq_true_iff
              code before.1 after.1).1 hstep,
        (interfaceExteriorFactoredStepBool_eq_true_iff
          code last.1 largerRight).1 hlast⟩
  · rintro (hold | ⟨first, last, hfirst, hmiddle, hlast⟩)
    · exact Or.inl hold
    · refine Or.inr ⟨first, last,
        (interfaceExteriorFactoredStepBool_eq_true_iff
          code largerLeft first.1).2 hfirst, ?_,
        (interfaceExteriorFactoredStepBool_eq_true_iff
          code last.1 largerRight).2 hlast⟩
      unfold forgottenCoordinateReachable
      rw [boolRelationReachable_eq_true_iff]
      exact hmiddle.mono fun before after hstep =>
        (interfaceExteriorFactoredStepBool_eq_true_iff
          code before.1 after.1).2 hstep

/-- The executable contracted row says exactly the proof-facing contraction
formula. -/
theorem partialReindexedExteriorConnected_eq_true_iff
    {Larger Retained : Type*} [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained]
    (code : BoundedInterfaceExteriorCode Larger)
    (retain : Retained → Option Larger)
    (left right : Retained) :
    partialReindexedExteriorConnected code retain left right = true ↔
      ∃ largerLeft largerRight,
        retain left = some largerLeft ∧
        retain right = some largerRight ∧
        PartialExteriorConnection code retain largerLeft largerRight := by
  classical
  cases hleft : retain left with
  | none =>
      simp [partialReindexedExteriorConnected, hleft]
  | some largerLeft =>
      cases hright : retain right with
      | none =>
          simp [partialReindexedExteriorConnected, hleft, hright]
      | some largerRight =>
          simp only [partialReindexedExteriorConnected, hleft, hright,
            decide_eq_true_eq]
          rw [partialExteriorConnection_bool_iff]
          simp

/-- The executable contracted exterior row is exact on an exact larger code. -/
theorem partialReindexedExteriorConnected_exact_eq_true_iff
    {N Larger Retained : Type*} [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    (hnone : ∀ retained, retain retained = none →
      retainedVertex retained ∉ graph.support)
    (left right : Retained) :
    partialReindexedExteriorConnected
        (exactInterfaceExteriorCode graph largerVertex) retain left right =
          true ↔
      ∃ entry exit : N,
        OutsideInterface retainedVertex entry ∧
        OutsideInterface retainedVertex exit ∧
        graph.Adj (retainedVertex left) entry ∧
        (exteriorGraph graph retainedVertex).Reachable entry exit ∧
        graph.Adj exit (retainedVertex right) := by
  constructor
  · intro hcomputed
    rcases (partialReindexedExteriorConnected_eq_true_iff
      (exactInterfaceExteriorCode graph largerVertex) retain left right).1
        hcomputed with
      ⟨largerLeft, largerRight, hleft, hright, hconnection⟩
    exact partialExteriorConnection_exact_sound graph largerVertex
      retainedVertex retain hsome hnone left right largerLeft largerRight
      hleft hright hconnection
  · intro hliteral
    cases hleft : retain left with
    | none =>
        rcases hliteral with
          ⟨entry, _exit, _hentryOutside, _hexitOutside, hentry, _hreach,
            _hexit⟩
        exact (hnone left hleft ⟨entry, hentry⟩).elim
    | some largerLeft =>
        cases hright : retain right with
        | none =>
            rcases hliteral with
              ⟨_entry, exit, _hentryOutside, _hexitOutside, _hentry, _hreach,
                hexit⟩
            exact (hnone right hright ⟨exit, hexit.symm⟩).elim
        | some largerRight =>
            apply (partialReindexedExteriorConnected_eq_true_iff
              (exactInterfaceExteriorCode graph largerVertex) retain
              left right).2
            exact ⟨largerLeft, largerRight, hleft, hright,
              partialExteriorConnection_exact_complete graph largerVertex
                retainedVertex retain hsome hnone left right largerLeft
                largerRight hleft hright hliteral⟩

/-- Assemble the executable contracted exterior row with the exact equality
and direct-adjacency rows. -/
def partialContractedInterfaceExteriorCode
    {Larger Retained : Type*} [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained] [DecidableEq Retained]
    (code : BoundedInterfaceExteriorCode Larger)
    (retain : Retained → Option Larger) :
    BoundedInterfaceExteriorCode Retained :=
  partialReindexedInterfaceExteriorCode code retain
    (partialReindexedExteriorConnected code retain)

/-- Crown exactness theorem for interface forgetting: applying the executable
three-row contraction to an exact larger code yields an exact primitive-step
relation for the literal target interface. -/
theorem partialContractedInterfaceExteriorCode_exact_step_iff
    {N Larger Retained : Type*} [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained] [DecidableEq Retained]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hinjective : Function.Injective retainedVertex)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    (hnone : ∀ retained, retain retained = none →
      retainedVertex retained ∉ graph.support)
    (left right : Retained) :
    InterfaceExteriorFactoredStep
        (partialContractedInterfaceExteriorCode
          (exactInterfaceExteriorCode graph largerVertex) retain)
        left right ↔
      InterfaceExteriorStep graph retainedVertex left right := by
  exact partialReindexedInterfaceExteriorCode_step_iff_of_exterior_exact
    graph largerVertex retainedVertex retain hinjective hsome hnone
    (partialReindexedExteriorConnected
      (exactInterfaceExteriorCode graph largerVertex) retain)
    (partialReindexedExteriorConnected_exact_eq_true_iff graph largerVertex
      retainedVertex retain hsome hnone)
    left right

end GoertzelV24InterfaceDeletionComponentFactorForgetExterior

end Mettapedia.GraphTheory.FourColor
