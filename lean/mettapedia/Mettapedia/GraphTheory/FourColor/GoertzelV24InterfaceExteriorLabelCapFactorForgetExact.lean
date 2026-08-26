import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorLabelCapFactorForget

/-!
# Exactness of exterior label-cap contraction

The executable contraction graph has two finite vertex kinds: forgotten
larger-interface coordinates and named components of the old strict exterior.
This file relates those atoms to vertices of the literal strict exterior after
partial interface forgetting.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InterfaceExteriorLabelCapFactorForgetExact

open GoertzelV24FiniteBoolRelationClosure
open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorForget
open GoertzelV24InterfaceDeletionComponentFactorForgetExterior
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24InterfaceExteriorLabelCapFactorForget
open SimpleGraph

/-- Literal graph vertex denoted by a contraction atom. -/
def exteriorLabelCapContractionAtomVertex
    {N Larger Incidence : Type*}
    (largerVertex : Larger → N) (incidenceVertex : Incidence → N) :
    ExteriorLabelCapContractionAtom Larger Incidence → N
  | .inl slot => largerVertex slot
  | .inr incidence => incidenceVertex incidence

/-- The old strict exterior embeds in the strict exterior of a partially
forgotten interface. -/
theorem exteriorGraph_larger_le_partialRetained
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

/-- Every executable atom step is a literal path in the strict exterior of the
partially retained interface. -/
theorem exteriorLabelCapContractionAtomStep_reachable_of_exact
    {N Larger Retained Incidence : Type*}
    [Fintype N] [DecidableEq N]
    [Fintype Larger] [DecidableEq Larger] [Fintype Retained]
    [Fintype Incidence] [LinearOrder Incidence]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    (hnone : ∀ retained, retain retained = none →
      retainedVertex retained ∉ graph.support)
    (incidenceSlot : Incidence → Larger)
    (incidenceVertex : Incidence → N)
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (hconnectivity : code.connectivity =
      exactInterfaceExteriorCode graph largerVertex)
    (hincidencePresent : ∀ incidence,
      code.incidencePresent incidence = true ↔
        ExteriorIncidencePresent graph largerVertex incidenceSlot
          incidenceVertex incidence)
    (hincidenceConnected : ∀ first second,
      code.incidenceConnected first second = true ↔
        ExteriorIncidencePresent graph largerVertex incidenceSlot
            incidenceVertex first ∧
          ExteriorIncidencePresent graph largerVertex incidenceSlot
            incidenceVertex second ∧
          (exteriorGraph graph largerVertex).Reachable
            (incidenceVertex first) (incidenceVertex second))
    (left right : ExteriorLabelCapContractionAtom Larger Incidence)
    (hstep : exteriorLabelCapContractionAtomStep
      code retain incidenceSlot left right = true) :
    (exteriorGraph graph retainedVertex).Reachable
      (exteriorLabelCapContractionAtomVertex largerVertex incidenceVertex left)
      (exteriorLabelCapContractionAtomVertex largerVertex incidenceVertex
        right) := by
  classical
  cases left with
  | inl leftSlot =>
      cases right with
      | inl rightSlot =>
          change (exteriorLabelCapContractionAtomPresent code retain
              (.inl leftSlot) &&
            exteriorLabelCapContractionAtomPresent code retain
              (.inl rightSlot) &&
            interfaceExteriorFactoredStepBool code.connectivity leftSlot
              rightSlot) = true at hstep
          have hpair := (Bool.and_eq_true_iff.mp hstep).1
          have hleft := (Bool.and_eq_true_iff.mp hpair).1
          have hright := (Bool.and_eq_true_iff.mp hpair).2
          have hprimitive := (Bool.and_eq_true_iff.mp hstep).2
          change (code.interfacePresent leftSlot &&
            codeSurvivesPartialRetained code.connectivity retain leftSlot) =
              true at hleft
          change (code.interfacePresent rightSlot &&
            codeSurvivesPartialRetained code.connectivity retain rightSlot) =
              true at hright
          have hleftSurvives := (Bool.and_eq_true_iff.mp hleft).2
          have hrightSurvives := (Bool.and_eq_true_iff.mp hright).2
          have hreachable : forgottenCoordinateReachable
              (exactInterfaceExteriorCode graph largerVertex) retain
              ⟨leftSlot, by simpa [hconnectivity] using hleftSurvives⟩
              ⟨rightSlot, by simpa [hconnectivity] using hrightSurvives⟩ =
                true := by
            unfold forgottenCoordinateReachable
            rw [boolRelationReachable_eq_true_iff]
            exact Relation.ReflTransGen.single (by
              simpa [hconnectivity] using hprimitive)
          exact (forgottenCoordinateReachable_exact_eq_true_iff graph
            largerVertex retainedVertex retain hsome hnone
              ⟨leftSlot, by simpa [hconnectivity] using hleftSurvives⟩
              ⟨rightSlot, by simpa [hconnectivity] using hrightSurvives⟩).1
                hreachable
      | inr rightIncidence =>
          change (exteriorLabelCapContractionAtomPresent code retain
              (.inl leftSlot) &&
            exteriorLabelCapContractionAtomPresent code retain
              (.inr rightIncidence) &&
            decide (leftSlot = incidenceSlot rightIncidence)) = true at hstep
          have hpair := (Bool.and_eq_true_iff.mp hstep).1
          have hleft := (Bool.and_eq_true_iff.mp hpair).1
          have hright := (Bool.and_eq_true_iff.mp hpair).2
          have hslot : leftSlot = incidenceSlot rightIncidence :=
            of_decide_eq_true (Bool.and_eq_true_iff.mp hstep).2
          change (code.interfacePresent leftSlot &&
            codeSurvivesPartialRetained code.connectivity retain leftSlot) =
              true at hleft
          change code.incidencePresent rightIncidence = true at hright
          have hleftSurvives := (Bool.and_eq_true_iff.mp hleft).2
          have hrightLiteral := (hincidencePresent rightIncidence).1 hright
          have hleftOutside : OutsideInterface retainedVertex
              (largerVertex leftSlot) :=
            outsideInterface_of_survives_partialRetained_of_mem_support graph
              largerVertex retainedVertex retain hsome hnone leftSlot
                ((codeSurvivesPartialRetained_exact_iff graph largerVertex
                  retain leftSlot).1 (by
                    simpa [hconnectivity] using hleftSurvives))
                ⟨incidenceVertex rightIncidence, by
                  simpa [hslot] using hrightLiteral.2⟩
          have hrightOutside : OutsideInterface retainedVertex
              (incidenceVertex rightIncidence) :=
            outsideInterface_of_outsideLarger_partialRetained_of_mem_support
              graph largerVertex retainedVertex retain hsome hnone
                (incidenceVertex rightIncidence) hrightLiteral.1
                ⟨largerVertex leftSlot, by
                  simpa [hslot] using hrightLiteral.2.symm⟩
          exact SimpleGraph.Adj.reachable ⟨by
            simpa [exteriorLabelCapContractionAtomVertex, hslot] using
              hrightLiteral.2, hleftOutside, hrightOutside⟩
  | inr leftIncidence =>
      cases right with
      | inl rightSlot =>
          change (exteriorLabelCapContractionAtomPresent code retain
              (.inr leftIncidence) &&
            exteriorLabelCapContractionAtomPresent code retain
              (.inl rightSlot) &&
            decide (incidenceSlot leftIncidence = rightSlot)) = true at hstep
          have hpair := (Bool.and_eq_true_iff.mp hstep).1
          have hleft := (Bool.and_eq_true_iff.mp hpair).1
          have hright := (Bool.and_eq_true_iff.mp hpair).2
          have hslot : incidenceSlot leftIncidence = rightSlot :=
            of_decide_eq_true (Bool.and_eq_true_iff.mp hstep).2
          change code.incidencePresent leftIncidence = true at hleft
          change (code.interfacePresent rightSlot &&
            codeSurvivesPartialRetained code.connectivity retain rightSlot) =
              true at hright
          have hrightSurvives := (Bool.and_eq_true_iff.mp hright).2
          have hleftLiteral := (hincidencePresent leftIncidence).1 hleft
          have hleftOutside : OutsideInterface retainedVertex
              (incidenceVertex leftIncidence) :=
            outsideInterface_of_outsideLarger_partialRetained_of_mem_support
              graph largerVertex retainedVertex retain hsome hnone
                (incidenceVertex leftIncidence) hleftLiteral.1
                ⟨largerVertex rightSlot, by
                  simpa [hslot] using hleftLiteral.2.symm⟩
          have hrightOutside : OutsideInterface retainedVertex
              (largerVertex rightSlot) :=
            outsideInterface_of_survives_partialRetained_of_mem_support graph
              largerVertex retainedVertex retain hsome hnone rightSlot
                ((codeSurvivesPartialRetained_exact_iff graph largerVertex
                  retain rightSlot).1 (by
                    simpa [hconnectivity] using hrightSurvives))
                ⟨incidenceVertex leftIncidence, by
                  simpa [hslot] using hleftLiteral.2⟩
          exact SimpleGraph.Adj.reachable ⟨by
            simpa [exteriorLabelCapContractionAtomVertex, hslot] using
              hleftLiteral.2.symm, hleftOutside, hrightOutside⟩
      | inr rightIncidence =>
          change (exteriorLabelCapContractionAtomPresent code retain
              (.inr leftIncidence) &&
            exteriorLabelCapContractionAtomPresent code retain
              (.inr rightIncidence) &&
            code.incidenceConnected leftIncidence rightIncidence) = true at hstep
          have hconnected := (Bool.and_eq_true_iff.mp hstep).2
          have hliteral :=
            (hincidenceConnected leftIncidence rightIncidence).1 hconnected
          exact hliteral.2.2.mono
            (exteriorGraph_larger_le_partialRetained graph largerVertex
              retainedVertex retain hsome hnone)

/-- Executable atom reachability is sound for literal target-exterior
reachability. -/
theorem exteriorLabelCapContractionAtomReachable_sound_of_exact
    {N Larger Retained Incidence : Type*}
    [Fintype N] [DecidableEq N]
    [Fintype Larger] [DecidableEq Larger] [Fintype Retained]
    [Fintype Incidence] [LinearOrder Incidence]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    (hnone : ∀ retained, retain retained = none →
      retainedVertex retained ∉ graph.support)
    (incidenceSlot : Incidence → Larger)
    (incidenceVertex : Incidence → N)
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (hconnectivity : code.connectivity =
      exactInterfaceExteriorCode graph largerVertex)
    (hincidencePresent : ∀ incidence,
      code.incidencePresent incidence = true ↔
        ExteriorIncidencePresent graph largerVertex incidenceSlot
          incidenceVertex incidence)
    (hincidenceConnected : ∀ first second,
      code.incidenceConnected first second = true ↔
        ExteriorIncidencePresent graph largerVertex incidenceSlot
            incidenceVertex first ∧
          ExteriorIncidencePresent graph largerVertex incidenceSlot
            incidenceVertex second ∧
          (exteriorGraph graph largerVertex).Reachable
            (incidenceVertex first) (incidenceVertex second))
    (left right : ExteriorLabelCapContractionAtom Larger Incidence)
    (hreachable : exteriorLabelCapContractionAtomReachable
      code retain incidenceSlot left right = true) :
    (exteriorGraph graph retainedVertex).Reachable
      (exteriorLabelCapContractionAtomVertex largerVertex incidenceVertex left)
      (exteriorLabelCapContractionAtomVertex largerVertex incidenceVertex
        right) := by
  rw [exteriorLabelCapContractionAtomReachable,
    boolRelationReachable_eq_true_iff] at hreachable
  exact Relation.ReflTransGen.trans_induction_on
    (motive := fun {first second} _ =>
      (exteriorGraph graph retainedVertex).Reachable
        (exteriorLabelCapContractionAtomVertex largerVertex incidenceVertex
          first)
        (exteriorLabelCapContractionAtomVertex largerVertex incidenceVertex
          second))
    hreachable (fun _ => SimpleGraph.Reachable.rfl)
    (fun hstep =>
      exteriorLabelCapContractionAtomStep_reachable_of_exact graph largerVertex
        retainedVertex retain hsome hnone incidenceSlot incidenceVertex code
          hconnectivity hincidencePresent hincidenceConnected _ _ hstep)
    (fun _ _ hfirst hsecond => hfirst.trans hsecond)

/-- A vertex outside the retained interface survives the corresponding mask
on the larger coordinate family. -/
theorem survivesMask_of_outside_partialRetained
    {N Larger Retained : Type*} [Fintype Retained] [DecidableEq Larger]
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    {vertex : N} (houtside : OutsideInterface retainedVertex vertex) :
    survivesMask largerVertex (partialRetainedCoordinateMask retain) vertex := by
  intro slot hremoved heq
  rw [partialRetainedCoordinateMask_eq_true_iff] at hremoved
  rcases hremoved with ⟨retained, hretain⟩
  exact houtside retained (heq.trans (hsome retained slot hretain))

/-- Exterior-graph reachability preserves strict-exterior membership. -/
theorem outsideInterface_of_exteriorGraph_reachable
    {N Interface : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) {first second : N}
    (hfirst : OutsideInterface interfaceVertex first)
    (hreachable : (exteriorGraph graph interfaceVertex).Reachable first second) :
    OutsideInterface interfaceVertex second := by
  have hpath :=
    (SimpleGraph.reachable_iff_reflTransGen first second).mp hreachable
  exact Relation.ReflTransGen.trans_induction_on
    (motive := fun {left right} _ =>
      OutsideInterface interfaceVertex left →
        OutsideInterface interfaceVertex right)
    hpath (fun _ houtside => houtside)
    (fun hadj _ => hadj.2.2)
    (fun _ _ hleft hright houtside => hright (hleft houtside)) hfirst

/-- Propositional path relation underlying the executable atom closure. -/
abbrev ExteriorLabelCapContractionAtomPath
    {Larger Retained Incidence : Type*} [Fintype Retained]
    [DecidableEq Larger]
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (retain : Retained → Option Larger)
    (incidenceSlot : Incidence → Larger) :=
  Relation.ReflTransGen
    (fun first second : ExteriorLabelCapContractionAtom Larger Incidence =>
      exteriorLabelCapContractionAtomStep code retain incidenceSlot first
        second = true)

theorem exteriorLabelCapContractionAtomStep_inl_inl
    {Larger Retained Incidence : Type*} [Fintype Retained]
    [DecidableEq Larger]
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (retain : Retained → Option Larger)
    (incidenceSlot : Incidence → Larger) (left right : Larger)
    (hleft : exteriorLabelCapContractionAtomPresent code retain (.inl left) =
      true)
    (hright : exteriorLabelCapContractionAtomPresent code retain (.inl right) =
      true)
    (hstep : interfaceExteriorFactoredStepBool code.connectivity left right =
      true) :
    exteriorLabelCapContractionAtomStep code retain incidenceSlot (.inl left)
        (.inl right) = true := by
  simp [exteriorLabelCapContractionAtomStep, hleft, hright, hstep]

theorem exteriorLabelCapContractionAtomStep_inl_inr
    {Larger Retained Incidence : Type*} [Fintype Retained]
    [DecidableEq Larger]
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (retain : Retained → Option Larger)
    (incidenceSlot : Incidence → Larger) (left : Larger) (right : Incidence)
    (hleft : exteriorLabelCapContractionAtomPresent code retain (.inl left) =
      true)
    (hright : exteriorLabelCapContractionAtomPresent code retain (.inr right) =
      true)
    (hslot : left = incidenceSlot right) :
    exteriorLabelCapContractionAtomStep code retain incidenceSlot (.inl left)
        (.inr right) = true := by
  subst left
  simp [exteriorLabelCapContractionAtomStep, hleft, hright]

theorem exteriorLabelCapContractionAtomStep_inr_inl
    {Larger Retained Incidence : Type*} [Fintype Retained]
    [DecidableEq Larger]
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (retain : Retained → Option Larger)
    (incidenceSlot : Incidence → Larger) (left : Incidence) (right : Larger)
    (hleft : exteriorLabelCapContractionAtomPresent code retain (.inr left) =
      true)
    (hright : exteriorLabelCapContractionAtomPresent code retain (.inl right) =
      true)
    (hslot : incidenceSlot left = right) :
    exteriorLabelCapContractionAtomStep code retain incidenceSlot (.inr left)
        (.inl right) = true := by
  subst right
  simp [exteriorLabelCapContractionAtomStep, hleft, hright]

theorem exteriorLabelCapContractionAtomStep_inr_inr
    {Larger Retained Incidence : Type*} [Fintype Retained]
    [DecidableEq Larger]
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (retain : Retained → Option Larger)
    (incidenceSlot : Incidence → Larger) (left right : Incidence)
    (hleft : exteriorLabelCapContractionAtomPresent code retain (.inr left) =
      true)
    (hright : exteriorLabelCapContractionAtomPresent code retain (.inr right) =
      true)
    (hconnected : code.incidenceConnected left right = true) :
    exteriorLabelCapContractionAtomStep code retain incidenceSlot (.inr left)
        (.inr right) = true := by
  simp [exteriorLabelCapContractionAtomStep, hleft, hright, hconnected]

/-- Traversal invariant for compressing a literal target-exterior walk.

The current literal vertex is either still in an old strict-exterior
component entered by a named incidence, or is exactly a live forgotten
coordinate.  In both cases an atom path from the fixed source has already been
constructed. -/
def ExteriorLabelCapContractionTraversalState
    {N Larger Retained Incidence : Type*} [Fintype Retained]
    [DecidableEq Larger]
    (graph : SimpleGraph N) (largerVertex : Larger → N)
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (retain : Retained → Option Larger)
    (incidenceSlot : Incidence → Larger)
    (incidenceVertex : Incidence → N)
    (source : ExteriorLabelCapContractionAtom Larger Incidence)
    (current : N) : Prop :=
  (∃ incidence,
    ExteriorLabelCapContractionAtomPath code retain incidenceSlot source
        (.inr incidence) ∧
      code.incidencePresent incidence = true ∧
      (exteriorGraph graph largerVertex).Reachable
        (incidenceVertex incidence) current) ∨
  ∃ slot,
    ExteriorLabelCapContractionAtomPath code retain incidenceSlot source
        (.inl slot) ∧
      exteriorLabelCapContractionAtomPresent code retain (.inl slot) = true ∧
      largerVertex slot = current

/-- The traversal invariant starts at any live contraction atom. -/
theorem exteriorLabelCapContractionTraversalState_start
    {N Larger Retained Incidence : Type*} [Fintype Retained]
    [DecidableEq Larger]
    (graph : SimpleGraph N) (largerVertex : Larger → N)
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (retain : Retained → Option Larger)
    (incidenceSlot : Incidence → Larger)
    (incidenceVertex : Incidence → N)
    (source : ExteriorLabelCapContractionAtom Larger Incidence)
    (hsource : exteriorLabelCapContractionAtomPresent code retain source =
      true) :
    ExteriorLabelCapContractionTraversalState graph largerVertex code retain
      incidenceSlot incidenceVertex source
      (exteriorLabelCapContractionAtomVertex largerVertex incidenceVertex
        source) := by
  cases source with
  | inl slot =>
      exact Or.inr ⟨slot, Relation.ReflTransGen.refl, hsource, rfl⟩
  | inr incidence =>
      exact Or.inl ⟨incidence, Relation.ReflTransGen.refl, hsource,
        SimpleGraph.Reachable.rfl⟩

/-- One literal target-exterior edge preserves the compressed traversal
invariant.  `hincidenceComplete` is the sole coverage hypothesis: every edge
from a larger interface coordinate into its strict exterior has a finite
incidence name. -/
theorem exteriorLabelCapContractionTraversalState_step
    {N Larger Retained Incidence : Type*}
    [Fintype Retained] [DecidableEq Larger]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    (incidenceSlot : Incidence → Larger)
    (incidenceVertex : Incidence → N)
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (hconnectivity : code.connectivity =
      exactInterfaceExteriorCode graph largerVertex)
    (hinterfacePresent : ∀ slot, largerVertex slot ∈ graph.support →
      code.interfacePresent slot = true)
    (hincidencePresent : ∀ incidence,
      code.incidencePresent incidence = true ↔
        ExteriorIncidencePresent graph largerVertex incidenceSlot
          incidenceVertex incidence)
    (hincidenceConnected : ∀ first second,
      code.incidenceConnected first second = true ↔
        ExteriorIncidencePresent graph largerVertex incidenceSlot
            incidenceVertex first ∧
          ExteriorIncidencePresent graph largerVertex incidenceSlot
            incidenceVertex second ∧
          (exteriorGraph graph largerVertex).Reachable
            (incidenceVertex first) (incidenceVertex second))
    (hincidenceComplete : ∀ slot outside,
      OutsideInterface largerVertex outside →
        graph.Adj (largerVertex slot) outside →
        ∃ incidence,
          incidenceSlot incidence = slot ∧ incidenceVertex incidence = outside)
    (source : ExteriorLabelCapContractionAtom Larger Incidence)
    {current next : N}
    (hstate : ExteriorLabelCapContractionTraversalState graph largerVertex code
      retain incidenceSlot incidenceVertex source current)
    (hstep : (exteriorGraph graph retainedVertex).Adj current next) :
    ExteriorLabelCapContractionTraversalState graph largerVertex code retain
      incidenceSlot incidenceVertex source next := by
  classical
  have nextSurvives : survivesMask largerVertex
      (partialRetainedCoordinateMask retain) next :=
    survivesMask_of_outside_partialRetained largerVertex retainedVertex retain
      hsome hstep.2.2
  by_cases hnextLarger : OutsideInterface largerVertex next
  · rcases hstate with hold | hforgotten
    · rcases hold with
        ⟨anchor, hpath, hanchorPresent, hanchorReach⟩
      have hanchorLiteral := (hincidencePresent anchor).1 hanchorPresent
      have hcurrentLarger : OutsideInterface largerVertex current :=
        outsideInterface_of_exteriorGraph_reachable graph largerVertex
          hanchorLiteral.1 hanchorReach
      exact Or.inl ⟨anchor, hpath, hanchorPresent,
        hanchorReach.trans (SimpleGraph.Adj.reachable
          ⟨hstep.1, hcurrentLarger, hnextLarger⟩)⟩
    · rcases hforgotten with
        ⟨currentSlot, hpath, hcurrentPresent, hcurrent⟩
      have hadj : graph.Adj (largerVertex currentSlot) next := by
        simpa [hcurrent] using hstep.1
      rcases hincidenceComplete currentSlot next hnextLarger hadj with
        ⟨incidence, hslot, hvertex⟩
      have hincidenceLiteral : ExteriorIncidencePresent graph largerVertex
          incidenceSlot incidenceVertex incidence := by
        constructor
        · simpa [hvertex] using hnextLarger
        · simpa [hslot, hvertex] using hadj
      have hincidencePresentTrue : code.incidencePresent incidence = true :=
        (hincidencePresent incidence).2 hincidenceLiteral
      have hatomStep : exteriorLabelCapContractionAtomStep code retain
          incidenceSlot (.inl currentSlot) (.inr incidence) = true :=
        exteriorLabelCapContractionAtomStep_inl_inr code retain incidenceSlot
          currentSlot incidence hcurrentPresent hincidencePresentTrue hslot.symm
      exact Or.inl ⟨incidence, hpath.tail hatomStep,
        hincidencePresentTrue, by simp [hvertex]⟩
  · simp only [OutsideInterface, not_forall, not_not] at hnextLarger
    rcases hnextLarger with ⟨nextSlot, hnext⟩
    have hnextSurvives : codeSurvivesPartialRetained code.connectivity retain
        nextSlot = true := by
      rw [hconnectivity,
        codeSurvivesPartialRetained_exact_iff graph largerVertex retain]
      simpa [hnext] using nextSurvives
    have hnextSupport : largerVertex nextSlot ∈ graph.support := by
      exact ⟨current, by simpa [hnext] using hstep.1.symm⟩
    have hnextPresent : exteriorLabelCapContractionAtomPresent code retain
        (.inl nextSlot) = true := by
      unfold exteriorLabelCapContractionAtomPresent
      exact Bool.and_eq_true_iff.mpr
        ⟨hinterfacePresent nextSlot hnextSupport, hnextSurvives⟩
    rcases hstate with hold | hforgotten
    · rcases hold with
        ⟨anchor, hpath, hanchorPresent, hanchorReach⟩
      have hanchorLiteral := (hincidencePresent anchor).1 hanchorPresent
      have hcurrentLarger : OutsideInterface largerVertex current :=
        outsideInterface_of_exteriorGraph_reachable graph largerVertex
          hanchorLiteral.1 hanchorReach
      have hadj : graph.Adj (largerVertex nextSlot) current := by
        simpa [hnext] using hstep.1.symm
      rcases hincidenceComplete nextSlot current hcurrentLarger hadj with
        ⟨incidence, hslot, hvertex⟩
      have hincidenceLiteral : ExteriorIncidencePresent graph largerVertex
          incidenceSlot incidenceVertex incidence := by
        constructor
        · simpa [hvertex] using hcurrentLarger
        · simpa [hslot, hvertex] using hadj
      have hincidencePresentTrue : code.incidencePresent incidence = true :=
        (hincidencePresent incidence).2 hincidenceLiteral
      have hconnected : code.incidenceConnected anchor incidence = true :=
        (hincidenceConnected anchor incidence).2
          ⟨hanchorLiteral, hincidenceLiteral, by simpa [hvertex] using
            hanchorReach⟩
      have hfirstStep : exteriorLabelCapContractionAtomStep code retain
          incidenceSlot (.inr anchor) (.inr incidence) = true :=
        exteriorLabelCapContractionAtomStep_inr_inr code retain incidenceSlot
          anchor incidence hanchorPresent hincidencePresentTrue hconnected
      have hsecondStep : exteriorLabelCapContractionAtomStep code retain
          incidenceSlot (.inr incidence) (.inl nextSlot) = true :=
        exteriorLabelCapContractionAtomStep_inr_inl code retain incidenceSlot
          incidence nextSlot hincidencePresentTrue hnextPresent hslot
      exact Or.inr ⟨nextSlot, (hpath.tail hfirstStep).tail hsecondStep,
        hnextPresent, hnext.symm⟩
    · rcases hforgotten with
        ⟨currentSlot, hpath, hcurrentPresent, hcurrent⟩
      have hadj : graph.Adj (largerVertex currentSlot)
          (largerVertex nextSlot) := by
        simpa [hcurrent, hnext] using hstep.1
      have hprimitive : interfaceExteriorFactoredStepBool code.connectivity
          currentSlot nextSlot = true := by
        rw [interfaceExteriorFactoredStepBool_eq_true_iff, hconnectivity,
          exactInterfaceExteriorCode_step_iff]
        exact Or.inr (Or.inl hadj)
      have hatomStep : exteriorLabelCapContractionAtomStep code retain
          incidenceSlot (.inl currentSlot) (.inl nextSlot) = true :=
        exteriorLabelCapContractionAtomStep_inl_inl code retain incidenceSlot
          currentSlot nextSlot hcurrentPresent hnextPresent hprimitive
      exact Or.inr ⟨nextSlot, hpath.tail hatomStep, hnextPresent, hnext.symm⟩

/-- Literal target-exterior reachability carries the compressed traversal
invariant from a live source atom to the reached vertex. -/
theorem exteriorLabelCapContractionTraversalState_reachable
    {N Larger Retained Incidence : Type*}
    [Fintype Retained] [DecidableEq Larger]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    (incidenceSlot : Incidence → Larger)
    (incidenceVertex : Incidence → N)
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (hconnectivity : code.connectivity =
      exactInterfaceExteriorCode graph largerVertex)
    (hinterfacePresent : ∀ slot, largerVertex slot ∈ graph.support →
      code.interfacePresent slot = true)
    (hincidencePresent : ∀ incidence,
      code.incidencePresent incidence = true ↔
        ExteriorIncidencePresent graph largerVertex incidenceSlot
          incidenceVertex incidence)
    (hincidenceConnected : ∀ first second,
      code.incidenceConnected first second = true ↔
        ExteriorIncidencePresent graph largerVertex incidenceSlot
            incidenceVertex first ∧
          ExteriorIncidencePresent graph largerVertex incidenceSlot
            incidenceVertex second ∧
          (exteriorGraph graph largerVertex).Reachable
            (incidenceVertex first) (incidenceVertex second))
    (hincidenceComplete : ∀ slot outside,
      OutsideInterface largerVertex outside →
        graph.Adj (largerVertex slot) outside →
        ∃ incidence,
          incidenceSlot incidence = slot ∧ incidenceVertex incidence = outside)
    (source : ExteriorLabelCapContractionAtom Larger Incidence)
    (hsource : exteriorLabelCapContractionAtomPresent code retain source =
      true)
    {target : N}
    (hreachable : (exteriorGraph graph retainedVertex).Reachable
      (exteriorLabelCapContractionAtomVertex largerVertex incidenceVertex
        source) target) :
    ExteriorLabelCapContractionTraversalState graph largerVertex code retain
      incidenceSlot incidenceVertex source target := by
  have hpath := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hreachable
  exact Relation.ReflTransGen.trans_induction_on
    (motive := fun {first second} _ =>
      ExteriorLabelCapContractionTraversalState graph largerVertex code retain
          incidenceSlot incidenceVertex source first →
        ExteriorLabelCapContractionTraversalState graph largerVertex code retain
          incidenceSlot incidenceVertex source second)
    hpath (fun _ hstate => hstate)
    (fun hstep hstate =>
      exteriorLabelCapContractionTraversalState_step graph largerVertex
        retainedVertex retain hsome incidenceSlot incidenceVertex code
          hconnectivity hinterfacePresent hincidencePresent hincidenceConnected
            hincidenceComplete source hstate hstep)
    (fun _ _ hfirst hsecond hstate => hsecond (hfirst hstate))
    (exteriorLabelCapContractionTraversalState_start graph largerVertex code
      retain incidenceSlot incidenceVertex source hsource)

/-- At a live target atom, the traversal invariant yields an atom path to that
exact target.  Equality aliases between larger coordinates are handled by one
exact interface step, so no injectivity hypothesis is hidden here. -/
theorem exteriorLabelCapContractionAtomPath_of_traversalState_target
    {N Larger Retained Incidence : Type*}
    [Fintype Retained] [DecidableEq Larger]
    (graph : SimpleGraph N) (largerVertex : Larger → N)
    (retain : Retained → Option Larger)
    (incidenceSlot : Incidence → Larger)
    (incidenceVertex : Incidence → N)
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (hconnectivity : code.connectivity =
      exactInterfaceExteriorCode graph largerVertex)
    (hincidencePresent : ∀ incidence,
      code.incidencePresent incidence = true ↔
        ExteriorIncidencePresent graph largerVertex incidenceSlot
          incidenceVertex incidence)
    (hincidenceConnected : ∀ first second,
      code.incidenceConnected first second = true ↔
        ExteriorIncidencePresent graph largerVertex incidenceSlot
            incidenceVertex first ∧
          ExteriorIncidencePresent graph largerVertex incidenceSlot
            incidenceVertex second ∧
          (exteriorGraph graph largerVertex).Reachable
            (incidenceVertex first) (incidenceVertex second))
    (source target : ExteriorLabelCapContractionAtom Larger Incidence)
    (htarget : exteriorLabelCapContractionAtomPresent code retain target =
      true)
    (hstate : ExteriorLabelCapContractionTraversalState graph largerVertex code
      retain incidenceSlot incidenceVertex source
        (exteriorLabelCapContractionAtomVertex largerVertex incidenceVertex
          target)) :
    ExteriorLabelCapContractionAtomPath code retain incidenceSlot source
      target := by
  classical
  cases target with
  | inl targetSlot =>
      rcases hstate with hold | hforgotten
      · rcases hold with
          ⟨anchor, _hpath, hanchorPresent, hanchorReach⟩
        have hanchorLiteral := (hincidencePresent anchor).1 hanchorPresent
        have houtside := outsideInterface_of_exteriorGraph_reachable graph
          largerVertex hanchorLiteral.1 hanchorReach
        exact (houtside targetSlot rfl).elim
      · rcases hforgotten with
          ⟨slot, hpath, hslotPresent, hvertex⟩
        have hprimitive : interfaceExteriorFactoredStepBool code.connectivity
            slot targetSlot = true := by
          rw [interfaceExteriorFactoredStepBool_eq_true_iff, hconnectivity,
            exactInterfaceExteriorCode_step_iff]
          exact Or.inl hvertex
        exact hpath.tail
          (exteriorLabelCapContractionAtomStep_inl_inl code retain
            incidenceSlot slot targetSlot hslotPresent htarget hprimitive)
  | inr targetIncidence =>
      rcases hstate with hold | hforgotten
      · rcases hold with
          ⟨anchor, hpath, hanchorPresent, hanchorReach⟩
        have hanchorLiteral := (hincidencePresent anchor).1 hanchorPresent
        have htargetLiteral :=
          (hincidencePresent targetIncidence).1 htarget
        have hconnected : code.incidenceConnected anchor targetIncidence =
            true :=
          (hincidenceConnected anchor targetIncidence).2
            ⟨hanchorLiteral, htargetLiteral, hanchorReach⟩
        exact hpath.tail
          (exteriorLabelCapContractionAtomStep_inr_inr code retain
            incidenceSlot anchor targetIncidence hanchorPresent htarget
              hconnected)
      · rcases hforgotten with
          ⟨slot, _hpath, _hslotPresent, hvertex⟩
        have htargetLiteral :=
          (hincidencePresent targetIncidence).1 htarget
        exact (htargetLiteral.1 slot hvertex.symm).elim

/-- Literal target-exterior reachability is complete for the finite atom
closure, provided every live larger-coordinate/exterior edge has an incidence
name. -/
theorem exteriorLabelCapContractionAtomReachable_complete_of_exact
    {N Larger Retained Incidence : Type*}
    [Fintype Larger] [DecidableEq Larger] [Fintype Retained]
    [Fintype Incidence] [LinearOrder Incidence]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    (incidenceSlot : Incidence → Larger)
    (incidenceVertex : Incidence → N)
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (hconnectivity : code.connectivity =
      exactInterfaceExteriorCode graph largerVertex)
    (hinterfacePresent : ∀ slot, largerVertex slot ∈ graph.support →
      code.interfacePresent slot = true)
    (hincidencePresent : ∀ incidence,
      code.incidencePresent incidence = true ↔
        ExteriorIncidencePresent graph largerVertex incidenceSlot
          incidenceVertex incidence)
    (hincidenceConnected : ∀ first second,
      code.incidenceConnected first second = true ↔
        ExteriorIncidencePresent graph largerVertex incidenceSlot
            incidenceVertex first ∧
          ExteriorIncidencePresent graph largerVertex incidenceSlot
            incidenceVertex second ∧
          (exteriorGraph graph largerVertex).Reachable
            (incidenceVertex first) (incidenceVertex second))
    (hincidenceComplete : ∀ slot outside,
      OutsideInterface largerVertex outside →
        graph.Adj (largerVertex slot) outside →
        ∃ incidence,
          incidenceSlot incidence = slot ∧ incidenceVertex incidence = outside)
    (source target : ExteriorLabelCapContractionAtom Larger Incidence)
    (hsource : exteriorLabelCapContractionAtomPresent code retain source =
      true)
    (htarget : exteriorLabelCapContractionAtomPresent code retain target =
      true)
    (hreachable : (exteriorGraph graph retainedVertex).Reachable
      (exteriorLabelCapContractionAtomVertex largerVertex incidenceVertex source)
      (exteriorLabelCapContractionAtomVertex largerVertex incidenceVertex
        target)) :
    exteriorLabelCapContractionAtomReachable code retain incidenceSlot source
      target = true := by
  rw [exteriorLabelCapContractionAtomReachable,
    boolRelationReachable_eq_true_iff]
  apply exteriorLabelCapContractionAtomPath_of_traversalState_target graph
    largerVertex retain incidenceSlot incidenceVertex code hconnectivity
      hincidencePresent hincidenceConnected source target htarget
  exact exteriorLabelCapContractionTraversalState_reachable graph largerVertex
    retainedVertex retain hsome incidenceSlot incidenceVertex code
      hconnectivity hinterfacePresent hincidencePresent hincidenceConnected
        hincidenceComplete source hsource hreachable

/-- On live atoms, executable contraction reachability is exactly literal
strict-exterior reachability after partial interface forgetting. -/
theorem exteriorLabelCapContractionAtomReachable_iff_of_exact
    {N Larger Retained Incidence : Type*}
    [Fintype N] [DecidableEq N]
    [Fintype Larger] [DecidableEq Larger] [Fintype Retained]
    [Fintype Incidence] [LinearOrder Incidence]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    (hnone : ∀ retained, retain retained = none →
      retainedVertex retained ∉ graph.support)
    (incidenceSlot : Incidence → Larger)
    (incidenceVertex : Incidence → N)
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (hconnectivity : code.connectivity =
      exactInterfaceExteriorCode graph largerVertex)
    (hinterfacePresent : ∀ slot, largerVertex slot ∈ graph.support →
      code.interfacePresent slot = true)
    (hincidencePresent : ∀ incidence,
      code.incidencePresent incidence = true ↔
        ExteriorIncidencePresent graph largerVertex incidenceSlot
          incidenceVertex incidence)
    (hincidenceConnected : ∀ first second,
      code.incidenceConnected first second = true ↔
        ExteriorIncidencePresent graph largerVertex incidenceSlot
            incidenceVertex first ∧
          ExteriorIncidencePresent graph largerVertex incidenceSlot
            incidenceVertex second ∧
          (exteriorGraph graph largerVertex).Reachable
            (incidenceVertex first) (incidenceVertex second))
    (hincidenceComplete : ∀ slot outside,
      OutsideInterface largerVertex outside →
        graph.Adj (largerVertex slot) outside →
        ∃ incidence,
          incidenceSlot incidence = slot ∧ incidenceVertex incidence = outside)
    (source target : ExteriorLabelCapContractionAtom Larger Incidence)
    (hsource : exteriorLabelCapContractionAtomPresent code retain source =
      true)
    (htarget : exteriorLabelCapContractionAtomPresent code retain target =
      true) :
    exteriorLabelCapContractionAtomReachable code retain incidenceSlot source
        target = true ↔
      (exteriorGraph graph retainedVertex).Reachable
        (exteriorLabelCapContractionAtomVertex largerVertex incidenceVertex
          source)
        (exteriorLabelCapContractionAtomVertex largerVertex incidenceVertex
          target) := by
  constructor
  · exact exteriorLabelCapContractionAtomReachable_sound_of_exact graph
      largerVertex retainedVertex retain hsome hnone incidenceSlot
        incidenceVertex code hconnectivity hincidencePresent
          hincidenceConnected source target
  · exact exteriorLabelCapContractionAtomReachable_complete_of_exact graph
      largerVertex retainedVertex retain hsome incidenceSlot incidenceVertex
        code hconnectivity hinterfacePresent hincidencePresent
          hincidenceConnected hincidenceComplete source target hsource htarget

end GoertzelV24InterfaceExteriorLabelCapFactorForgetExact

end Mettapedia.GraphTheory.FourColor
