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

end GoertzelV24InterfaceExteriorLabelCapFactorForgetExact

end Mettapedia.GraphTheory.FourColor
