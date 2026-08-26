import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorLabelCapFactorForgetExact
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorLabelCapFactorForgetWeight

/-!
# Exact label partition for exterior contraction

The finite contraction atoms have a literal label semantics.  A forgotten
coordinate contributes its singleton ambient label.  A canonical incidence
contributes the labels of the old strict-exterior component it enters.

This file proves that these supports cover exactly the labels of the literal
strict-exterior component after partial interface forgetting.  It does not
assume coordinate injectivity or label injectivity; those hypotheses enter
only later, when a concrete geometry proves that the covering supports are
pairwise disjoint and therefore that cardinalities add.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InterfaceExteriorLabelCapFactorForgetWeightExact

open GoertzelV24FiniteBoolRelationClosure
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24InterfaceExteriorLabelCapFactorForget
open GoertzelV24InterfaceExteriorLabelCapFactorForgetExact
open GoertzelV24InterfaceExteriorLabelCapFactorForgetWeight
open SimpleGraph

/-- Labels in the literal retained-exterior component denoted by an atom. -/
noncomputable def exteriorLabelCapContractionLiteralLabelSupport
    {N Larger Retained Incidence Label : Type*}
    [Fintype N] [DecidableEq N] [Fintype Label] [DecidableEq Label]
    (graph : SimpleGraph N) (retainedVertex : Retained → N)
    (largerVertex : Larger → N) (incidenceVertex : Incidence → N)
    (label : N → Label)
    (source : ExteriorLabelCapContractionAtom Larger Incidence) :
    Finset Label := by
  classical
  exact (Finset.univ.filter fun vertex =>
    (exteriorGraph graph retainedVertex).Reachable
      (exteriorLabelCapContractionAtomVertex largerVertex incidenceVertex source)
      vertex).image label

@[simp]
theorem mem_exteriorLabelCapContractionLiteralLabelSupport_iff
    {N Larger Retained Incidence Label : Type*}
    [Fintype N] [DecidableEq N] [Fintype Label] [DecidableEq Label]
    (graph : SimpleGraph N) (retainedVertex : Retained → N)
    (largerVertex : Larger → N) (incidenceVertex : Incidence → N)
    (label : N → Label)
    (source : ExteriorLabelCapContractionAtom Larger Incidence)
    (value : Label) :
    value ∈ exteriorLabelCapContractionLiteralLabelSupport graph retainedVertex
        largerVertex incidenceVertex label source ↔
      ∃ vertex : N,
        (exteriorGraph graph retainedVertex).Reachable
          (exteriorLabelCapContractionAtomVertex largerVertex incidenceVertex
            source) vertex ∧
        label vertex = value := by
  classical
  simp [exteriorLabelCapContractionLiteralLabelSupport]

/-- Every live exact incidence class has a canonical least representative,
connected to the supplied incidence. -/
theorem exists_contractionIncidenceRepresentative_connected_of_exact
    {N Larger Incidence : Type*}
    [Fintype Incidence] [LinearOrder Incidence]
    (graph : SimpleGraph N) (largerVertex : Larger → N)
    (incidenceSlot : Incidence → Larger)
    (incidenceVertex : Incidence → N)
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
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
    (incidence : Incidence)
    (hpresent : code.incidencePresent incidence = true) :
    ∃ representative,
      exteriorLabelCapContractionIncidenceRepresentative code representative =
          true ∧
        code.incidenceConnected incidence representative = true := by
  classical
  let component := Finset.univ.filter fun candidate =>
    code.incidenceConnected candidate incidence = true
  have hliteral := (hincidencePresent incidence).1 hpresent
  have hself : code.incidenceConnected incidence incidence = true :=
    (hincidenceConnected incidence incidence).2
      ⟨hliteral, hliteral, SimpleGraph.Reachable.rfl⟩
  have hnonempty : component.Nonempty := by
    refine ⟨incidence, ?_⟩
    simp [component, hself]
  rcases Finset.exists_min_image component id hnonempty with
    ⟨representative, hrepresentativeMem, hminimal⟩
  have hrepresentativeToIncidence :
      code.incidenceConnected representative incidence = true := by
    simpa [component] using hrepresentativeMem
  have hrepresentativeLiteral :=
    (hincidenceConnected representative incidence).1
      hrepresentativeToIncidence
  have hrepresentativePresent :
      code.incidencePresent representative = true :=
    (hincidencePresent representative).2 hrepresentativeLiteral.1
  have hincidenceToRepresentative :
      code.incidenceConnected incidence representative = true :=
    (hincidenceConnected incidence representative).2
      ⟨hliteral, hrepresentativeLiteral.1,
        hrepresentativeLiteral.2.2.symm⟩
  refine ⟨representative, ?_, hincidenceToRepresentative⟩
  unfold exteriorLabelCapContractionIncidenceRepresentative
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hrepresentativePresent, ?_⟩
  simp only [decide_eq_true_eq]
  intro candidate hcandidateToRepresentative
  have hcandidateLiteral :=
    (hincidenceConnected candidate representative).1
      hcandidateToRepresentative
  have hcandidateToIncidence :
      code.incidenceConnected candidate incidence = true :=
    (hincidenceConnected candidate incidence).2
      ⟨hcandidateLiteral.1, hliteral,
        hcandidateLiteral.2.2.trans hrepresentativeLiteral.2.2⟩
  exact hminimal candidate (by simp [component, hcandidateToIncidence])

/-- Two connected canonical incidence representatives are equal. -/
theorem contractionIncidenceRepresentative_eq_of_connected_exact
    {N Larger Incidence : Type*}
    [Fintype Incidence] [LinearOrder Incidence]
    (graph : SimpleGraph N) (largerVertex : Larger → N)
    (incidenceSlot : Incidence → Larger)
    (incidenceVertex : Incidence → N)
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (hincidenceConnected : ∀ first second,
      code.incidenceConnected first second = true ↔
        ExteriorIncidencePresent graph largerVertex incidenceSlot
            incidenceVertex first ∧
          ExteriorIncidencePresent graph largerVertex incidenceSlot
            incidenceVertex second ∧
          (exteriorGraph graph largerVertex).Reachable
            (incidenceVertex first) (incidenceVertex second))
    {first second : Incidence}
    (hfirst : exteriorLabelCapContractionIncidenceRepresentative code first =
      true)
    (hsecond : exteriorLabelCapContractionIncidenceRepresentative code second =
      true)
    (hconnected : code.incidenceConnected first second = true) :
    first = second := by
  have hfirstData := Bool.and_eq_true_iff.mp hfirst
  have hsecondData := Bool.and_eq_true_iff.mp hsecond
  have hfirstLeast : ∀ candidate,
      code.incidenceConnected candidate first = true → first ≤ candidate := by
    simpa [exteriorLabelCapContractionIncidenceRepresentative] using
      hfirstData.2
  have hsecondLeast : ∀ candidate,
      code.incidenceConnected candidate second = true → second ≤ candidate := by
    simpa [exteriorLabelCapContractionIncidenceRepresentative] using
      hsecondData.2
  have hliteral := (hincidenceConnected first second).1 hconnected
  have hreverse : code.incidenceConnected second first = true :=
    (hincidenceConnected second first).2
      ⟨hliteral.2.1, hliteral.1, hliteral.2.2.symm⟩
  exact le_antisymm (hfirstLeast second hreverse)
    (hsecondLeast first hconnected)

/-- For exact data, the union of the atom supports in one finite contraction
component is exactly its literal retained-exterior label support. -/
theorem exteriorLabelCapContractionLiteralLabelSupport_eq_atom_biUnion
    {N Larger Retained Incidence Label : Type*}
    [Fintype N] [DecidableEq N]
    [Fintype Larger] [DecidableEq Larger] [Fintype Retained]
    [Fintype Incidence] [LinearOrder Incidence]
    [Fintype Label] [DecidableEq Label]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    (hnone : ∀ retained, retain retained = none →
      retainedVertex retained ∉ graph.support)
    (incidenceSlot : Incidence → Larger)
    (incidenceVertex : Incidence → N)
    (label : N → Label)
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
      true) :
    exteriorLabelCapContractionLiteralLabelSupport graph retainedVertex
        largerVertex incidenceVertex label source =
      (exteriorLabelCapContractionComponentAtoms code retain incidenceSlot
        source).biUnion
        (exteriorLabelCapContractionAtomLabelSupport code
          (fun slot => label (largerVertex slot))
          (fun incidence => exteriorIncidenceLabelSupport graph largerVertex
            incidenceSlot incidenceVertex label incidence)) := by
  classical
  ext value
  rw [mem_exteriorLabelCapContractionLiteralLabelSupport_iff]
  constructor
  · rintro ⟨vertex, hreachable, rfl⟩
    have hstate := exteriorLabelCapContractionTraversalState_reachable graph
      largerVertex retainedVertex retain hsome incidenceSlot incidenceVertex
      code hconnectivity hinterfacePresent hincidencePresent
      hincidenceConnected hincidenceComplete source hsource hreachable
    rcases hstate with hold | hforgotten
    · rcases hold with
        ⟨anchor, hpath, hanchorPresent, hanchorReach⟩
      rcases exists_contractionIncidenceRepresentative_connected_of_exact graph
          largerVertex incidenceSlot incidenceVertex code hincidencePresent
          hincidenceConnected anchor hanchorPresent with
        ⟨representative, hrepresentative, hanchorConnected⟩
      have hrepresentativePresent : code.incidencePresent representative =
          true :=
        (Bool.and_eq_true_iff.mp hrepresentative).1
      have hstep : exteriorLabelCapContractionAtomStep code retain
          incidenceSlot (.inr anchor) (.inr representative) = true :=
        exteriorLabelCapContractionAtomStep_inr_inr code retain incidenceSlot
          anchor representative hanchorPresent hrepresentativePresent
            hanchorConnected
      have hpathRepresentative := hpath.tail hstep
      have hreachableRepresentative :
          exteriorLabelCapContractionAtomReachable code retain incidenceSlot
            source (.inr representative) = true := by
        rw [exteriorLabelCapContractionAtomReachable,
          boolRelationReachable_eq_true_iff]
        exact hpathRepresentative
      have hrepresentativeMem : Sum.inr representative ∈
          exteriorLabelCapContractionComponentAtoms code retain incidenceSlot
            source := by
        simp [exteriorLabelCapContractionComponentAtoms,
          exteriorLabelCapContractionAtomPresent, hrepresentativePresent,
          hreachableRepresentative]
      apply Finset.mem_biUnion.mpr
      refine ⟨.inr representative, hrepresentativeMem, ?_⟩
      simp [exteriorLabelCapContractionAtomLabelSupport, hrepresentative]
      rw [mem_exteriorIncidenceLabelSupport_iff]
      have hanchorLiteral := (hincidencePresent anchor).1 hanchorPresent
      have hconnectedLiteral :=
        (hincidenceConnected anchor representative).1 hanchorConnected
      exact ⟨hconnectedLiteral.2.1, vertex,
        hconnectedLiteral.2.2.symm.trans hanchorReach, rfl⟩
    · rcases hforgotten with ⟨slot, hpath, hpresent, hvertex⟩
      have hreachableSlot :
          exteriorLabelCapContractionAtomReachable code retain incidenceSlot
            source (.inl slot) = true := by
        rw [exteriorLabelCapContractionAtomReachable,
          boolRelationReachable_eq_true_iff]
        exact hpath
      have hslotMem : Sum.inl slot ∈
          exteriorLabelCapContractionComponentAtoms code retain incidenceSlot
            source := by
        simp [exteriorLabelCapContractionComponentAtoms, hpresent,
          hreachableSlot]
      apply Finset.mem_biUnion.mpr
      refine ⟨.inl slot, hslotMem, ?_⟩
      simp [exteriorLabelCapContractionAtomLabelSupport, hvertex]
  · rw [Finset.mem_biUnion]
    rintro ⟨atom, hatomMem, hvalue⟩
    have hatomData := (Finset.mem_filter.mp hatomMem).2
    have hpresent : exteriorLabelCapContractionAtomPresent code retain atom =
        true := (Bool.and_eq_true_iff.mp hatomData).1
    have hatomReachable : exteriorLabelCapContractionAtomReachable code retain
        incidenceSlot source atom = true :=
      (Bool.and_eq_true_iff.mp hatomData).2
    have hliteralReachable :=
      exteriorLabelCapContractionAtomReachable_sound_of_exact graph
        largerVertex retainedVertex retain hsome hnone incidenceSlot
          incidenceVertex code hconnectivity hincidencePresent
            hincidenceConnected source atom hatomReachable
    cases atom with
    | inl slot =>
        simp only [exteriorLabelCapContractionAtomLabelSupport,
          Finset.mem_singleton] at hvalue
        exact ⟨largerVertex slot, hliteralReachable, hvalue.symm⟩
    | inr incidence =>
        by_cases hrepresentative :
            exteriorLabelCapContractionIncidenceRepresentative code incidence
        · simp only [exteriorLabelCapContractionAtomLabelSupport,
            hrepresentative, if_true] at hvalue
          rw [mem_exteriorIncidenceLabelSupport_iff] at hvalue
          rcases hvalue with ⟨_hincidence, vertex, hreach, hlabel⟩
          exact ⟨vertex,
            hliteralReachable.trans
              (hreach.mono (exteriorGraph_larger_le_partialRetained graph
                largerVertex retainedVertex retain hsome hnone)),
            hlabel⟩
        · simp [exteriorLabelCapContractionAtomLabelSupport,
            hrepresentative] at hvalue

/-- If ambient labels are injective on the literal target component and the
larger coordinate presentation is injective, distinct component atoms denote
disjoint label supports. -/
theorem exteriorLabelCapContractionAtomLabelSupport_pairwiseDisjoint_of_injective
    {N Larger Retained Incidence Label : Type*}
    [Fintype N] [DecidableEq N]
    [Fintype Larger] [DecidableEq Larger] [Fintype Retained]
    [Fintype Incidence] [LinearOrder Incidence]
    [Fintype Label] [DecidableEq Label]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    (hnone : ∀ retained, retain retained = none →
      retainedVertex retained ∉ graph.support)
    (incidenceSlot : Incidence → Larger)
    (incidenceVertex : Incidence → N)
    (label : N → Label)
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
    (source : ExteriorLabelCapContractionAtom Larger Incidence)
    (hlargerInjective : Function.Injective largerVertex)
    (hlabelInjective : Set.InjOn label
      {vertex |
        (exteriorGraph graph retainedVertex).Reachable
          (exteriorLabelCapContractionAtomVertex largerVertex incidenceVertex
            source) vertex}) :
    (↑(exteriorLabelCapContractionComponentAtoms code retain incidenceSlot
        source) : Set (ExteriorLabelCapContractionAtom Larger Incidence)
      ).PairwiseDisjoint
      (exteriorLabelCapContractionAtomLabelSupport code
        (fun slot => label (largerVertex slot))
        (fun incidence => exteriorIncidenceLabelSupport graph largerVertex
          incidenceSlot incidenceVertex label incidence)) := by
  classical
  intro first hfirst second hsecond hne
  change Disjoint
    (exteriorLabelCapContractionAtomLabelSupport code
      (fun slot => label (largerVertex slot))
      (fun incidence => exteriorIncidenceLabelSupport graph largerVertex
        incidenceSlot incidenceVertex label incidence) first)
    (exteriorLabelCapContractionAtomLabelSupport code
      (fun slot => label (largerVertex slot))
      (fun incidence => exteriorIncidenceLabelSupport graph largerVertex
        incidenceSlot incidenceVertex label incidence) second)
  rw [Finset.disjoint_left]
  intro value hvalueFirst hvalueSecond
  have atomData : ∀ atom ∈
      exteriorLabelCapContractionComponentAtoms code retain incidenceSlot
        source,
      exteriorLabelCapContractionAtomPresent code retain atom = true ∧
        exteriorLabelCapContractionAtomReachable code retain incidenceSlot
          source atom = true := by
    intro atom hatom
    have hdata := (Finset.mem_filter.mp hatom).2
    exact Bool.and_eq_true_iff.mp hdata
  have hfirstData := atomData first hfirst
  have hsecondData := atomData second hsecond
  have hfirstReach :=
    exteriorLabelCapContractionAtomReachable_sound_of_exact graph largerVertex
      retainedVertex retain hsome hnone incidenceSlot incidenceVertex code
        hconnectivity hincidencePresent hincidenceConnected source first
          hfirstData.2
  have hsecondReach :=
    exteriorLabelCapContractionAtomReachable_sound_of_exact graph largerVertex
      retainedVertex retain hsome hnone incidenceSlot incidenceVertex code
        hconnectivity hincidencePresent hincidenceConnected source second
          hsecondData.2
  cases first with
  | inl firstSlot =>
      simp only [exteriorLabelCapContractionAtomLabelSupport,
        Finset.mem_singleton] at hvalueFirst
      cases second with
      | inl secondSlot =>
          simp only [exteriorLabelCapContractionAtomLabelSupport,
            Finset.mem_singleton] at hvalueSecond
          have hvertex : largerVertex firstSlot = largerVertex secondSlot :=
            hlabelInjective hfirstReach hsecondReach
              (hvalueFirst.symm.trans hvalueSecond)
          exact hne (by simp [hlargerInjective hvertex])
      | inr secondIncidence =>
          by_cases hrepresentative :
              exteriorLabelCapContractionIncidenceRepresentative code
                secondIncidence
          · simp only [exteriorLabelCapContractionAtomLabelSupport,
              hrepresentative, if_true] at hvalueSecond
            rw [mem_exteriorIncidenceLabelSupport_iff] at hvalueSecond
            rcases hvalueSecond with
              ⟨hsecondLiteral, vertex, hvertexReach, hvertexLabel⟩
            have htargetVertexReach :
                (exteriorGraph graph retainedVertex).Reachable
                  (exteriorLabelCapContractionAtomVertex largerVertex
                    incidenceVertex source) vertex :=
              hsecondReach.trans
                (hvertexReach.mono
                  (exteriorGraph_larger_le_partialRetained graph largerVertex
                    retainedVertex retain hsome hnone))
            have hvertexEq : largerVertex firstSlot = vertex :=
              hlabelInjective hfirstReach htargetVertexReach
                (hvalueFirst.symm.trans hvertexLabel.symm)
            have hvertexOutside : OutsideInterface largerVertex vertex :=
              outsideInterface_of_exteriorGraph_reachable graph largerVertex
                hsecondLiteral.1 hvertexReach
            exact hvertexOutside firstSlot hvertexEq.symm
          · simp [exteriorLabelCapContractionAtomLabelSupport,
              hrepresentative] at hvalueSecond
  | inr firstIncidence =>
      by_cases hfirstRepresentative :
          exteriorLabelCapContractionIncidenceRepresentative code
            firstIncidence
      · simp only [exteriorLabelCapContractionAtomLabelSupport,
          hfirstRepresentative, if_true] at hvalueFirst
        rw [mem_exteriorIncidenceLabelSupport_iff] at hvalueFirst
        rcases hvalueFirst with
          ⟨hfirstLiteral, firstVertex, hfirstVertexReach, hfirstVertexLabel⟩
        have hfirstTargetVertexReach :
            (exteriorGraph graph retainedVertex).Reachable
              (exteriorLabelCapContractionAtomVertex largerVertex
                incidenceVertex source) firstVertex :=
          hfirstReach.trans
            (hfirstVertexReach.mono
              (exteriorGraph_larger_le_partialRetained graph largerVertex
                retainedVertex retain hsome hnone))
        cases second with
        | inl secondSlot =>
            simp only [exteriorLabelCapContractionAtomLabelSupport,
              Finset.mem_singleton] at hvalueSecond
            have hvertexEq : firstVertex = largerVertex secondSlot :=
              hlabelInjective hfirstTargetVertexReach hsecondReach
                (hfirstVertexLabel.trans hvalueSecond)
            have hvertexOutside : OutsideInterface largerVertex firstVertex :=
              outsideInterface_of_exteriorGraph_reachable graph largerVertex
                hfirstLiteral.1 hfirstVertexReach
            exact hvertexOutside secondSlot hvertexEq
        | inr secondIncidence =>
            by_cases hsecondRepresentative :
                exteriorLabelCapContractionIncidenceRepresentative code
                  secondIncidence
            · simp only [exteriorLabelCapContractionAtomLabelSupport,
                hsecondRepresentative, if_true] at hvalueSecond
              rw [mem_exteriorIncidenceLabelSupport_iff] at hvalueSecond
              rcases hvalueSecond with
                ⟨hsecondLiteral, secondVertex, hsecondVertexReach,
                  hsecondVertexLabel⟩
              have hsecondTargetVertexReach :
                  (exteriorGraph graph retainedVertex).Reachable
                    (exteriorLabelCapContractionAtomVertex largerVertex
                      incidenceVertex source) secondVertex :=
                hsecondReach.trans
                  (hsecondVertexReach.mono
                    (exteriorGraph_larger_le_partialRetained graph largerVertex
                      retainedVertex retain hsome hnone))
              have hvertexEq : firstVertex = secondVertex :=
                hlabelInjective hfirstTargetVertexReach
                  hsecondTargetVertexReach
                  (hfirstVertexLabel.trans hsecondVertexLabel.symm)
              have hincidencesConnected :
                  code.incidenceConnected firstIncidence secondIncidence =
                    true :=
                (hincidenceConnected firstIncidence secondIncidence).2
                  ⟨hfirstLiteral, hsecondLiteral,
                    hfirstVertexReach.trans
                      (hvertexEq ▸ hsecondVertexReach.symm)⟩
              have hincidenceEq :=
                contractionIncidenceRepresentative_eq_of_connected_exact graph
                  largerVertex incidenceSlot incidenceVertex code
                    hincidenceConnected hfirstRepresentative
                      hsecondRepresentative hincidencesConnected
              exact hne (by simp [hincidenceEq])
            · simp [exteriorLabelCapContractionAtomLabelSupport,
                hsecondRepresentative] at hvalueSecond
      · simp [exteriorLabelCapContractionAtomLabelSupport,
          hfirstRepresentative] at hvalueFirst

/-- For exact connectivity, injective coordinates, and labels injective on the
literal retained component, the executable contracted cap is exactly the cap
of the literal component's distinct-label cardinality. -/
theorem exteriorLabelCapContractionComponentCap_val_eq_literalLabelSupport
    {N Larger Retained Incidence Label : Type*}
    [Fintype N] [DecidableEq N]
    [Fintype Larger] [DecidableEq Larger] [Fintype Retained]
    [Fintype Incidence] [LinearOrder Incidence]
    [Fintype Label] [DecidableEq Label]
    (graph : SimpleGraph N)
    (largerVertex : Larger → N) (retainedVertex : Retained → N)
    (retain : Retained → Option Larger)
    (hsome : ∀ retained slot, retain retained = some slot →
      largerVertex slot = retainedVertex retained)
    (hnone : ∀ retained, retain retained = none →
      retainedVertex retained ∉ graph.support)
    (incidenceSlot : Incidence → Larger)
    (incidenceVertex : Incidence → N)
    (label : N → Label)
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
    (hincidenceCap : ∀ incidence,
      (code.incidenceCap incidence).val =
        min (exteriorIncidenceLabelSupport graph largerVertex incidenceSlot
          incidenceVertex label incidence).card cap)
    (source : ExteriorLabelCapContractionAtom Larger Incidence)
    (hsource : exteriorLabelCapContractionAtomPresent code retain source =
      true)
    (hlargerInjective : Function.Injective largerVertex)
    (hlabelInjective : Set.InjOn label
      {vertex |
        (exteriorGraph graph retainedVertex).Reachable
          (exteriorLabelCapContractionAtomVertex largerVertex incidenceVertex
            source) vertex}) :
    (exteriorLabelCapContractionComponentCap code retain incidenceSlot source
      ).val =
      min (exteriorLabelCapContractionLiteralLabelSupport graph retainedVertex
        largerVertex incidenceVertex label source).card cap := by
  classical
  have hdisjoint :=
    exteriorLabelCapContractionAtomLabelSupport_pairwiseDisjoint_of_injective
      graph largerVertex retainedVertex retain hsome hnone incidenceSlot
        incidenceVertex label code hconnectivity hincidencePresent
          hincidenceConnected source hlargerInjective hlabelInjective
  calc
    (exteriorLabelCapContractionComponentCap code retain incidenceSlot source
      ).val =
        min ((exteriorLabelCapContractionComponentAtoms code retain
          incidenceSlot source).biUnion
          (exteriorLabelCapContractionAtomLabelSupport code
            (fun slot ↦ label (largerVertex slot))
            (fun incidence ↦ exteriorIncidenceLabelSupport graph largerVertex
              incidenceSlot incidenceVertex label incidence))).card cap :=
      exteriorLabelCapContractionComponentCap_val_eq_biUnion code retain
        incidenceSlot source (fun slot ↦ label (largerVertex slot))
          (fun incidence ↦ exteriorIncidenceLabelSupport graph largerVertex
            incidenceSlot incidenceVertex label incidence) hincidenceCap
              hdisjoint
    _ = min (exteriorLabelCapContractionLiteralLabelSupport graph
        retainedVertex largerVertex incidenceVertex label source).card cap := by
      rw [← exteriorLabelCapContractionLiteralLabelSupport_eq_atom_biUnion
        graph largerVertex retainedVertex retain hsome hnone incidenceSlot
          incidenceVertex label code hconnectivity hinterfacePresent
            hincidencePresent hincidenceConnected hincidenceComplete source
              hsource]

end GoertzelV24InterfaceExteriorLabelCapFactorForgetWeightExact

end Mettapedia.GraphTheory.FourColor
