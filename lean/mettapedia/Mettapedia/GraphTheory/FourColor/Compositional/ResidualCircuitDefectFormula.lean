import Mettapedia.GraphTheory.FourColor.Compositional.ResidualExchangeDefectLocalization

/-!
# Residual defect as a finite circuit-class count

The two involutions on the alternating carrier generate a finite quotient of
cyclic positions.  Physical reachability identifies this quotient exactly
with the residual connected components which meet the carrier.  Restricting
to odd components turns the global defect-localization identity into a wholly
finite circuit-class formula.

This is the promised semantic boundary: a later wall argument may compute or
compare the finite circuit states, while the theorem here guarantees that it
is comparing the actual physical residual defect.  No direction of change is
assumed.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualCircuitDefectFormula

open GoertzelV24AlternatingMatchingComponent
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualDefectDescent
open GoertzelV24ResidualOddness
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualTwoFactor
open MatchingParity
open ResidualCircuitOddness
open ResidualCircuitParity
open ResidualCircuitPhysicalReachability
open ResidualExchangeDefectLocalization
open SimpleGraph

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The equivalence generators for old residual circuits: traverse either a
common return path or one local `tau` edge. -/
def oldCircuitRelation
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    CyclePosition sigma site → CyclePosition sigma site → Prop :=
  AlternatingStep
    (orderedSiteReturnPairing hG sigma hSigma site)
    (orderedSiteTauPairing sigma site)

/-- The corresponding generators after exchange, using local `sigma` edges. -/
def newCircuitRelation
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    CyclePosition sigma site → CyclePosition sigma site → Prop :=
  AlternatingStep
    (orderedSiteReturnPairing hG sigma hSigma site)
    (orderedSiteSigmaPairing sigma site)

/-- Finite undirected old residual circuit classes. -/
abbrev OldCircuitClass
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :=
  Quot (oldCircuitRelation hG sigma hSigma site)

/-- Finite undirected new residual circuit classes. -/
abbrev NewCircuitClass
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :=
  Quot (newCircuitRelation hG sigma hSigma site)

/-- Map an abstract old circuit class to its physical residual component. -/
def oldCircuitToComponent
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    OldCircuitClass hG sigma hSigma site →
      (residualGraph G sigma).ConnectedComponent :=
  Quot.lift
    (fun root => (residualGraph G sigma).connectedComponentMk
      (cycleVertexOrder sigma site root).1)
    (by
      intro left right hstep
      apply SimpleGraph.ConnectedComponent.sound
      apply oldResidual_reachable_of_eqvGen hG sigma hSigma site
      exact Relation.EqvGen.rel left right hstep)

/-- Map an abstract new circuit class to its physical residual component after
exchange. -/
def newCircuitToComponent
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    NewCircuitClass hG sigma hSigma site →
      (residualGraph G
        (sigma.exchange site.tau site.carrier
          site.sigma_closed site.tau_closed)).ConnectedComponent :=
  Quot.lift
    (fun root => (residualGraph G
      (sigma.exchange site.tau site.carrier
        site.sigma_closed site.tau_closed)).connectedComponentMk
          (cycleVertexOrder sigma site root).1)
    (by
      intro left right hstep
      apply SimpleGraph.ConnectedComponent.sound
      apply newResidual_reachable_of_eqvGen hG sigma hSigma site
      exact Relation.EqvGen.rel left right hstep)

@[simp]
theorem oldCircuitToComponent_mk
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : CyclePosition sigma site) :
    oldCircuitToComponent hG sigma hSigma site
        (Quot.mk _ root) =
      (residualGraph G sigma).connectedComponentMk
        (cycleVertexOrder sigma site root).1 :=
  rfl

@[simp]
theorem newCircuitToComponent_mk
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : CyclePosition sigma site) :
    newCircuitToComponent hG sigma hSigma site
        (Quot.mk _ root) =
      (residualGraph G
        (sigma.exchange site.tau site.carrier
          site.sigma_closed site.tau_closed)).connectedComponentMk
        (cycleVertexOrder sigma site root).1 :=
  rfl

/-- Physical reachability makes the old circuit-to-component map injective. -/
theorem oldCircuitToComponent_injective
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    Function.Injective (oldCircuitToComponent hG sigma hSigma site) := by
  intro left right
  refine Quot.induction_on₂ left right ?_
  intro leftRoot rightRoot heq
  apply Quot.eqvGen_sound
  apply (oldResidual_reachable_iff_eqvGen
    hG sigma hSigma site leftRoot rightRoot).1
  exact SimpleGraph.ConnectedComponent.eq.mp heq

/-- Physical reachability makes the new circuit-to-component map injective. -/
theorem newCircuitToComponent_injective
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    Function.Injective (newCircuitToComponent hG sigma hSigma site) := by
  intro left right
  refine Quot.induction_on₂ left right ?_
  intro leftRoot rightRoot heq
  apply Quot.eqvGen_sound
  apply (newResidual_reachable_iff_eqvGen
    hG sigma hSigma site leftRoot rightRoot).1
  exact SimpleGraph.ConnectedComponent.eq.mp heq

/-- Every old circuit class denotes a component meeting the carrier. -/
theorem oldCircuitToComponent_meets_carrier
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (circuit : OldCircuitClass hG sigma hSigma site) :
    ¬ Disjoint
      (oldCircuitToComponent hG sigma hSigma site circuit).supp
      (site.carrier : Set V) := by
  refine Quot.induction_on circuit ?_
  intro root
  apply Set.not_disjoint_iff.2
  exact ⟨(cycleVertexOrder sigma site root).1,
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem,
    (cycleVertexOrder sigma site root).2⟩

/-- Every new circuit class likewise denotes a component meeting the carrier. -/
theorem newCircuitToComponent_meets_carrier
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (circuit : NewCircuitClass hG sigma hSigma site) :
    ¬ Disjoint
      (newCircuitToComponent hG sigma hSigma site circuit).supp
      (site.carrier : Set V) := by
  refine Quot.induction_on circuit ?_
  intro root
  apply Set.not_disjoint_iff.2
  exact ⟨(cycleVertexOrder sigma site root).1,
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem,
    (cycleVertexOrder sigma site root).2⟩

/-- Old circuit classes whose physical components are odd. -/
def oldOddCircuitClasses
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    Set (OldCircuitClass hG sigma hSigma site) :=
  {circuit | oldCircuitToComponent hG sigma hSigma site circuit ∈
    (residualGraph G sigma).oddComponents}

/-- New circuit classes whose physical components are odd. -/
def newOddCircuitClasses
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    Set (NewCircuitClass hG sigma hSigma site) :=
  {circuit | newCircuitToComponent hG sigma hSigma site circuit ∈
    (residualGraph G
      (sigma.exchange site.tau site.carrier
        site.sigma_closed site.tau_closed)).oddComponents}

/-- At a concrete old root, membership in the odd circuit-class set is
exactly the stored finite parity bit. -/
theorem quot_mk_mem_oldOddCircuitClasses_iff_parity
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : CyclePosition sigma site) :
    Quot.mk (oldCircuitRelation hG sigma hSigma site) root ∈
        oldOddCircuitClasses hG sigma hSigma site ↔
      oldCircuitParity hG sigma hSigma site root = 1 := by
  exact (oldCircuitParity_eq_one_iff_mem_oddComponents
    hG sigma hSigma site root).symm

/-- The same characterization after exchange. -/
theorem quot_mk_mem_newOddCircuitClasses_iff_parity
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : CyclePosition sigma site) :
    Quot.mk (newCircuitRelation hG sigma hSigma site) root ∈
        newOddCircuitClasses hG sigma hSigma site ↔
      newCircuitParity hG sigma hSigma site root = 1 := by
  exact (newCircuitParity_eq_one_iff_mem_oddComponents
    hG sigma hSigma site root).symm

/-- Every odd old component meeting the carrier is represented by a circuit
class. -/
theorem oldCircuitToComponent_surjective_on_carrierOdd
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (target : (residualGraph G sigma).ConnectedComponent)
    (htarget : target ∈ oldCarrierOddComponents sigma site) :
    ∃ circuit, ∃ hcircuit :
        circuit ∈ oldOddCircuitClasses hG sigma hSigma site,
      oldCircuitToComponent hG sigma hSigma site circuit = target := by
  obtain ⟨vertex, hvertexSupp, hvertexCarrier⟩ :=
    Set.not_disjoint_iff.1 htarget.2
  let root : CyclePosition sigma site :=
    (cycleVertexOrder sigma site).symm ⟨vertex, hvertexCarrier⟩
  let circuit : OldCircuitClass hG sigma hSigma site :=
    Quot.mk _ root
  have hroot : (cycleVertexOrder sigma site root).1 = vertex := by
    exact congrArg Subtype.val
      ((cycleVertexOrder sigma site).apply_symm_apply
        ⟨vertex, hvertexCarrier⟩)
  have hcomponent :
      oldCircuitToComponent hG sigma hSigma site circuit = target := by
    change (residualGraph G sigma).connectedComponentMk
      (cycleVertexOrder sigma site root).1 = target
    rw [hroot]
    exact hvertexSupp
  refine ⟨circuit, ?_, hcomponent⟩
  change oldCircuitToComponent hG sigma hSigma site circuit ∈
    (residualGraph G sigma).oddComponents
  rw [hcomponent]
  exact htarget.1

/-- Every odd new component meeting the carrier is represented by a new
circuit class. -/
theorem newCircuitToComponent_surjective_on_carrierOdd
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (target : (residualGraph G
      (sigma.exchange site.tau site.carrier
        site.sigma_closed site.tau_closed)).ConnectedComponent)
    (htarget : target ∈ newCarrierOddComponents sigma site) :
    ∃ circuit, ∃ hcircuit :
        circuit ∈ newOddCircuitClasses hG sigma hSigma site,
      newCircuitToComponent hG sigma hSigma site circuit = target := by
  obtain ⟨vertex, hvertexSupp, hvertexCarrier⟩ :=
    Set.not_disjoint_iff.1 htarget.2
  let root : CyclePosition sigma site :=
    (cycleVertexOrder sigma site).symm ⟨vertex, hvertexCarrier⟩
  let circuit : NewCircuitClass hG sigma hSigma site :=
    Quot.mk _ root
  have hroot : (cycleVertexOrder sigma site root).1 = vertex := by
    exact congrArg Subtype.val
      ((cycleVertexOrder sigma site).apply_symm_apply
        ⟨vertex, hvertexCarrier⟩)
  have hcomponent :
      newCircuitToComponent hG sigma hSigma site circuit = target := by
    change (residualGraph G
      (sigma.exchange site.tau site.carrier
        site.sigma_closed site.tau_closed)).connectedComponentMk
          (cycleVertexOrder sigma site root).1 = target
    rw [hroot]
    exact hvertexSupp
  refine ⟨circuit, ?_, hcomponent⟩
  change newCircuitToComponent hG sigma hSigma site circuit ∈
    (residualGraph G
      (sigma.exchange site.tau site.carrier
        site.sigma_closed site.tau_closed)).oddComponents
  rw [hcomponent]
  exact htarget.1

/-- Counting abstract odd old circuit classes is exactly counting physical odd
components which meet the carrier. -/
theorem oldOddCircuitClasses_ncard_eq_oldCarrierOddComponents
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    (oldOddCircuitClasses hG sigma hSigma site).ncard =
      (oldCarrierOddComponents sigma site).ncard := by
  apply Set.ncard_congr (fun circuit _ =>
    oldCircuitToComponent hG sigma hSigma site circuit)
  · intro circuit hcircuit
    exact ⟨hcircuit,
      oldCircuitToComponent_meets_carrier hG sigma hSigma site circuit⟩
  · intro left right _ _
    intro heq
    exact oldCircuitToComponent_injective hG sigma hSigma site heq
  · exact oldCircuitToComponent_surjective_on_carrierOdd
      hG sigma hSigma site

/-- The corresponding exact count after exchange. -/
theorem newOddCircuitClasses_ncard_eq_newCarrierOddComponents
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    (newOddCircuitClasses hG sigma hSigma site).ncard =
      (newCarrierOddComponents sigma site).ncard := by
  apply Set.ncard_congr (fun circuit _ =>
    newCircuitToComponent hG sigma hSigma site circuit)
  · intro circuit hcircuit
    exact ⟨hcircuit,
      newCircuitToComponent_meets_carrier hG sigma hSigma site circuit⟩
  · intro left right _ _
    intro heq
    exact newCircuitToComponent_injective hG sigma hSigma site heq
  · exact newCircuitToComponent_surjective_on_carrierOdd
      hG sigma hSigma site

/-- The exact global residual-defect equation, now expressed entirely by the
finite old and new circuit-class sets on the exchange carrier. -/
theorem residualDefect_add_newOddCircuitClasses_eq_new_add_old
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    residualDefect G sigma +
        (newOddCircuitClasses hG sigma hSigma site).ncard =
      residualDefect G
          (sigma.exchange site.tau site.carrier
            site.sigma_closed site.tau_closed) +
        (oldOddCircuitClasses hG sigma hSigma site).ncard := by
  rw [newOddCircuitClasses_ncard_eq_newCarrierOddComponents,
    oldOddCircuitClasses_ncard_eq_oldCarrierOddComponents]
  exact residualDefect_add_newCarrier_eq_new_add_oldCarrier
    hG sigma hSigma site

/-- If the old pairing is residual-defect minimal against this exchange, then
the finite odd-circuit count on the carrier cannot decrease.  The direction is
an exact consequence of the global defect comparison and the balance formula;
it is not a parity-only local monotonicity principle. -/
theorem oldOddCircuitClasses_ncard_le_new_of_residualDefect_le
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (hminimal :
      residualDefect G sigma ≤
        residualDefect G
          (sigma.exchange site.tau site.carrier
            site.sigma_closed site.tau_closed)) :
    (oldOddCircuitClasses hG sigma hSigma site).ncard ≤
      (newOddCircuitClasses hG sigma hSigma site).ncard := by
  have hbalance :=
    residualDefect_add_newOddCircuitClasses_eq_new_add_old
      hG sigma hSigma site
  omega

/-- For the exchange-rigid site witness used by the mesh route, the finite
odd-circuit count is therefore monotone without any additional hypothesis. -/
theorem oldOddCircuitClasses_ncard_le_new
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    (oldOddCircuitClasses hG sigma hSigma site).ncard ≤
      (newOddCircuitClasses hG sigma hSigma site).ncard :=
  oldOddCircuitClasses_ncard_le_new_of_residualDefect_le
    hG sigma hSigma site site.exchange_rigid

/-- The exchange preserves global residual defect exactly when it preserves
the number of odd finite circuit classes on the carrier. -/
theorem residualDefect_eq_exchange_iff_oldOddCircuitClasses_ncard_eq_new
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    residualDefect G sigma =
        residualDefect G
          (sigma.exchange site.tau site.carrier
            site.sigma_closed site.tau_closed) ↔
      (oldOddCircuitClasses hG sigma hSigma site).ncard =
        (newOddCircuitClasses hG sigma hSigma site).ncard := by
  have hbalance :=
    residualDefect_add_newOddCircuitClasses_eq_new_add_old
      hG sigma hSigma site
  omega

/-- Strict growth of global residual defect is equivalent to strict growth of
the finite odd-circuit count on the exchange carrier. -/
theorem residualDefect_lt_exchange_iff_oldOddCircuitClasses_ncard_lt_new
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    residualDefect G sigma <
        residualDefect G
          (sigma.exchange site.tau site.carrier
            site.sigma_closed site.tau_closed) ↔
      (oldOddCircuitClasses hG sigma hSigma site).ncard <
        (newOddCircuitClasses hG sigma hSigma site).ncard := by
  have hbalance :=
    residualDefect_add_newOddCircuitClasses_eq_new_add_old
      hG sigma hSigma site
  omega

end

end ResidualCircuitDefectFormula

end Mettapedia.GraphTheory.FourColor.Compositional
