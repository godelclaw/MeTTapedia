import Mettapedia.GraphTheory.FourColor.Compositional.ResidualCircuitOddness
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualExchangeComponentLocalization

/-!
# Residual defect localizes to the exchange carrier

An alternating matching exchange changes residual adjacency only at its
carrier.  This file upgrades the rootwise cancellation theorem to the level of
connected-component sets.  Odd components avoiding the carrier correspond
bijectively before and after exchange, with literally equal vertex supports.

Consequently, any change in residual defect is accounted for entirely by odd
components which meet the finite carrier.  This is exact bookkeeping, not a
monotonicity statement.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualExchangeDefectLocalization

open GoertzelV24AlternatingMatchingComponent
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualDefectDescent
open GoertzelV24ResidualOddness
open GoertzelV24ResidualTwoFactor
open MatchingParity
open ResidualExchangeComponentLocalization
open SimpleGraph

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Odd old residual components disjoint from the operated carrier. -/
def oldOffCarrierOddComponents
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    Set (residualGraph G sigma).ConnectedComponent :=
  {component | component ∈ (residualGraph G sigma).oddComponents ∧
    Disjoint component.supp (site.carrier : Set V)}

/-- Odd new residual components disjoint from the operated carrier. -/
def newOffCarrierOddComponents
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    Set (residualGraph G
      (sigma.exchange site.tau site.carrier
        site.sigma_closed site.tau_closed)).ConnectedComponent :=
  {component | component ∈
      (residualGraph G
        (sigma.exchange site.tau site.carrier
          site.sigma_closed site.tau_closed)).oddComponents ∧
    Disjoint component.supp (site.carrier : Set V)}

/-- Rootwise avoidance says exactly that the root's whole old residual
component is disjoint from the carrier. -/
theorem oldComponentAvoidsCarrier_iff_disjoint_supp
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : V) :
    OldComponentAvoidsCarrier sigma site root ↔
      Disjoint ((residualGraph G sigma).connectedComponentMk root).supp
        (site.carrier : Set V) := by
  rw [Set.disjoint_left]
  constructor
  · intro havoid vertex hmem hcarrier
    apply havoid vertex hcarrier
    exact (SimpleGraph.ConnectedComponent.eq.mp hmem).symm
  · intro hdisjoint vertex hcarrier hreachable
    exact hdisjoint
      (SimpleGraph.ConnectedComponent.eq.mpr hreachable.symm) hcarrier

/-- Rootwise avoidance has the analogous support characterization after the
exchange. -/
theorem newComponentAvoidsCarrier_iff_disjoint_supp
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : V) :
    NewComponentAvoidsCarrier sigma site root ↔
      Disjoint ((residualGraph G
        (sigma.exchange site.tau site.carrier
          site.sigma_closed site.tau_closed)).connectedComponentMk root).supp
        (site.carrier : Set V) := by
  rw [Set.disjoint_left]
  constructor
  · intro havoid vertex hmem hcarrier
    apply havoid vertex hcarrier
    exact (SimpleGraph.ConnectedComponent.eq.mp hmem).symm
  · intro hdisjoint vertex hcarrier hreachable
    exact hdisjoint
      (SimpleGraph.ConnectedComponent.eq.mpr hreachable.symm) hcarrier

/-- Choose one vertex of an old residual component and take its new residual
component.  On carrier-avoiding components this choice preserves the whole
support and hence is canonical. -/
noncomputable def oldComponentToNew
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (component : (residualGraph G sigma).ConnectedComponent) :
    (residualGraph G
      (sigma.exchange site.tau site.carrier
        site.sigma_closed site.tau_closed)).ConnectedComponent :=
  (residualGraph G
    (sigma.exchange site.tau site.carrier
      site.sigma_closed site.tau_closed)).connectedComponentMk
        component.exists_rep.choose

/-- The chosen image of an avoiding old component has exactly the same vertex
support. -/
theorem oldComponentToNew_supp_eq
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (component : (residualGraph G sigma).ConnectedComponent)
    (havoid : Disjoint component.supp (site.carrier : Set V)) :
    (oldComponentToNew sigma site component).supp = component.supp := by
  let root : V := component.exists_rep.choose
  have hroot : (residualGraph G sigma).connectedComponentMk root = component :=
    component.exists_rep.choose_spec
  have hrootAvoids : OldComponentAvoidsCarrier sigma site root :=
    (oldComponentAvoidsCarrier_iff_disjoint_supp sigma site root).2 (by
      simpa only [hroot] using havoid)
  calc
    (oldComponentToNew sigma site component).supp =
        ((residualGraph G
          (sigma.exchange site.tau site.carrier
            site.sigma_closed site.tau_closed)).connectedComponentMk root).supp := by
          rfl
    _ = ((residualGraph G sigma).connectedComponentMk root).supp :=
      (oldResidual_connectedComponent_supp_eq_newResidual_of_avoids_carrier
        sigma hSigma site root hrootAvoids).symm
    _ = component.supp := by rw [hroot]

/-- The support-preserving map sends every odd avoiding old component to an
odd avoiding new component. -/
theorem oldComponentToNew_mem_newOffCarrierOddComponents
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (component : (residualGraph G sigma).ConnectedComponent)
    (hcomponent : component ∈ oldOffCarrierOddComponents sigma site) :
    oldComponentToNew sigma site component ∈
      newOffCarrierOddComponents sigma site := by
  rcases hcomponent with ⟨hodd, havoid⟩
  have hsupp := oldComponentToNew_supp_eq
    sigma hSigma site component havoid
  change Odd component.supp.ncard at hodd
  exact ⟨by
      change Odd (oldComponentToNew sigma site component).supp.ncard
      rw [hsupp]
      exact hodd,
    by simpa only [hsupp] using havoid⟩

/-- The support-preserving map is injective on avoiding old components. -/
theorem oldComponentToNew_injective_on_offCarrier
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {left right : (residualGraph G sigma).ConnectedComponent}
    (hleft : left ∈ oldOffCarrierOddComponents sigma site)
    (hright : right ∈ oldOffCarrierOddComponents sigma site)
    (heq : oldComponentToNew sigma site left =
      oldComponentToNew sigma site right) :
    left = right := by
  apply SimpleGraph.ConnectedComponent.supp_injective
  rw [← oldComponentToNew_supp_eq sigma hSigma site left hleft.2,
    ← oldComponentToNew_supp_eq sigma hSigma site right hright.2,
    heq]

/-- Every odd avoiding new component is the image of an odd avoiding old
component. -/
theorem oldComponentToNew_surjective_on_offCarrier
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (target : (residualGraph G
      (sigma.exchange site.tau site.carrier
        site.sigma_closed site.tau_closed)).ConnectedComponent)
    (htarget : target ∈ newOffCarrierOddComponents sigma site) :
    ∃ source, ∃ hsource : source ∈ oldOffCarrierOddComponents sigma site,
      oldComponentToNew sigma site source = target := by
  let root : V := target.exists_rep.choose
  have hroot : (residualGraph G
      (sigma.exchange site.tau site.carrier
        site.sigma_closed site.tau_closed)).connectedComponentMk root = target :=
    target.exists_rep.choose_spec
  have hnewAvoids : NewComponentAvoidsCarrier sigma site root :=
    (newComponentAvoidsCarrier_iff_disjoint_supp sigma site root).2 (by
      simpa only [hroot] using htarget.2)
  have holdAvoids : OldComponentAvoidsCarrier sigma site root :=
    (oldComponentAvoidsCarrier_iff_newComponentAvoidsCarrier
      sigma hSigma site root).2 hnewAvoids
  let source := (residualGraph G sigma).connectedComponentMk root
  have hsupp : source.supp = target.supp := by
    calc
      source.supp = ((residualGraph G
          (sigma.exchange site.tau site.carrier
            site.sigma_closed site.tau_closed)).connectedComponentMk root).supp :=
        oldResidual_connectedComponent_supp_eq_newResidual_of_avoids_carrier
          sigma hSigma site root holdAvoids
      _ = target.supp := by rw [hroot]
  have hsource : source ∈ oldOffCarrierOddComponents sigma site := by
    have hodd : Odd target.supp.ncard := htarget.1
    exact ⟨by
        change Odd source.supp.ncard
        rw [hsupp]
        exact hodd,
      by simpa only [hsupp] using htarget.2⟩
  refine ⟨source, hsource, ?_⟩
  apply SimpleGraph.ConnectedComponent.supp_injective
  rw [oldComponentToNew_supp_eq sigma hSigma site source hsource.2,
    hsupp]

/-- The number of odd residual components away from the carrier is unchanged
by exchange. -/
theorem oldOffCarrierOddComponents_ncard_eq_new
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    (oldOffCarrierOddComponents sigma site).ncard =
      (newOffCarrierOddComponents sigma site).ncard := by
  apply Set.ncard_congr (fun component _ =>
    oldComponentToNew sigma site component)
  · exact oldComponentToNew_mem_newOffCarrierOddComponents sigma hSigma site
  · intro left right hleft hright
    exact oldComponentToNew_injective_on_offCarrier
      sigma hSigma site hleft hright
  · exact oldComponentToNew_surjective_on_offCarrier sigma hSigma site

/-- Odd old residual components which meet the operated carrier. -/
def oldCarrierOddComponents
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    Set (residualGraph G sigma).ConnectedComponent :=
  {component | component ∈ (residualGraph G sigma).oddComponents ∧
    ¬ Disjoint component.supp (site.carrier : Set V)}

/-- Odd new residual components which meet the operated carrier. -/
def newCarrierOddComponents
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    Set (residualGraph G
      (sigma.exchange site.tau site.carrier
        site.sigma_closed site.tau_closed)).ConnectedComponent :=
  {component | component ∈
      (residualGraph G
        (sigma.exchange site.tau site.carrier
          site.sigma_closed site.tau_closed)).oddComponents ∧
    ¬ Disjoint component.supp (site.carrier : Set V)}

/-- Old odd components split into the disjoint off-carrier and carrier-touching
parts. -/
theorem old_oddComponents_eq_offCarrier_union_carrier
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    (residualGraph G sigma).oddComponents =
      oldOffCarrierOddComponents sigma site ∪
        oldCarrierOddComponents sigma site := by
  ext component
  simp only [oldOffCarrierOddComponents, oldCarrierOddComponents,
    Set.mem_setOf_eq, Set.mem_union]
  tauto

/-- New odd components have the analogous disjoint partition. -/
theorem new_oddComponents_eq_offCarrier_union_carrier
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    (residualGraph G
      (sigma.exchange site.tau site.carrier
        site.sigma_closed site.tau_closed)).oddComponents =
      newOffCarrierOddComponents sigma site ∪
        newCarrierOddComponents sigma site := by
  ext component
  simp only [newOffCarrierOddComponents, newCarrierOddComponents,
    Set.mem_setOf_eq, Set.mem_union]
  tauto

/-- The old off-carrier and carrier-touching parts are disjoint. -/
theorem oldOffCarrierOddComponents_disjoint_carrier
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    Disjoint (oldOffCarrierOddComponents sigma site)
      (oldCarrierOddComponents sigma site) := by
  rw [Set.disjoint_left]
  intro component hoff hcarrier
  exact hcarrier.2 hoff.2

/-- The new off-carrier and carrier-touching parts are disjoint. -/
theorem newOffCarrierOddComponents_disjoint_carrier
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    Disjoint (newOffCarrierOddComponents sigma site)
      (newCarrierOddComponents sigma site) := by
  rw [Set.disjoint_left]
  intro component hoff hcarrier
  exact hcarrier.2 hoff.2

/-- Cardinality form of the old odd-component partition. -/
theorem old_oddComponents_ncard_eq_offCarrier_add_carrier
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    (residualGraph G sigma).oddComponents.ncard =
      (oldOffCarrierOddComponents sigma site).ncard +
        (oldCarrierOddComponents sigma site).ncard := by
  calc
    (residualGraph G sigma).oddComponents.ncard =
        (oldOffCarrierOddComponents sigma site ∪
          oldCarrierOddComponents sigma site).ncard := by
      rw [old_oddComponents_eq_offCarrier_union_carrier]
    _ = _ := Set.ncard_union_eq
      (oldOffCarrierOddComponents_disjoint_carrier sigma site)

/-- Cardinality form of the new odd-component partition. -/
theorem new_oddComponents_ncard_eq_offCarrier_add_carrier
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    (residualGraph G
      (sigma.exchange site.tau site.carrier
        site.sigma_closed site.tau_closed)).oddComponents.ncard =
      (newOffCarrierOddComponents sigma site).ncard +
        (newCarrierOddComponents sigma site).ncard := by
  calc
    (residualGraph G
      (sigma.exchange site.tau site.carrier
        site.sigma_closed site.tau_closed)).oddComponents.ncard =
        (newOffCarrierOddComponents sigma site ∪
          newCarrierOddComponents sigma site).ncard := by
      rw [new_oddComponents_eq_offCarrier_union_carrier]
    _ = _ := Set.ncard_union_eq
      (newOffCarrierOddComponents_disjoint_carrier sigma site)

/-- Subtraction-free localization of odd-component counts.  After the
unchanged off-carrier components cancel, only the two finite carrier-touching
terms remain. -/
theorem oddComponents_ncard_add_newCarrier_eq_new_add_oldCarrier
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    (residualGraph G sigma).oddComponents.ncard +
        (newCarrierOddComponents sigma site).ncard =
      (residualGraph G
        (sigma.exchange site.tau site.carrier
          site.sigma_closed site.tau_closed)).oddComponents.ncard +
        (oldCarrierOddComponents sigma site).ncard := by
  rw [old_oddComponents_ncard_eq_offCarrier_add_carrier,
    new_oddComponents_ncard_eq_offCarrier_add_carrier,
    oldOffCarrierOddComponents_ncard_eq_new sigma hSigma site]
  omega

/-- Exact localization of global residual defect to the carrier-touching odd
components.  This equation deliberately makes no claim about which carrier
term is larger. -/
theorem residualDefect_add_newCarrier_eq_new_add_oldCarrier
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    residualDefect G sigma +
        (newCarrierOddComponents sigma site).ncard =
      residualDefect G
          (sigma.exchange site.tau site.carrier
            site.sigma_closed site.tau_closed) +
        (oldCarrierOddComponents sigma site).ncard := by
  have hExchanged :
      (sigma.exchange site.tau site.carrier
        site.sigma_closed site.tau_closed).SupportedBy G :=
    Pairing.exchange_supportedBy sigma site.tau site.carrier
      site.sigma_closed site.tau_closed hSigma site.tau_supported
  rw [residualDefect_eq_oddComponents_ncard hG sigma hSigma,
    residualDefect_eq_oddComponents_ncard hG _ hExchanged]
  exact oddComponents_ncard_add_newCarrier_eq_new_add_oldCarrier
    sigma hSigma site

end

end ResidualExchangeDefectLocalization

end Mettapedia.GraphTheory.FourColor.Compositional
