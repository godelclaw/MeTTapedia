import Mettapedia.GraphTheory.FourColor.Compositional.CarrierBoundaryDeepAlternative
import Mettapedia.GraphTheory.FourColor.Compositional.CarrierConnectedCutAlternative
import Mettapedia.GraphTheory.FourColor.Compositional.CarrierSaturationProfileBound

/-!
# Complete-profile pumping along a saturated carrier

Keep every cyclic carrier coordinate whose two endpoint margins exceed the
uniform shallow-return boundary bound.  If neither a physical attachment nor
a deep return stack occurs, all of these coordinates are uniformly bounded
saturated prefixes.  Their coherently rooted connected cuts have distinct
complete phased `Count` states, so only finitely many such coordinates exist.

Consequently a carrier longer than that exact finite-state budget must expose
either a physical attachment or a strict family of connected return cuts.
This is the route's compositional pumping principle at one residual site.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace CarrierProfilePumpingAlternative

open CarrierBoundaryDeepAlternative
open CarrierConnectedCutAlternative
open CarrierSaturationBoundaryDecomposition
open CarrierSaturationProfileBound
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open PathPrefixConnectedCutProfileBound
open ResidualReturnSeparatorExitSide
open ResidualReturnStrictFamily
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Carrier coordinates with enough vertices on both sides to support the
cubic-tree cycle witnesses used by connected-cut saturation. -/
def centralCarrierPositions
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (bound : Nat) : Finset (CyclePosition sigma site) :=
  Finset.univ.filter fun cut =>
    0 < cut.val ∧ bound ≤ cut.val ∧
      bound ≤ Fintype.card (CyclePosition sigma site) - cut.val

/-- A carrier with more than `2 * bound + target` cyclic coordinates has more
than `target` coordinates after both endpoint margins are removed. -/
theorem target_lt_card_centralCarrierPositions
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (bound target : Nat) (hbound : 0 < bound)
    (hmany : 2 * bound + target <
      Fintype.card (CyclePosition sigma site)) :
    target < (centralCarrierPositions sigma site bound).card := by
  classical
  have hm : 2 * bound + target < site.cycle.tail.support.length := by
    simpa using hmany
  let embed : Fin (target + 1) →
      {cut // cut ∈ centralCarrierPositions sigma site bound} :=
    fun index =>
      ⟨⟨bound + index.val, by omega⟩, by
        simp only [centralCarrierPositions, Finset.mem_filter,
          Finset.mem_univ, true_and]
        constructor
        · omega
        constructor <;> omega⟩
  have hinjective : Function.Injective embed := by
    intro left right heq
    apply Fin.ext
    have hvalues := congrArg (fun cut => cut.1.val) heq
    change bound + left.val = bound + right.val at hvalues
    omega
  have hcard := Fintype.card_le_of_injective embed hinjective
  have hcard' : target + 1 ≤
      (centralCarrierPositions sigma site bound).card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using hcard
  omega

/-- Unless an attachment or a deep return stack has appeared, the complete
profile theorem bounds all central saturated carrier-prefix cuts at once. -/
theorem attachment_or_strictFamily_or_card_centralCarrierPositions_le
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length : Nat) :
    (∃ chord : OrderedReturnChord
        (orderedSiteReturnPairing hG sigma hSigma bond.site),
      Nonempty (AttachmentExitSideReceipt rotation hG sigma hSigma
        bond.site chord)) ∨
      HasStrictlyNestedConnectedReturnCutFamily G length ∨
      (centralCarrierPositions sigma bond.site
        (connectedCarrierCutBound length)).card ≤
          pathPrefixProfileStateCount (connectedCarrierCutBound length) := by
  classical
  by_cases hreceipt : ∃ chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma bond.site),
    Nonempty (AttachmentExitSideReceipt rotation hG sigma hSigma
      bond.site chord)
  · exact Or.inl hreceipt
  right
  by_cases hfamily : HasStrictlyNestedConnectedReturnCutFamily G length
  · exact Or.inl hfamily
  right
  apply card_carrierPrefixFamily_le_profileStateCount rotation minimal hG
    sigma hSigma bond.site (connectedCarrierCutBound length)
      (centralCarrierPositions sigma bond.site
        (connectedCarrierCutBound length))
  · intro cut hcut
    exact (Finset.mem_filter.mp hcut).2.1
  · intro cut _hcut
    rcases attachment_or_strictFamily_or_card_ambientExitDart_le rotation
        minimal hG sigma hSigma bond length cut with
      hreceipt' | hfamily' | hboundary
    · exact False.elim (hreceipt hreceipt')
    · exact False.elim (hfamily hfamily')
    · exact hboundary
  · intro cut hcut
    exact ⟨(Finset.mem_filter.mp hcut).2.2.1,
      (Finset.mem_filter.mp hcut).2.2.2⟩

/-- **Carrier complete-profile pumping.**  Once the carrier exceeds the two
endpoint margins plus the exact complete-state count, the bounded shallow
branch is impossible.  A physical attachment or a strict connected-cut family
must occur. -/
theorem attachment_or_strictFamily_of_profileLongCarrier
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length : Nat)
    (hcarrierLarge :
      2 * connectedCarrierCutBound length +
          pathPrefixProfileStateCount (connectedCarrierCutBound length) <
        bond.site.cycle.tail.support.length) :
    (∃ chord : OrderedReturnChord
        (orderedSiteReturnPairing hG sigma hSigma bond.site),
      Nonempty (AttachmentExitSideReceipt rotation hG sigma hSigma
        bond.site chord)) ∨
      HasStrictlyNestedConnectedReturnCutFamily G length := by
  have hboundPositive : 0 < connectedCarrierCutBound length := by
    simp only [connectedCarrierCutBound]
    omega
  have hcardLarge :
      2 * connectedCarrierCutBound length +
          pathPrefixProfileStateCount (connectedCarrierCutBound length) <
        Fintype.card (CyclePosition sigma bond.site) := by
    simpa using hcarrierLarge
  have hcentralLarge := target_lt_card_centralCarrierPositions sigma bond.site
    (connectedCarrierCutBound length)
    (pathPrefixProfileStateCount (connectedCarrierCutBound length))
    hboundPositive hcardLarge
  rcases attachment_or_strictFamily_or_card_centralCarrierPositions_le
      rotation minimal hG sigma hSigma bond length with
    hreceipt | hfamily | hcentralBound
  · exact Or.inl hreceipt
  · exact Or.inr hfamily
  · exact False.elim (Nat.not_lt_of_ge hcentralBound hcentralLarge)

end

end CarrierProfilePumpingAlternative

end Mettapedia.GraphTheory.FourColor.Compositional
