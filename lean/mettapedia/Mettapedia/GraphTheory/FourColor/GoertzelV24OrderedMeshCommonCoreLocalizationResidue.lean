import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairCommonCoreLocalization
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshCommonCoreDisagreementResidue

/-!
# Localizing the collateral loss in a nine-site repair cycle

The periodic nine-site repair residue contains a step which gains agreement
with one partner and loses agreement with another partner at the repaired
site.  Common-core localization turns that bookkeeping fact into a geometric
dichotomy.  Either the gained and lost partners themselves disagree, or a
witness for the new repaired--lost disagreement is one of the five ambient
edges deleted at the gained partner.

This theorem sharpens the finite coherence residue.  It does not claim that
either horn already gives a support-preserving replacement or excludes a
wall.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedMeshCommonCoreLocalizationResidue

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairCommonCoreLocalization
open GoertzelV24MeshIsoperimetry
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshCommonCoreDisagreementResidue
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a n : Nat}

variable
  (rotation : Data G)
  (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
  (ordered : OrderedInjectiveMesh
    (toMultigraph rotation.toRotationSystem) a (n + 1))

/-- The mesh residue's inequality predicate is exactly the negation of the
generic common-core agreement relation. -/
theorem commonCoreAgrees_iff_not_coloringsDisagree
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color) :
    CommonCoreAgrees source target sourceColoring targetColoring ↔
      ¬ CommonCoreColoringsDisagree source target
        sourceColoring targetColoring := by
  simp only [CommonCoreAgrees, CommonCoreColoringsDisagree, not_ne_iff]

/-- The sharpened trade residue.  Either the two partner sites disagree, or
the new repaired--lost disagreement is witnessed on an edge deleted by the
gained partner. -/
def HasPartnerDisagreementOrLocalizedCollateralLoss
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (target : NineSiteTaitAssignment rotation minimal ordered row slot) : Prop :=
  ∃ repaired gainedPartner lostPartner : Fin 9,
    repaired ≠ gainedPartner ∧
    (CommonCoreColoringsDisagree
        (rowSiteData rotation minimal ordered row slot gainedPartner)
        (rowSiteData rotation minimal ordered row slot lostPartner)
        (target gainedPartner).1 (target lostPartner).1 ∨
      CommonCoreDisagreementLocalizedAt
        (rowSiteData rotation minimal ordered row slot repaired)
        (rowSiteData rotation minimal ordered row slot gainedPartner)
        (rowSiteData rotation minimal ordered row slot lostPartner)
        (target repaired).1 (target lostPartner).1)

/-- Reversing the ordered pair preserves the fact of common-core
disagreement. -/
theorem coloringsDisagree_symm
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color)
    (hdisagrees : CommonCoreColoringsDisagree source target
      sourceColoring targetColoring) :
    CommonCoreColoringsDisagree target source
      targetColoring sourceColoring := by
  intro htargetSource
  have htargetSourceAgrees : CommonCoreAgrees target source
      targetColoring sourceColoring := htargetSource
  have hsourceTargetAgrees := commonCoreAgrees_symm
    target source targetColoring sourceColoring htargetSourceAgrees
  exact hdisagrees hsourceTargetAgrees

/-- One anchored agreement trade has either a partner--partner disagreement
or a collateral-loss witness localized at the gained partner. -/
theorem partnerDisagreementOrLocalizedCollateralLoss_of_anchoredTrade
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    {source target : NineSiteTaitAssignment rotation minimal ordered row slot}
    (htrade : HasAnchoredAgreementTrade rotation minimal ordered row slot
      source target) :
    HasPartnerDisagreementOrLocalizedCollateralLoss
      rotation minimal ordered row slot target := by
  rcases htrade with
    ⟨repaired, gainedPartner, lostFirst, lostSecond, hne,
      hlossTouches, _hsourceGainedDisagrees, htargetGainedAgrees,
      _hsourceLostAgrees, htargetLostDisagrees⟩
  rcases hlossTouches with hlostFirst | hlostSecond
  · subst lostFirst
    refine ⟨repaired, gainedPartner, lostSecond, hne, ?_⟩
    by_cases hpartnerDisagrees :
        CommonCoreColoringsDisagree
          (rowSiteData rotation minimal ordered row slot gainedPartner)
          (rowSiteData rotation minimal ordered row slot lostSecond)
          (target gainedPartner).1 (target lostSecond).1
    · exact Or.inl hpartnerDisagrees
    · right
      apply commonCoreDisagreementLocalizedAt_of_chain
        (rowSiteData rotation minimal ordered row slot repaired)
        (rowSiteData rotation minimal ordered row slot gainedPartner)
        (rowSiteData rotation minimal ordered row slot lostSecond)
        (target repaired).1 (target gainedPartner).1 (target lostSecond).1
      · exact (commonCoreAgrees_iff_not_coloringsDisagree
          (rowSiteData rotation minimal ordered row slot repaired)
          (rowSiteData rotation minimal ordered row slot gainedPartner)
          (target repaired).1 (target gainedPartner).1).2
          htargetGainedAgrees
      · exact (commonCoreAgrees_iff_not_coloringsDisagree
          (rowSiteData rotation minimal ordered row slot gainedPartner)
          (rowSiteData rotation minimal ordered row slot lostSecond)
          (target gainedPartner).1 (target lostSecond).1).2
          hpartnerDisagrees
      · intro hagrees
        exact ((commonCoreAgrees_iff_not_coloringsDisagree
          (rowSiteData rotation minimal ordered row slot repaired)
          (rowSiteData rotation minimal ordered row slot lostSecond)
          (target repaired).1 (target lostSecond).1).1 hagrees)
          htargetLostDisagrees
  · subst lostSecond
    have htargetRepairedLostDisagrees :
        CommonCoreColoringsDisagree
          (rowSiteData rotation minimal ordered row slot repaired)
          (rowSiteData rotation minimal ordered row slot lostFirst)
          (target repaired).1 (target lostFirst).1 :=
      coloringsDisagree_symm
        (rowSiteData rotation minimal ordered row slot lostFirst)
        (rowSiteData rotation minimal ordered row slot repaired)
        (target lostFirst).1 (target repaired).1 htargetLostDisagrees
    refine ⟨repaired, gainedPartner, lostFirst, hne, ?_⟩
    by_cases hpartnerDisagrees :
        CommonCoreColoringsDisagree
          (rowSiteData rotation minimal ordered row slot gainedPartner)
          (rowSiteData rotation minimal ordered row slot lostFirst)
          (target gainedPartner).1 (target lostFirst).1
    · exact Or.inl hpartnerDisagrees
    · right
      apply commonCoreDisagreementLocalizedAt_of_chain
        (rowSiteData rotation minimal ordered row slot repaired)
        (rowSiteData rotation minimal ordered row slot gainedPartner)
        (rowSiteData rotation minimal ordered row slot lostFirst)
        (target repaired).1 (target gainedPartner).1 (target lostFirst).1
      · exact (commonCoreAgrees_iff_not_coloringsDisagree
          (rowSiteData rotation minimal ordered row slot repaired)
          (rowSiteData rotation minimal ordered row slot gainedPartner)
          (target repaired).1 (target gainedPartner).1).2
          htargetGainedAgrees
      · exact (commonCoreAgrees_iff_not_coloringsDisagree
          (rowSiteData rotation minimal ordered row slot gainedPartner)
          (rowSiteData rotation minimal ordered row slot lostFirst)
          (target gainedPartner).1 (target lostFirst).1).2
          hpartnerDisagrees
      · intro hagrees
        exact ((commonCoreAgrees_iff_not_coloringsDisagree
          (rowSiteData rotation minimal ordered row slot repaired)
          (rowSiteData rotation minimal ordered row slot lostFirst)
          (target repaired).1 (target lostFirst).1).1 hagrees)
          htargetRepairedLostDisagrees

/-- **Localized periodic-repair residue.**  If no assignment exposes the
branching or boundary-reaching horns, a strict repair step ends in a state
where either two partner sites disagree or the collateral disagreement has
a witness edge inside the gained partner's five-edge deleted footprint. -/
theorem exists_partnerDisagreementOrLocalizedCollateralLoss_of_no_branchingOrBoundary
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (hno : ∀ assignment :
      NineSiteTaitAssignment rotation minimal ordered row slot,
      ¬ HasNineSiteBranchingOrBoundary rotation minimal ordered row slot
          assignment) :
    ∃ source target,
      NineSiteStrictRepairStep rotation minimal ordered row slot source target ∧
      HasPartnerDisagreementOrLocalizedCollateralLoss
        rotation minimal ordered row slot target := by
  obtain ⟨source, target, hstep, htrade⟩ :=
    exists_anchoredAgreementTrade_of_no_branchingOrBoundary
      rotation minimal ordered row slot hno
  exact ⟨source, target, hstep,
    partnerDisagreementOrLocalizedCollateralLoss_of_anchoredTrade
      rotation minimal ordered row slot htrade⟩

end

end GoertzelV24OrderedMeshCommonCoreLocalizationResidue

end Mettapedia.GraphTheory.FourColor
