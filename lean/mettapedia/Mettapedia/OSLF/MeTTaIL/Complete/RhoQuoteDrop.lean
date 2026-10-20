import Mettapedia.OSLF.MeTTaIL.Complete.QuoteDropCoherence
import Mettapedia.OSLF.MeTTaIL.Complete.RhoPresented

/-!
# Rho modulo its parallel laws and the name equation

Rho's language declares the name equation `@(*n) = n` (`QuoteDrop`) besides the parallel laws of
`PPar`. The plan with its standard reduction contexts leaves the equation out of its search: from
right to left it expands without bound. The explorer that commits the quote-drop normal form and
then the sorted normal form of the parallel laws explores every process reachable by steps modulo
both, up to both (`rho_explores_quoteDrop`).

COMM meets every condition: it has no premises, its left side mentions no quote, its one explicit
substitution puts the quotation `@q` into a body that depends on the received name, and it uses
the reflective substitution of rho's presentation. A quoted name is never a reduction context.

Positive example: the channels `@0` and `@(*@0)` are one name (`quoteDrop_identifies`). Negative
example: the channels `@0` and `@{}` stay distinct, since the parallel laws do not identify an
empty parallel composition with `PZero` (`emptyWrapper_separates`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.RhoQuoteDrop

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission CanonicalBags QuoteDrop RhoPresented
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Rho's reflective presentation. -/
abbrev presentation : ReflectivePresentationDecl := rhoReflectivePresentation.toReflectivePresentationDecl

theorem distinct : presentation.dropConstructor ≠ presentation.quoteConstructor := by decide

/-- **Rho types its reflective presentation**: `NQuote` takes a process to a name, `PDrop` a name to
a process, and `NQuote` is the only constructor of names. -/
theorem typedPresentation :
    QuoteDropTyped (GeneralPlanEnvironment.environment GeneralRho.Standard.plan).language presentation where
  quote rule member label := by
    rcases mem_terms member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [rhoCalc, presentation, rhoReflectivePresentation,
        TypeExpr.proc, TypeExpr.name, TypeExpr.baseType]
  drop rule member label := by
    rcases mem_terms member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [rhoCalc, presentation, rhoReflectivePresentation,
        TypeExpr.proc, TypeExpr.name, TypeExpr.baseType]
  names rule member category := by
    rcases mem_terms member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [rhoCalc, presentation, rhoReflectivePresentation]

/-- **A quoted name is never a reduction context.** -/
theorem quoteOpaque : QuoteOpaque GeneralRho.Standard.plan.permissions.sites presentation := by
  refine ⟨rfl, fun index member => ?_⟩
  change (presentation.quoteConstructor, index) ∈ GeneralRho.Standard.sites.constructorArguments at member
  simp [GeneralRho.Standard.sites] at member

/-- **COMM fires at quote-drop normal forms.** -/
theorem fires : RulesFireAtNormal GeneralRho.Standard.plan presentation := by
  intro declaration ordinal member rule spec selected specified
  obtain ⟨rfl, rfl, rfl⟩ := rule_at member selected specified
  refine ⟨rfl, ?_, ?_, .inr GeneralRho.substitution_selected⟩
  · rw [comm_left]
    simp [quoteFree, presentation, rhoReflectivePresentation]
  · decide +kernel

/-- **The explorer is complete for rho modulo its parallel laws and the name equation**: every
closed process reachable from a well-sorted closed process by finitely many steps modulo the
parallel laws and `@(*n) = n` is explored from the committed form of the process, up to both. -/
theorem rho_explores_quoteDrop (source : Pattern)
    (sorted : OpenPatternWellSorted (GeneralPlanEnvironment.environment GeneralRho.Standard.plan).language
      GeneralRho.Standard.plan.snapshot.free [] (.base "Proc") source)
    {target : Pattern}
    (reaches : (QuoteDropCoherence.gslt GeneralRho.Standard.plan [] (.base "Proc") presentation).MultiStep source target) :
    ∃ state, Explore.Explored (S := QuoteDropCoherence.search GeneralRho.Standard.plan [] (.base "Proc") presentation)
        (QuoteDropCoherence.commit GeneralRho.Standard.plan presentation source) state ∧
      QuoteDropCoherence.ModelEquiv GeneralRho.Standard.plan [] (.base "Proc") presentation state target :=
  QuoteDropCoherence.presented_explores_quoteDrop checked (noEquations [] (.base "Proc")) extrusions_eq canonical
    descentAdmissible (fun _ member => absurd member List.not_mem_nil) (show LawTypeOk _ _ (.base "Proc") from trivial)
    distinct typedPresentation quoteOpaque fires source sorted reaches

/-! ## Examples -/

/-- The empty process `0`. -/
def zero : Pattern := .apply "PZero" []

/-- The quoted empty process `@0`. -/
def quotedZero : Pattern := .apply "NQuote" [zero]

/-- Sending `0` on a channel. -/
def send (channel : Pattern) : Pattern := .apply "POutput" [channel, zero]

/-- **Positive example**: the channels `@0` and `@(*@0)` are one name. -/
theorem quoteDrop_identifies :
    QuoteDropCoherence.commit GeneralRho.Standard.plan presentation (send (.apply "NQuote" [.apply "PDrop" [quotedZero]])) =
      QuoteDropCoherence.commit GeneralRho.Standard.plan presentation (send quotedZero) := by
  have normalEq : normal presentation (send (.apply "NQuote" [.apply "PDrop" [quotedZero]])) =
      normal presentation (send quotedZero) := by decide +kernel
  simp only [QuoteDropCoherence.commit, normalEq]

/-- **Negative example**: the channels `@0` and `@{}` stay distinct. -/
theorem emptyWrapper_separates :
    QuoteDropCoherence.commit GeneralRho.Standard.plan presentation (send (.apply "NQuote" [.collection .hashBag [] none])) ≠
      QuoteDropCoherence.commit GeneralRho.Standard.plan presentation (send quotedZero) := by
  intro same
  have emptyNormal : normal presentation (send (.apply "NQuote" [.collection .hashBag [] none])) =
      send (.apply "NQuote" [.collection .hashBag [] none]) := by decide +kernel
  have zeroNormal : normal presentation (send quotedZero) = send quotedZero := by decide +kernel
  simp only [QuoteDropCoherence.commit, emptyNormal, zeroNormal] at same
  -- law-equal terms keep every constructor above their collections
  have related : LawSame (Normalized.laws GeneralRho.Standard.plan) (send quotedZero)
      (send (.apply "NQuote" [.collection .hashBag [] none])) :=
    .trans _ _ _ (to_lawNormal _ _) (same ▸ .symm _ _ (to_lawNormal _ _))
  obtain ⟨arguments, shape, pointwise⟩ := related.apply_inv
  simp only [send, Pattern.apply.injEq, true_and] at shape
  subst shape
  obtain ⟨quoted, _⟩ := List.forall₂_cons.mp pointwise
  obtain ⟨inner, innerShape, innerPointwise⟩ := quoted.apply_inv
  simp only [Pattern.apply.injEq, true_and] at innerShape
  subst innerShape
  obtain ⟨zeroSame, _⟩ := List.forall₂_cons.mp innerPointwise
  obtain ⟨_, impossible, _⟩ := zeroSame.apply_inv
  cases impossible

end Mettapedia.OSLF.MeTTaIL.Complete.RhoQuoteDrop
