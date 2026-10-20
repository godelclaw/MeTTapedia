import Mettapedia.OSLF.Bridges.TypeTheory.AuthoredNaturalAdmission

/-!
# Authored natural admission controls

Finite declaration checks exercise the parsed module rows. Proof-bearing
controls separately exercise substitution, displayed-type adjustment, and
rejection of a raw executable instance whose branch is undeclared.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Bridges.TypeTheory.AuthoredNaturalAdmission.Controls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies

def advanceIndex : Fin Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.language.rewrites.length :=
  ⟨0, by decide +kernel⟩

def declarations : List (String × Bool) := [
  ("parsed signature", signatureMatches),
  ("parsed zero row", (admit? .zero zeroAdmission.index zeroName natEliminateName).isSome),
  ("parsed successor row", (admit? .succ succAdmission.index succName natEliminateName).isSome),
  ("counter advance is not eliminator computation",
    (admit? .zero advanceIndex zeroName natEliminateName).isNone),
  ("zero row cannot claim successor identity",
    (admit? .zero zeroAdmission.index succName natEliminateName).isNone),
  ("successor row cannot claim zero identity",
    (admit? .succ succAdmission.index zeroName natEliminateName).isNone),
  ("vector eliminator is a different declaration",
    (admit? .zero zeroAdmission.index zeroName vecEliminateName).isNone),
  ("successor endpoint does not bind to zero schema",
    (admit? .zero succAdmission.index zeroName natEliminateName).isNone),
  ("changed successor reduct is refused",
    decide (¬ Matches .succ { succAdmission.row with right := .fvar "s" }
      succName natEliminateName)),
  ("undeclared pattern variable is refused",
    (lowerPattern Branch.zero.environment (.fvar "undeclared")).isNone),
  ("binder is outside this concrete row interpretation",
    (lowerPattern Branch.zero.environment (.lambda none (.bvar 0))).isNone)]

theorem declarations_pass : declarations.all Prod.snd = true := by decide +kernel

#eval declarations

theorem canonical_zero_endpoints :
    HasType natContextPZS natZeroIotaLeft natZeroIotaType ∧
    HasType natContextPZS natZeroIotaRight natZeroIotaType := by
  have receipt := zeroAdmission.endpoints_typed natContextPZS ids
    (CtxMor.identity rules natContextPZS) (subst ids Branch.zero.schema.type) (.refl _)
  simpa only [Admission.left_eq, Admission.right_eq, subst_ids, Branch.schema, natZeroIotaSchema] using receipt

/-- Deliberately display a type which is convertible to, but syntactically
different from, the principal result type. -/
def betaExpanded {scope : Nat} (type : Tower.Tm scope) : Tower.Tm scope :=
  .app (.lam (rename wk type)) zeroTm

theorem betaExpanded_adjustment {scope : Nat} (type : Tower.Tm scope) :
    TypeAdjustment rules type (betaExpanded type) := by
  have reduction : StepCore rules.computation rules.headEq (betaExpanded type) type := by
    simpa only [betaExpanded, inst0_rename_wk] using
      (StepCore.betaPi (root := rules.computation) (headEq := rules.headEq)
        (rename wk type) zeroTm)
  exact .conversion (.symm _ _ (.rel _ _ reduction))

def extendedContext : Tower.Ctx 5 := .snoc natContextPZSN natTm

def principalType : Tower.Tm 5 := subst projection natSuccIotaType

def displayedType : Tower.Tm 5 := betaExpanded principalType

def weakenedSuccessorReceipt :
    TypedIotaReceipt extendedContext
      (subst projection succAdmission.left) (subst projection succAdmission.right) displayedType :=
  succAdmission.typedReceipt extendedContext projection
    (CtxMor.projectionTyped rules natContextPZSN natTm) displayedType
    (betaExpanded_adjustment principalType)

theorem weakening_retains_displayed_type :
    HasType extendedContext (rename wk natSuccIotaLeft) displayedType ∧
    HasType extendedContext (rename wk natSuccIotaRight) displayedType := by
  have receipt := weakenedSuccessorReceipt
  constructor
  · simpa only [Admission.left_eq, subst_projection, Branch.schema, natSuccIotaSchema] using receipt.sourceTyping
  · simpa only [Admission.right_eq, subst_projection, Branch.schema, natSuccIotaSchema] using receipt.targetTyping

theorem displayed_type_is_not_principal : displayedType ≠ principalType := by decide +kernel

/-- The module's accepted declaration does not admit all of its raw instances. -/
theorem undeclared_branch_has_no_adjusted_receipt (type : Tower.Tm 0) :
    ¬ Nonempty (TypedIotaInstance.Adjusted (.nil : Tower.Ctx 0)
      untypedNatZeroLeft zeroTm type) := by
  rintro ⟨receipt⟩
  exact untypedNatZeroLeft_not_hasType type receipt.toReceipt.sourceTyping

theorem undeclared_branch_has_no_typed_substitution
    (substitution : Sub Tower.Head Branch.zero.arity 0)
    (sameSource : subst substitution zeroAdmission.left = untypedNatZeroLeft) :
    ¬ CtxMor rules Branch.zero.schema.context (.nil : Tower.Ctx 0) substitution := by
  intro typed
  have sourceTyping :=
    (zeroAdmission.typedReceipt .nil substitution typed
      (subst substitution Branch.zero.schema.type) (.refl _)).sourceTyping
  rw [sameSource] at sourceTyping
  exact untypedNatZeroLeft_not_hasType _ sourceTyping

theorem source_execution_and_typed_admission_are_distinct
    (base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base
      Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.language
      AuthoredNaturalCounter.untypedSource.encode
      (Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.Term.number 0).encode ∧
    ∀ type : Tower.Tm 0,
      ¬ Nonempty (TypedIotaInstance.Adjusted (.nil : Tower.Ctx 0)
        untypedNatZeroLeft zeroTm type) :=
  ⟨AuthoredNaturalCounter.untyped_source_executes base,
    undeclared_branch_has_no_adjusted_receipt⟩

end Mettapedia.OSLF.Bridges.TypeTheory.AuthoredNaturalAdmission.Controls
