import Mettapedia.OSLF.MeTTaIL.StructuralDescentAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseWeakening

/-!
# Computed prerequisites for contextual operational evidence

Positive relation queries are checked against the actual finite provider
snapshot, including inside quantified bodies. Syntactic freshness is refused.
Closed rows are admitted from their original authored sorts, and recursive
calls use the existing declaration-derived structural descent check.

Passing these checks establishes precisely the stated prerequisites. A
complete firing substitution action and a two-sided query comparison are
separate semantic obligations; this checker does not silently supply them.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeOperationalAdmission

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.GSLT.LanguageDef.WellSorted

inductive PositivePremise (provider : ProviderSnapshot) : Premise → Prop where
  | query {relation : String} {arguments : List Pattern} {signature : Signature} :
      signature? provider relation arguments.length = some signature →
      PositivePremise provider (.relationQuery relation arguments)
  | child (source target : Pattern) : PositivePremise provider (.congruence source target)
  | scopedChild (step : ScopedStepPremise) : PositivePremise provider (.scopedStep step)
  | quantified {collection parameter : String} {body : Premise} :
      PositivePremise provider body → PositivePremise provider (.forAll collection parameter body)

def checkPremise (provider : ProviderSnapshot) : Premise → Bool
  | .freshness _ => false
  | .relationQuery relation arguments => (signature? provider relation arguments.length).isSome
  | .congruence _ _ | .scopedStep _ => true
  | .forAll _ _ body => checkPremise provider body

theorem checkPremise_sound {provider : ProviderSnapshot} {premise : Premise}
    (checked : checkPremise provider premise = true) : PositivePremise provider premise := by
  induction premise with
  | freshness condition => cases checked
  | congruence source target => exact .child source target
  | scopedStep step => exact .scopedChild step
  | relationQuery relation arguments =>
      cases selected : signature? provider relation arguments.length with
      | none => simp only [checkPremise, selected, Option.isSome_none] at checked; cases checked
      | some signature => exact .query selected
  | forAll collection parameter body ih => exact .quantified (ih checked)

theorem checkPremise_complete {provider : ProviderSnapshot} {premise : Premise}
    (positive : PositivePremise provider premise) : checkPremise provider premise = true := by
  induction positive with
  | query selected => simp only [checkPremise, selected, Option.isSome_some]
  | child | scopedChild => rfl
  | quantified _ ih => exact ih

theorem checkPremise_exact (provider : ProviderSnapshot) (premise : Premise) :
    checkPremise provider premise = true ↔ PositivePremise provider premise :=
  ⟨checkPremise_sound, checkPremise_complete⟩

theorem freshness_refused (provider : ProviderSnapshot) (condition : FreshnessCondition) :
    checkPremise provider (.freshness condition) = false := rfl

theorem missing_query_refused {provider : ProviderSnapshot} {relation : String}
    {arguments : List Pattern}
    (missing : signature? provider relation arguments.length = none) :
    checkPremise provider (.relationQuery relation arguments) = false := by
  simp only [checkPremise, missing, Option.isSome_none]

/-- Provider admission is specified directly by authored signature data and
the independent heterogeneous row typing judgment. -/
structure ClosedProvider (language : LanguageDef) (free : FreeTypeContext)
    (provider : ProviderSnapshot) : Prop where
  modeLengths : ∀ signature ∈ provider.signatures,
    signature.argumentTypes.length = signature.modes.length
  unique : (provider.signatures.map fun signature =>
    (signature.relation, signature.argumentTypes.length)).Nodup
  rows : ∀ row ∈ provider.rows, ∃ signature,
    signature? provider row.relation row.values.length = some signature ∧
      RowTyped language free [] signature row

theorem closedProvider_sound {language : LanguageDef} {free : FreeTypeContext}
    {provider : ProviderSnapshot}
    (checked : checkProviderClosed language free provider = true) :
    ClosedProvider language free provider := by
  have parts := checked
  simp only [checkProviderClosed, Bool.and_eq_true, decide_eq_true_eq] at parts
  refine ⟨?_, parts.1.2, ?_⟩
  · intro signature present
    simpa only [beq_iff_eq] using List.all_eq_true.mp parts.1.1 signature present
  · intro row present
    exact checkProviderClosed_row language free provider checked row present

theorem closedProvider_complete {language : LanguageDef} {free : FreeTypeContext}
    {provider : ProviderSnapshot} (closed : ClosedProvider language free provider) :
    checkProviderClosed language free provider = true := by
  simp only [checkProviderClosed, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, closed.unique⟩, ?_⟩
  · apply List.all_eq_true.mpr
    intro signature present
    simpa only [beq_iff_eq] using closed.modeLengths signature present
  · apply List.all_eq_true.mpr
    intro row present
    obtain ⟨signature, selected, typed⟩ := closed.rows row present
    simpa only [selected] using checkRow_complete typed

theorem closedProvider_exact (language : LanguageDef) (free : FreeTypeContext)
    (provider : ProviderSnapshot) :
    checkProviderClosed language free provider = true ↔ ClosedProvider language free provider :=
  ⟨closedProvider_sound, closedProvider_complete⟩

def PositiveRules (environment : Environment) : Prop :=
  ∀ rule ∈ environment.language.rewrites, ∀ premise ∈ rule.premises,
    PositivePremise environment.provider premise

def checkPositiveRules (environment : Environment) : Bool :=
  environment.language.rewrites.all fun rule => rule.premises.all (checkPremise environment.provider)

theorem positiveRules_exact (environment : Environment) :
    checkPositiveRules environment = true ↔ PositiveRules environment := by
  simp only [checkPositiveRules, PositiveRules, List.all_eq_true, checkPremise_exact]

structure Prerequisites (environment : Environment) : Prop where
  closed : ClosedProvider environment.language environment.free environment.provider
  positive : PositiveRules environment
  recursive : StructuralDescent.checkEnvironment environment = true

def checkPrerequisites (environment : Environment) : Bool :=
  checkProviderClosed environment.language environment.free environment.provider &&
    checkPositiveRules environment && StructuralDescent.checkEnvironment environment

theorem prerequisites_exact (environment : Environment) :
    checkPrerequisites environment = true ↔ Prerequisites environment := by
  simp only [checkPrerequisites, Bool.and_eq_true, closedProvider_exact, positiveRules_exact]
  constructor
  · rintro ⟨⟨closed, positive⟩, recursive⟩
    exact ⟨closed, positive, recursive⟩
  · intro ready
    exact ⟨⟨ready.closed, ready.positive⟩, ready.recursive⟩

/-- The fixed-snapshot executor can support more premise forms than these
contextual reindexing prerequisites permit. Neither status is an assertion
that the complete event interpretation is already natural. -/
structure Report where
  operational : Bool
  reindexingPrerequisites : Bool
  deriving Repr, DecidableEq

def inspect (environment : Environment) : Report where
  operational := StructuralDescent.checkEnvironment environment
  reindexingPrerequisites := checkPrerequisites environment

theorem prerequisite_is_operational {environment : Environment}
    (ready : (inspect environment).reindexingPrerequisites = true) :
    (inspect environment).operational = true :=
  (prerequisites_exact environment).mp ready |>.recursive

theorem prerequisites_row_any_context {environment : Environment}
    (ready : checkPrerequisites environment = true) {row : ProviderRow}
    (member : row ∈ environment.provider.rows) (bound : List TypeExpr) :
    ∃ signature, signature? environment.provider row.relation row.values.length = some signature ∧
      RowTyped environment.language environment.free bound signature row := by
  obtain ⟨signature, selected, typed⟩ := ((prerequisites_exact environment).mp ready).closed.rows row member
  exact ⟨signature, selected, closed_row_in_bound typed bound⟩

end Mettapedia.OSLF.NativeTypes.Modal.NativeOperationalAdmission
