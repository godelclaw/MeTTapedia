import Mettapedia.OSLF.Syntax.BindingClosedPredicateGuard
import Mettapedia.OSLF.Framework.RhoScopeMinimumReceiptTransport
import Mettapedia.OSLF.Framework.RhoScopeProbeRounds

/-!
# Ground-origin admission for native complementary scope guards

The closed origin is retained through the actual quotient-model
substitution. Constructed closed values at both rho sorts earn a retraction.
The terminating scope guard on these origins classifies both the native
generated predicate and its genuine Heyting negation. Current refutation
can therefore be promoted on this admitted family.

Actual paid probe responses receive the same constructed minimum
certificate or current-exclusion receipt, together with the supplied
closed origin and its stronger native verdict. This is a resource-GSLT
join; it does not lower a guarded receiver to a rho executor or price the
scope search's host computation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.Framework.RhoGroundedScopeGuard

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open BindingSubstitutionAlgebra BindingConstructorPredicates IntrinsicScopedConditionalPresheaf
open BindingPredicateFutureLogic BindingGroundedPredicates
open RhoEquationGeneratedScope RhoGeneratedScopeSubstitution RhoGeneratedScopeDecision
open RhoScopeMinimumReceipts RhoScopeMinimumReceiptTransport RhoScopeAssayReceipts
open Mettapedia.GSLT.Causality ResourceInteraction ProbeCampaign
open ComplementaryAssay (Verdict)

def defaults : (sort : Srt) → TermQ rhoSourceE [] sort
  | .pr => zero []
  | .nm => quote (zero [])

noncomputable section

def negative (left right : Predicate model Srt.pr) : Predicate model Srt.nm :=
  nativeNegation (native left right)

theorem negative_is_native (left right : Predicate model Srt.pr) :
    (negative left right).subfunctor = (native left right).subfunctor ⇨ ⊥ :=
  nativeNegation_subfunctor (native left right)

theorem grounded_membership (left right : Predicate model Srt.pr)
    (context : Ctx sig) (origin : Name []) :
    generated left.holds right.holds (ground (A := model) context origin) ↔ generated left.holds right.holds origin :=
  predicate_ground_iff defaults (native left right) context origin

theorem grounded_negation (left right : Predicate model Srt.pr)
    (context : Ctx sig) (origin : Name []) :
    (negative left right).holds (ground (A := model) context origin) ↔ ¬ generated left.holds right.holds origin :=
  nativeNegation_ground_iff defaults (native left right) context origin

def nativeVerdict (left right : Predicate model Srt.pr)
    {context : Ctx sig} (name : Name context) : Verdict → Prop
  | .confirm => (native left right).holds name
  | .refute => (negative left right).holds name

structure NativeDecisionReceipt (left right : Predicate model Srt.pr)
    {context : Ctx sig} (name : Name context) (branch : Verdict) where
  observed : DecisionReceipt left.holds right.holds name branch
  origin : GroundOrigin (A := model) (sort := Srt.nm) name
  sound : nativeVerdict left right name branch

def promote (left right : Predicate model Srt.pr)
    {context : Ctx sig} {name : Name context} {branch : Verdict}
    (receipt : DecisionReceipt left.holds right.holds name branch)
    (origin : GroundOrigin (A := model) (sort := Srt.nm) name) :
    NativeDecisionReceipt left right name branch where
  observed := receipt
  origin := origin
  sound := by
    cases branch with
    | confirm => exact decisionReceipt_sound receipt
    | refute =>
      exact ground_origin_promotes_exclusion defaults (native left right) origin
        (decisionReceipt_sound receipt)

variable (left right : Predicate model Srt.pr)
variable [∀ context : Ctx sig, DecidablePred (left.holds (Γ := context))]
variable [∀ context : Ctx sig, DecidablePred (right.holds (Γ := context))]

local instance scopeDecision (context : Ctx sig) :
    DecidablePred ((native left right).holds (Γ := context)) :=
  fun name => generatedDecision left.holds right.holds name

def classifier :
    closedPrograms (A := model) (sort := Srt.nm) ⟶
      BindingPredicateBooleanGuard.booleans (A := model) :=
  BindingClosedPredicateGuard.guard (native left right)

theorem positive_classifier :
    (native left right).subfunctor.preimage groundingMap =
      BindingClosedPredicateGuard.trueValues.preimage (classifier left right) :=
  BindingClosedPredicateGuard.positive_classifier (native left right) defaults

theorem negative_classifier :
    (negative left right).subfunctor.preimage groundingMap =
      BindingClosedPredicateGuard.falseValues.preimage (classifier left right) := by
  rw [negative_is_native]
  exact BindingClosedPredicateGuard.negative_classifier (native left right) defaults

/-- The least grade is preserved on this actual retraction. Independently
selected certificate trees are not identified. -/
theorem grounded_minimum_grade {context : Ctx sig} {origin : Name []}
    {sourceReceipt : Certificate left.holds right.holds origin}
    {targetReceipt : Certificate left.holds right.holds (ground (A := model) context origin)}
    (sourceReadout : minimumReceipt? left.holds right.holds origin = some sourceReceipt)
    (targetReadout : minimumReceipt? left.holds right.holds (ground (A := model) context origin) = some targetReceipt) :
    sourceReceipt.depth = targetReceipt.depth := by
  let forward : Environment sig (TermQ rhoSourceE) [] context :=
    emptyEnvironment (A := model) context
  let backward : Environment sig (TermQ rhoSourceE) context [] :=
    closingEnvironment (A := model) defaults context
  exact roundtrip_minimum_depths forward backward
    (fun process admitted => left.substitute forward process admitted)
    (fun process admitted => right.substitute forward process admitted)
    (fun process admitted => left.substitute backward process admitted)
    (fun process admitted => right.substitute backward process admitted)
    (closing_ground (A := model) defaults context origin) sourceReadout targetReadout

end

end Mettapedia.OSLF.Framework.RhoGroundedScopeGuard
