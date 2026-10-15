import Mettapedia.OSLF.Framework.RhoGroundedScopeGuard

/-!
# Complete future substitution of grounded assay receipts

A supplied closed origin supplies a local inverse for every future map on
that name. Transport of the actual confirmation certificate is therefore
still least, although future substitution need not be invertible on other
names. Refutation transports its full native negative certificate. Both
branches retain the supplied closed origin and the confirmation's ordered
atomic premises.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.Framework.RhoGroundedScopeReceiptSubstitution

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open BindingSubstitutionAlgebra BindingConstructorPredicates BindingPredicateFutureLogic
open BindingGroundedPredicates
open RhoEquationGeneratedScope RhoGeneratedScopeSubstitution
open RhoGroundedScopeGuard RhoScopeAssayReceipts
open Mettapedia.GSLT.Causality.ComplementaryAssay (Verdict)

noncomputable section

def returnEnvironment (source target : Ctx sig) :
    Environment sig (TermQ rhoSourceE) target source :=
  fun sort _ => ground (A := model) source (defaults sort)

theorem grounded_roundtrip {source target : Ctx sig}
    (env : Environment sig (TermQ rhoSourceE) source target)
    {name : Name source} (origin : GroundOrigin (A := model) (sort := Srt.nm) name) :
    model.substitution.substitute (returnEnvironment source target)
      (model.substitution.substitute env name) = name := by
  rw [← origin.property, substitute_ground, substitute_ground]

def substitute {source target : Ctx sig} {left right : Predicate model Srt.pr}
    {name : Name source} {branch : Verdict}
    (env : Environment sig (TermQ rhoSourceE) source target)
    (receipt : NativeDecisionReceipt left right name branch) :
    NativeDecisionReceipt left right (model.substitution.substitute env name) branch where
  observed := by
    cases branch with
    | confirm =>
      cases receipt.observed with
      | confirm certificate least =>
        refine .confirm
          (transport env
            (fun process admitted => left.substitute env process admitted)
            (fun process admitted => right.substitute env process admitted) certificate) ?_
        intro other
        let returned : Certificate left.holds right.holds name :=
          grounded_roundtrip env receipt.origin ▸
            transport (returnEnvironment source target)
              (fun process admitted => left.substitute (returnEnvironment source target) process admitted)
              (fun process admitted => right.substitute (returnEnvironment source target) process admitted)
              other
        have depth : returned.depth = other.depth := by
          simp only [returned, depth_cast, transport_depth]
        have bound := least returned
        rw [depth] at bound
        simpa only [transport_depth] using bound
    | refute =>
      exact .refute (nativeNegation_excludes_current (native left right)
        ((negative left right).substitute env name receipt.sound))
  origin := receipt.origin.substitute env
  sound := by
    cases branch with
    | confirm => exact (native left right).substitute env name receipt.sound
    | refute => exact (negative left right).substitute env name receipt.sound

theorem supplied_closed_origin_retained {source target : Ctx sig}
    {left right : Predicate model Srt.pr} {name : Name source} {branch : Verdict}
    (env : Environment sig (TermQ rhoSourceE) source target)
    (receipt : NativeDecisionReceipt left right name branch) :
    (substitute env receipt).origin.val = receipt.origin.val := rfl

theorem confirmation_depth_retained {source target : Ctx sig}
    {left right : Predicate model Srt.pr} {name : Name source}
    (env : Environment sig (TermQ rhoSourceE) source target)
    (receipt : NativeDecisionReceipt left right name .confirm) :
    (positiveCertificate (substitute env receipt).observed).depth =
      (positiveCertificate receipt.observed).depth := by
  cases receipt with
  | mk observed origin sound =>
    cases observed with
    | confirm certificate least =>
      exact transport_depth env
        (fun process admitted => left.substitute env process admitted)
        (fun process admitted => right.substitute env process admitted) certificate

theorem confirmation_premises_retained {source target : Ctx sig}
    {left right : Predicate model Srt.pr} {name : Name source}
    (env : Environment sig (TermQ rhoSourceE) source target)
    (receipt : NativeDecisionReceipt left right name .confirm) :
    (positiveCertificate (substitute env receipt).observed).atomicOrigins =
      (positiveCertificate receipt.observed).atomicOrigins.map
        (Sum.map (model.substitution.substitute env) (model.substitution.substitute env)) := by
  cases receipt with
  | mk observed origin sound =>
    cases observed with
    | confirm certificate least =>
      exact transport_atomicOrigins env
        (fun process admitted => left.substitute env process admitted)
        (fun process admitted => right.substitute env process admitted) certificate

end

end Mettapedia.OSLF.Framework.RhoGroundedScopeReceiptSubstitution
