import Mettapedia.GSLT.LanguageDef.InitialRuleClosureAuthority
import Mettapedia.UniversalAlgebra.Certificate
import Mettapedia.UniversalAlgebra.Instances.Monoid

/-!
# Equation systems as SemanticService authorities

An equation system supplies SemanticService with three deliberately separate components:
least equational consequence as proof scope, truth in every model as meaning,
and finite witnessed derivation trees as replay certificates.  Replay checks
scope exactly; semantic soundness follows independently from the model theory.

Formerly `Mettapedia.UniversalAlgebra.NIK.Authority`, part of the native inference kernel (NIK) development of 2026-08-11 to 2026-10-08; renamed to its subject name on 2026-10-08.
The namespace was `Mettapedia.UniversalAlgebra.NIK`; it is now `Mettapedia.UniversalAlgebra.SemanticService`.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra.SemanticService

open Mettapedia.Logic
open Mettapedia.GSLT.LanguageDef.InitialRuleClosureAuthority
open Mettapedia.GSLT.LanguageDef.SemanticEvidence

universe u

variable {S : Signature.{u}} [DecidableEq S.Operation]

/-- The generic qualified rule-system package for equational logic. -/
def qualifiedRuleSystem (system : EquationSystem S) :
    QualifiedRuleSystem.{u, u} (Equation S) where
  rules := EquationalRule system
  witness := equationalRuleInterface system
  Meaning := Entails system
  rules_sound := equationalRule_sound system

/-- A SemanticService theory whose scope is generated equational consequence and whose
meaning is validity in every model of the equation system. -/
def theory (system : EquationSystem S) :=
  (qualifiedRuleSystem system).theory

/-- The exact replay contract for an equation system. -/
def contract (system : EquationSystem S) :=
  (qualifiedRuleSystem system).contract

/-- Every accepted equational certificate denotes an equation valid in every
model of the system. -/
theorem accepted_entails (system : EquationSystem S) (equation : Equation S)
    (certificate : Derivation (Equation S)
      (EquationalRuleWitness system))
    (accepted : ((contract system).checker ()).check equation certificate = true) :
    Entails system equation :=
  ((contract system).projection ()).sound equation certificate accepted

/-! ## Executable positive and negative controls -/

open Mettapedia.UniversalAlgebra.Monoid

/-- The nontrivial monoid derivation has an accepted SemanticService certificate. -/
theorem monoid_positive_certificate :
    ∃ certificate,
      ((contract equationSystem).checker ()).check
        (mul (mul one x) one, x) certificate = true :=
  ((contract equationSystem).scopeAuthority ()).complete _ one_mul_mul_one

/-- No certificate can make two distinct variables a monoid consequence. -/
theorem monoid_negative_certificate :
    ¬ ∃ certificate,
      ((contract equationSystem).checker ()).check
        ((Term.var 0 : Term signature), Term.var 1) certificate = true := by
  rintro ⟨certificate, accepted⟩
  exact distinct_variables_not_consequence
    (((contract equationSystem).scopeAuthority ()).sound _ certificate accepted)

end Mettapedia.UniversalAlgebra.SemanticService
