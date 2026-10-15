import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.RefinementBridge
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementConstructorInterpretation
import Mettapedia.TypeTheory.PresheafNativePropositionSubstitution

/-!
# Generated higher-order fixed-point encodings in the common native grammar

No fixed-point constructor or predicate oracle is added. Quantification is
over the actual ordinary type `A → Prop`; predicate application uses the
existing typed application and proposition readout. The operator body is
placed under both actual binders with capture-avoiding renaming.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.FixedPointSyntax

open _root_.CategoryTheory Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open NativeLocalTypeFormers PresheafNativePropositionReadout
open DisplayedPresheafComprehension

universe u v z
variable {S : Symbols.{v}} {Atom : Type z} {n : Nat}

def predicateType (domain : TypeExpr S n) : TypeExpr S n := .pi domain .propositions

def application (domain : TypeExpr S n) (predicate argument : TermExpr S n) : PropExpr S n :=
  .holds (.app domain .propositions predicate argument)

/-- Insert the predicate binder before the already authored tested argument. -/
def insertPredicate : Renaming (n + 1) (n + 2) :=
  Fin.cases 0 (fun index => index.succ.succ)

def operatorAt (domain : TypeExpr S n) (atoms : Atom → PropExpr S (n + 1))
    (body : Logic.Formula (Sum Atom Unit)) : PropExpr S (n + 2) :=
  RefinementBridge.embed
    (Sum.elim (fun name => (atoms name).rename insertPredicate)
      (fun _ => application (domain.rename Fin.succ |>.rename Fin.succ) (.var 1) (.var 0))) body

def candidateAt (domain : TypeExpr S n) : PropExpr S (n + 2) :=
  application (domain.rename Fin.succ |>.rename Fin.succ) (.var 1) (.var 0)

def prefixed (domain : TypeExpr S n) (atoms : Atom → PropExpr S (n + 1))
    (body : Logic.Formula (Sum Atom Unit)) : PropExpr S (n + 1) :=
  .all (domain.rename Fin.succ) (.implies (operatorAt domain atoms body) (candidateAt domain))

def postfixed (domain : TypeExpr S n) (atoms : Atom → PropExpr S (n + 1))
    (body : Logic.Formula (Sum Atom Unit)) : PropExpr S (n + 1) :=
  .all (domain.rename Fin.succ) (.implies (candidateAt domain) (operatorAt domain atoms body))

/-- Correct least encoding: every pre-fixed predicate contains the result. -/
def least (domain : TypeExpr S n) (atoms : Atom → PropExpr S (n + 1))
    (body : Logic.Formula (Sum Atom Unit)) (tested : TermExpr S n) : PropExpr S n :=
  .all (predicateType domain)
    (.implies (prefixed domain atoms body)
      (application (domain.rename Fin.succ) (.var 0) (tested.rename Fin.succ)))

/-- Correct greatest encoding: a post-fixed predicate witnesses membership. -/
def greatest (domain : TypeExpr S n) (atoms : Atom → PropExpr S (n + 1))
    (body : Logic.Formula (Sum Atom Unit)) (tested : TermExpr S n) : PropExpr S n :=
  .exists (predicateType domain)
    (.and (postfixed domain atoms body)
      (application (domain.rename Fin.succ) (.var 0) (tested.rename Fin.succ)))

/-- Variance refusal precedes emitting either derived higher-order formula. -/
def generate (domain : TypeExpr S n) (atoms : Atom → PropExpr S (n + 1))
    (body : Logic.Formula (Sum Atom Unit)) (tested : TermExpr S n) :
    Option (PropExpr S n × PropExpr S n) :=
  if Monotone.variance true body then
    some (least domain atoms body tested, greatest domain atoms body tested) else none

theorem generate_none_iff (domain : TypeExpr S n) (atoms : Atom → PropExpr S (n + 1))
    (body : Logic.Formula (Sum Atom Unit)) (tested : TermExpr S n) :
    generate domain atoms body tested = none ↔ Monotone.variance true body = false := by
  cases checked : Monotone.variance true body <;> simp [generate, checked]

variable {C : Type u} [Category.{u} C]

/-- The generated power type uses the original native dependent-product evaluator. -/
theorem evaluate_predicateType (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1)
    (domainRead : model.evaluateType context domain = some A) :
    model.evaluateType context (predicateType domain) =
      some (NativeLocalTypeFormers.pi A (nativeOmega (totalSpace A.decoded))) := by
  exact model.evaluate_pi context domain .propositions A _ domainRead
    (model.evaluate_propositions (context.snoc A))

noncomputable def applicationValue {P : Cᵒᵖ ⥤ Type u} (A : NativeType P)
    (function : (NativeLocalTypeFormers.pi A
      (nativeOmega (totalSpace A.decoded))).decoded.sections)
    (value : A.decoded.sections) : (nativeOmega P).decoded.sections :=
  cast (congrArg (fun type : NativeType P => ↥type.decoded.sections)
    (nativeOmega_reindex (sectionLift A.decoded value)))
    (NativeLocalTypeOperations.app function value)

theorem applicationValue_substitution {P : Cᵒᵖ ⥤ Type u} (A : NativeType P)
    (function : (NativeLocalTypeFormers.pi A
      (nativeOmega (totalSpace A.decoded))).decoded.sections)
    (value : A.decoded.sections) :
    applicationValue A function value =
      PresheafNativePropositionSubstitution.substituteNative (sectionLift A.decoded value)
        ((NativeLocalTypeOperations.functionEquiv A
          (nativeOmega (totalSpace A.decoded))).symm function) := by
  rfl

theorem applicationValue_holds {P : Cᵒᵖ ⥤ Type u} (A : NativeType P)
    (function : (NativeLocalTypeFormers.pi A
      (nativeOmega (totalSpace A.decoded))).decoded.sections)
    (value : A.decoded.sections) :
    nativeHolds (applicationValue A function value) =
      (nativeHolds ((NativeLocalTypeOperations.functionEquiv A
          (nativeOmega (totalSpace A.decoded))).symm function)).preimage
        (sectionLift A.decoded value) := by
  rw [applicationValue_substitution,
    PresheafNativePropositionSubstitution.nativeHolds_substituteNative]

/-- Application in the emitted formulas actually evaluates a native Π term
and reads its returned sieve; it does not call an atomic predicate oracle. -/
theorem evaluate_application (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1)
    (predicate argument : TermExpr S n)
    (function : (NativeLocalTypeFormers.pi A
      (nativeOmega (totalSpace A.decoded))).decoded.sections)
    (value : A.decoded.sections)
    (domainRead : model.evaluateType context domain = some A)
    (functionRead : model.evaluateTerm context predicate = some ⟨_, function⟩)
    (valueRead : model.evaluateTerm context argument = some ⟨_, value⟩) :
    model.evaluatePredicate context (application domain predicate argument) =
      some (nativeHolds (applicationValue A function value)) := by
  have evaluated := model.evaluate_application context domain .propositions A
    (nativeOmega (totalSpace A.decoded)) domainRead
    (model.evaluate_propositions (context.snoc A)) predicate argument function value
    functionRead valueRead
  have typeSame := nativeOmega_reindex (sectionLift A.decoded value)
  have termRead : model.evaluateTerm context (.app domain .propositions predicate argument) =
      some ⟨nativeOmega context.1, applicationValue A function value⟩ := by
    apply evaluated.trans
    apply congrArg some
    apply Sigma.ext typeSame
    exact (cast_heq (congrArg (fun type : NativeType context.1 => ↥type.decoded.sections)
      typeSame) (NativeLocalTypeOperations.app function value)).symm
  exact model.evaluate_holds context _ _ termRead

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.FixedPointSyntax
