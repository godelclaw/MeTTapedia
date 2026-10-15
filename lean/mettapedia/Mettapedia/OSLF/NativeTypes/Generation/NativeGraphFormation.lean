import Mettapedia.OSLF.NativeTypes.Generation.NativeDeclarations

/-!
# Formation certificates for generated constructor graphs

The graph is quantified logical equality with the declared constructor
operation. Its formation certificate retains the supplied ordered argument
substitution and the separate target typing derivation. Binding parameters
remain ordinary dependent function parameters in the generated telescope.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.NativeEquality

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

universe u
variable {S : Symbols.{u}} {D : Signature S}

def weakenType {n : Nat} (context : ContextExpr S n) (binder carrier : TypeExpr S n)
    (binderFormed : Derivation D (.type context binder))
    (carrierFormed : Derivation D (.type context carrier)) :
    Derivation D (.type (.snoc context binder) (carrier.rename Fin.succ)) := by
  simpa only [RuleCode.conclusion, TypeExpr.substitute_variables] using
    deriveList (.substituteType (.snoc context binder) context (fun i => .var i.succ) carrier)
      (.cons (deriveList (.substitutionWeaken context binder) (.cons binderFormed .nil))
        (.cons carrierFormed .nil))

def weakenTerm {n : Nat} (context : ContextExpr S n) (binder carrier : TypeExpr S n)
    (term : TermExpr S n) (binderFormed : Derivation D (.type context binder))
    (typed : Derivation D (.term context term carrier)) :
    Derivation D (.term (.snoc context binder) (term.rename Fin.succ) (carrier.rename Fin.succ)) := by
  simpa only [RuleCode.conclusion, TypeExpr.substitute_variables, TermExpr.substitute_variables] using
    deriveList (.substituteTerm (.snoc context binder) context (fun i => .var i.succ) term carrier)
      (.cons (deriveList (.substitutionWeaken context binder) (.cons binderFormed .nil))
        (.cons typed .nil))

def predicateFormation {n : Nat} (context : ContextExpr S n) (carrier : TypeExpr S n)
    (contextFormed : Derivation D (.context context))
    (carrierFormed : Derivation D (.type context carrier)) :
    Derivation D (.type context (predicateType carrier)) :=
  deriveList (.piFormation context carrier .propositions)
    (.cons carrierFormed (.cons
      (deriveList (.propositionType (.snoc context carrier))
        (.cons (deriveList (.contextExtend context carrier)
          (.cons contextFormed (.cons carrierFormed .nil))) .nil)) .nil))

def applicationFormation {n : Nat} (context : ContextExpr S n) (carrier : TypeExpr S n)
    (value : TermExpr S n) (contextFormed : Derivation D (.context context))
    (carrierFormed : Derivation D (.type context carrier))
    (typed : Derivation D (.term context value carrier)) :
    Derivation D (.predicate (.snoc context (predicateType carrier))
      (.holds (.app (carrier.rename Fin.succ) .propositions (.var 0) (value.rename Fin.succ)))) := by
  let predicateFormed := predicateFormation context carrier contextFormed carrierFormed
  let extended := deriveList (.contextExtend context (predicateType carrier))
    (.cons contextFormed (.cons predicateFormed .nil))
  let domainFormed := weakenType context (predicateType carrier) carrier predicateFormed carrierFormed
  let bodyFormed := deriveList
    (.propositionType (.snoc (.snoc context (predicateType carrier)) (carrier.rename Fin.succ)))
    (.cons (deriveList
      (.contextExtend (.snoc context (predicateType carrier)) (carrier.rename Fin.succ))
      (.cons extended (.cons domainFormed .nil))) .nil)
  have variableTyped : Derivation D (.term (.snoc context (predicateType carrier)) (.var 0)
      (.pi (carrier.rename Fin.succ) .propositions)) := by
    simpa only [RuleCode.conclusion, ContextExpr.lookup_zero, predicateType, TypeExpr.rename] using
      deriveList (.variable (.snoc context (predicateType carrier)) 0) (.cons extended .nil)
  have applied : Derivation D (.term (.snoc context (predicateType carrier))
      (.app (carrier.rename Fin.succ) .propositions (.var 0) (value.rename Fin.succ)) .propositions) :=
    deriveList (.application (.snoc context (predicateType carrier))
      (carrier.rename Fin.succ) .propositions (.var 0) (value.rename Fin.succ))
      (.cons domainFormed (.cons bodyFormed (.cons variableTyped
        (.cons (weakenTerm context (predicateType carrier) carrier value predicateFormed typed) .nil))))
  exact deriveList (.holdsFormation _ _) (.cons applied .nil)

def formation {n : Nat} (context : ContextExpr S n) (carrier : TypeExpr S n)
    (first second : TermExpr S n) (contextFormed : Derivation D (.context context))
    (carrierFormed : Derivation D (.type context carrier))
    (firstTyped : Derivation D (.term context first carrier))
    (secondTyped : Derivation D (.term context second carrier)) :
    Derivation D (.predicate context (equal carrier first second)) :=
  deriveList (.universalFormation context (predicateType carrier) _)
    (.cons (predicateFormation context carrier contextFormed carrierFormed)
      (.cons (deriveList (.implicationFormation (.snoc context (predicateType carrier)) _ _)
        (.cons (applicationFormation context carrier first contextFormed carrierFormed firstTyped)
          (.cons (applicationFormation context carrier second contextFormed carrierFormed secondTyped) .nil))) .nil))

end Mettapedia.OSLF.NativeTypes.Generation.NativeEquality

namespace Mettapedia.OSLF.NativeTypes.Generation.NativeSignature.Installation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.Calculi.NativeDependent

variable {language : LanguageDef} (installed : Installation language)

def primitiveTyping (constructor : installed.Constructor) {n : Nat}
    (context : Refinement.ContextExpr installed.symbols n)
    (arguments : Fin (installed.parameters constructor).length → Refinement.TermExpr installed.symbols n)
    (contextFormed : Refinement.Derivation installed.signature (.context context))
    (argumentsTyped : Refinement.Derivation installed.signature
      (.substitution context (installed.signature.termParameters constructor) arguments)) :
    Refinement.Derivation installed.signature
      (.term context (.primitive constructor arguments) (installed.result constructor).native) := by
  have original := Refinement.deriveList (.primitive context constructor arguments)
    (.cons contextFormed (.cons (installed.formation.termHeader constructor)
      (.cons (installed.formation.termResult constructor) (.cons argumentsTyped .nil))))
  change Refinement.Derivation installed.signature
    (.term context (.primitive constructor arguments)
      ((installed.result constructor).native.substitute arguments)) at original
  simpa only [Carrier.native_substitute] using original

def graphFormation (constructor : installed.Constructor) {n : Nat}
    (context : Refinement.ContextExpr installed.symbols n)
    (arguments : Fin (installed.parameters constructor).length → Refinement.TermExpr installed.symbols n)
    (target : Refinement.TermExpr installed.symbols n)
    (contextFormed : Refinement.Derivation installed.signature (.context context))
    (argumentsTyped : Refinement.Derivation installed.signature
      (.substitution context (installed.signature.termParameters constructor) arguments))
    (targetTyped : Refinement.Derivation installed.signature
      (.term context target (installed.result constructor).native)) :
    Refinement.Derivation installed.signature (.predicate context (installed.graph constructor arguments target)) :=
  NativeEquality.formation context (installed.result constructor).native target
    (.primitive constructor arguments) contextFormed
    (carrierFormation (installed.result constructor) context contextFormed)
    targetTyped (installed.primitiveTyping constructor context arguments contextFormed argumentsTyped)

theorem graphFormation_checked (constructor : installed.Constructor) {n : Nat}
    (context : Refinement.ContextExpr installed.symbols n)
    (arguments : Fin (installed.parameters constructor).length → Refinement.TermExpr installed.symbols n)
    (target : Refinement.TermExpr installed.symbols n)
    (contextFormed : Refinement.Derivation installed.signature (.context context))
    (argumentsTyped : Refinement.Derivation installed.signature
      (.substitution context (installed.signature.termParameters constructor) arguments))
    (targetTyped : Refinement.Derivation installed.signature
      (.term context target (installed.result constructor).native)) :
    installed.check (Certificates.Refinement.erase
      (installed.graphFormation constructor context arguments target contextFormed argumentsTyped targetTyped))
      (.predicate context (installed.graph constructor arguments target)) = true :=
  Certificates.Refinement.check_erase _

end Mettapedia.OSLF.NativeTypes.Generation.NativeSignature.Installation
