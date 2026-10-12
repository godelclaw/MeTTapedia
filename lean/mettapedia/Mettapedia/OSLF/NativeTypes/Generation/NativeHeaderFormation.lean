import Mettapedia.OSLF.NativeTypes.Generation.NativeSignature
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementHeaderFormation

/-!
# Generated native declaration formation

Authored sort and constructor headers produce actual native derivation trees.
Each constructor parameter is formed at its own mixed-context position;
function parameters are formed by the dependent function rule. Constructor
graphs are derived from these operations and native logical equality.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.NativeSignature

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

variable {language : LanguageDef} {headers : List (Header language)}

abbrev declarations := signature language headers

def emptyContext : Derivation (signature language headers) (.context .nil) :=
  deriveList .contextNil .nil

def carrierFormation (carrier : Carrier language) {n : Nat}
    (context : ContextExpr (symbols language headers) n)
    (formed : Derivation (signature language headers) (.context context)) :
    Derivation (signature language headers) (.type context carrier.native) :=
  match carrier with
  | .sort position =>
      deriveList (.typeFamily context position Fin.elim0)
        (.cons formed (.cons emptyContext
          (.cons (deriveList (.substitutionNil context) (.cons formed .nil)) .nil)))
  | .function domain codomain =>
      let domainTree := carrierFormation domain context formed
      let extended := deriveList (.contextExtend context domain.native)
        (.cons formed (.cons domainTree .nil))
      deriveList (.piFormation context domain.native codomain.native)
        (.cons domainTree (.cons (carrierFormation codomain (.snoc context domain.native) extended) .nil))

def telescopeFormation (parameters : List (Carrier language)) :
    Derivation (signature language headers) (.context (telescope parameters)) :=
  match parameters with
  | [] => emptyContext
  | parameter :: parameters =>
      let previous := telescopeFormation parameters
      deriveList (.contextExtend (telescope parameters) parameter.native)
        (.cons previous (.cons (carrierFormation parameter (telescope parameters) previous) .nil))

theorem emptyContext_before (bound : Nat) :
    (emptyContext (language := language) (headers := headers)).before bound := by
  apply deriveList_before
  · trivial
  · trivial

theorem carrierFormation_before (carrier : Carrier language) {n : Nat}
    (context : ContextExpr (symbols language headers) n)
    (formed : Derivation (signature language headers) (.context context))
    (bound : Nat) (positive : 0 < bound) (contextBefore : formed.before bound) :
    (carrierFormation carrier context formed).before bound := by
  induction carrier generalizing n with
  | sort position =>
      apply deriveList_before
      · exact ⟨(formed.before_judgment contextBefore),
          (Carrier.sort position).native_before n bound positive⟩
      · exact ⟨contextBefore, emptyContext_before bound,
          deriveList_before _ _ bound
            ⟨formed.before_judgment contextBefore, True.intro, fun position => Fin.elim0 position⟩
            ⟨contextBefore, True.intro⟩, True.intro⟩
  | function domain codomain domainIH codomainIH =>
      have domainBefore := domainIH context formed contextBefore
      have extendedBefore :
          (deriveList (.contextExtend context domain.native)
            (.cons formed (.cons (carrierFormation domain context formed) .nil))).before bound := by
        apply deriveList_before
        · exact ⟨(formed.before_judgment contextBefore), domain.native_before n bound positive⟩
        · exact ⟨contextBefore, domainBefore, True.intro⟩
      apply deriveList_before
      · exact ⟨(formed.before_judgment contextBefore),
          (Carrier.function domain codomain).native_before n bound positive⟩
      · exact ⟨domainBefore, codomainIH _ _ extendedBefore, True.intro⟩

theorem telescopeFormation_before (parameters : List (Carrier language))
    (bound : Nat) (positive : 0 < bound) :
    (telescopeFormation (headers := headers) parameters).before bound := by
  induction parameters with
  | nil => exact emptyContext_before bound
  | cons parameter parameters ih =>
      apply deriveList_before
      · change _ ∧ _
        exact ⟨telescope_before parameters bound positive, parameter.native_before _ bound positive⟩
      · exact ⟨ih, carrierFormation_before _ _ _ bound positive ih, True.intro⟩

/-- Header formation is constructed from generated rules, rather than a
global semantic model or a supplied formation predicate. -/
def headerFormation (language : LanguageDef) (headers : List (Header language)) :
    HeaderFormation (signature language headers) where
  typeHeader _ := emptyContext
  typeHeader_before _ := emptyContext_before 0
  termHeader position := telescopeFormation headers[position].parameters
  termHeader_before position := telescopeFormation_before _ 1 (by decide)
  termResult position := carrierFormation (.sort headers[position].result)
    (telescope headers[position].parameters) (telescopeFormation headers[position].parameters)
  termResult_before position := carrierFormation_before _ _ _ 1 (by decide)
    (telescopeFormation_before _ 1 (by decide))
  predicateHeader symbol := nomatch symbol
  predicateHeader_before symbol := nomatch symbol

end Mettapedia.OSLF.NativeTypes.Generation.NativeSignature
