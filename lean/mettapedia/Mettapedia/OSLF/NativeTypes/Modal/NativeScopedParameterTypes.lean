import Mettapedia.OSLF.NativeTypes.Modal.NativeEventParameters
import Mettapedia.OSLF.NativeTypes.Generation.NativeHeaderFormation
import Mettapedia.OSLF.NativeTypes.Certificates.RefinementChecking

/-!
# Generated native types for scoped event parameters

An ordered dependency context becomes a native function telescope over the
original authored sort alphabet. Its raw type is computed from the same scoped
slot metadata consumed by independent operational assignment typing. Native
formation certificates are derived uniformly in arbitrary native contexts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeScopedParameterTypes

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open NativeEventParameters

variable {plan : Plan} {schema : Rules.Schema plan}

def functionCarrier {language : LanguageDef} (dependencies : List (Generation.NativeSignature.Carrier language))
    (result : Generation.NativeSignature.Carrier language) : Generation.NativeSignature.Carrier language :=
  dependencies.reverse.foldr Generation.NativeSignature.Carrier.function result

theorem functionCarrier_source {language : LanguageDef}
    (dependencies : List (Generation.NativeSignature.Carrier language)) (result : Generation.NativeSignature.Carrier language) :
    (functionCarrier dependencies result).source =
      (dependencies.map Generation.NativeSignature.Carrier.source).reverse.foldr TypeExpr.arrow result.source := by
  have sourceFold : ∀ domains : List (Generation.NativeSignature.Carrier language),
      (domains.foldr Generation.NativeSignature.Carrier.function result).source =
        (domains.map Generation.NativeSignature.Carrier.source).foldr TypeExpr.arrow result.source := by
    intro domains
    induction domains with
    | nil => rfl
    | cons domain domains ih =>
        change TypeExpr.arrow domain.source (domains.foldr Generation.NativeSignature.Carrier.function result).source = _
        rw [ih]
        rfl
  unfold functionCarrier
  rw [sourceFold, List.map_reverse]

def authoredType (slot : Slot schema) : TypeExpr :=
  slot.dependencies.reverse.foldr TypeExpr.arrow slot.expected

def decodeSlot? (slot : Slot schema) : Option (Generation.NativeSignature.Carrier plan.snapshot.language) := do
  let dependencies ← Generation.NativeSignature.decodeList (Generation.NativeSignature.decodeType? plan.snapshot.language) slot.dependencies
  let result ← Generation.NativeSignature.decodeType? plan.snapshot.language slot.expected
  pure (functionCarrier dependencies result)

private theorem decoded_sources {language : LanguageDef} {types : List TypeExpr}
    {carriers : List (Generation.NativeSignature.Carrier language)}
    (decoded : Generation.NativeSignature.decodeList (Generation.NativeSignature.decodeType? language) types = some carriers) :
    carriers.map Generation.NativeSignature.Carrier.source = types := by
  have each := Generation.NativeSignature.decodeList_sound decoded
  clear decoded
  induction each with
  | nil => rfl
  | cons first _ ih =>
      simp only [List.map_cons, Generation.NativeSignature.decodeType?_sound first, ih]

theorem decodeSlot?_sound {slot : Slot schema} {carrier : Generation.NativeSignature.Carrier plan.snapshot.language}
    (decoded : decodeSlot? slot = some carrier) : carrier.source = authoredType slot := by
  cases dependencies : Generation.NativeSignature.decodeList (Generation.NativeSignature.decodeType? plan.snapshot.language) slot.dependencies with
  | none => simp [decodeSlot?, dependencies] at decoded
  | some domains =>
      cases result : Generation.NativeSignature.decodeType? plan.snapshot.language slot.expected with
      | none => simp [decodeSlot?, dependencies, result] at decoded
      | some codomain =>
          simp [decodeSlot?, dependencies, result] at decoded
          cases decoded
          have declared : domains.map Generation.NativeSignature.Carrier.source = slot.dependencies := decoded_sources dependencies
          rw [functionCarrier_source, declared, Generation.NativeSignature.decodeType?_sound result]
          rfl

/-- Admission states authored type formation, independently of the decoder. -/
def Admitted (slot : Slot schema) : Prop :=
  (∀ dependency ∈ slot.dependencies, Generation.NativeSignature.AdmittedType plan.snapshot.language dependency) ∧
    Generation.NativeSignature.AdmittedType plan.snapshot.language slot.expected

theorem decodeSlot?_complete {slot : Slot schema} (admitted : Admitted slot) :
    ∃ carrier, decodeSlot? slot = some carrier := by
  obtain ⟨domains, dependencies⟩ := Generation.NativeSignature.decodeList_exists
    (fun dependency member => Generation.NativeSignature.decodeType?_complete (admitted.1 dependency member))
  obtain ⟨codomain, result⟩ := Generation.NativeSignature.decodeType?_complete admitted.2
  exact ⟨functionCarrier domains codomain,
    by simp [decodeSlot?, dependencies, result]⟩

structure Installed (slot : Slot schema) where
  carrier : Generation.NativeSignature.Carrier plan.snapshot.language
  decoded : decodeSlot? slot = some carrier

def install? (slot : Slot schema) : Option (Installed slot) :=
  match decoded : decodeSlot? slot with
  | none => none
  | some carrier => some ⟨carrier, decoded⟩

/-- The formation tree is constructed by the same full native rule checker
that checks authored constructor types. -/
def Installed.formation {headers : List (Generation.NativeSignature.Header plan.snapshot.language)}
    {slot : Slot schema} (installed : Installed slot) {n : Nat}
    (context : ContextExpr (Generation.NativeSignature.symbols plan.snapshot.language headers) n)
    (formed : Derivation (Generation.NativeSignature.signature plan.snapshot.language headers) (.context context)) :
    Derivation (Generation.NativeSignature.signature plan.snapshot.language headers) (.type context installed.carrier.native) :=
  Generation.NativeSignature.carrierFormation installed.carrier context formed

def Installed.certificate {headers : List (Generation.NativeSignature.Header plan.snapshot.language)}
    {slot : Slot schema} (installed : Installed slot) {n : Nat}
    (context : ContextExpr (Generation.NativeSignature.symbols plan.snapshot.language headers) n)
    (formed : Derivation (Generation.NativeSignature.signature plan.snapshot.language headers) (.context context)) :=
  Mettapedia.OSLF.NativeTypes.Certificates.Refinement.erase (installed.formation context formed)

theorem Installed.certificate_checked {headers : List (Generation.NativeSignature.Header plan.snapshot.language)}
    {slot : Slot schema} (installed : Installed slot) {n : Nat}
    (context : ContextExpr (Generation.NativeSignature.symbols plan.snapshot.language headers) n)
    (formed : Derivation (Generation.NativeSignature.signature plan.snapshot.language headers) (.context context)) :
    Mettapedia.OSLF.NativeTypes.Certificates.Refinement.check (installed.certificate context formed)
      (.type context installed.carrier.native) = true :=
  Mettapedia.OSLF.NativeTypes.Certificates.Refinement.check_erase _

theorem Installed.authored_contract {slot : Slot schema} (installed : Installed slot) :
    installed.carrier.source = authoredType slot := decodeSlot?_sound installed.decoded

end Mettapedia.OSLF.NativeTypes.Modal.NativeScopedParameterTypes
