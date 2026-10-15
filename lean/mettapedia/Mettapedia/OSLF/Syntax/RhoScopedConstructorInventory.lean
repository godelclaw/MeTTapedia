import Mettapedia.OSLF.Syntax.RhoScopedInstanceReadout
import Mettapedia.OSLF.Syntax.RhoScopedParallelInventory
import Mettapedia.OSLF.Syntax.RhoFiniteQuotationOrigins

/-!
# Complete scoped constructor arguments in finite process inventories

Canonical input patterns retain their entire continuation under the name
binder. Input and output argument readouts are injective on the source equation
classes. Consequently an actual finite parallel inventory contains only
finitely many such argument pairs, including open and reflective bodies.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedConstructorInventory

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoIntrinsicReadback RhoIntrinsicCanonicalBag RhoScopedParallelInventory
open RhoSchema.IntrinsicEncoding RhoCanonicalNamePairs
open MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

abbrev Input (context : Ctx sig) := Name context × Process (Srt.nm :: context)
abbrev Output (context : Ctx sig) := Name context × Process context

def inputPattern {context : Ctx sig} (arguments : Input context) : Pattern :=
  .apply "PInput" [encodeEquationClass arguments.1,
    .lambda none (encodeEquationClass arguments.2)]

def outputPattern {context : Ctx sig} (arguments : Output context) : Pattern :=
  .apply "POutput" [encodeEquationClass arguments.1, encodeEquationClass arguments.2]

def dropPattern {context : Ctx sig} (name : Name context) : Pattern :=
  .apply "PDrop" [encodeEquationClass name]

theorem encode_output {context : Ctx sig} (name : Name context) (payload : Process context) :
    encodeEquationClass (outputClass name payload) = outputPattern (name, payload) := by
  induction name using Quotient.inductionOn with
  | _ name =>
    induction payload using Quotient.inductionOn with
    | _ payload =>
      change canonicalize (.apply "POutput" [encodeTerm name, encodeTerm payload]) = _
      rw [canonicalize_apply_general "POutput" _ (by simp)]
      rfl

theorem encode_input {context : Ctx sig} (name : Name context)
    (body : Process (Srt.nm :: context)) :
    encodeEquationClass (inputClass name body) = inputPattern (name, body) := by
  induction name using Quotient.inductionOn with
  | _ name =>
    induction body using Quotient.inductionOn with
    | _ body =>
      change canonicalize (.apply "PInput" [encodeTerm name, .lambda none (encodeTerm body)]) = _
      rw [canonicalize_apply_general "PInput" _ (by simp)]
      rfl

theorem inputPattern_injective (context : Ctx sig) :
    Function.Injective (inputPattern (context := context)) := by
  rintro ⟨name, body⟩ ⟨name', body'⟩ same
  have arguments := Pattern.apply.inj same
  have names : encodeEquationClass name = encodeEquationClass name' := by
    exact (List.cons.inj arguments.2).1
  have bodies : encodeEquationClass body = encodeEquationClass body' := by
    have tail := (List.cons.inj arguments.2).2
    exact Pattern.lambda.inj (List.cons.inj tail).1 |>.2
  exact Prod.ext (canonical_encoding_injective context Srt.nm names)
    (canonical_encoding_injective (Srt.nm :: context) Srt.pr bodies)

theorem outputPattern_injective (context : Ctx sig) :
    Function.Injective (outputPattern (context := context)) := by
  rintro ⟨name, body⟩ ⟨name', body'⟩ same
  have arguments := Pattern.apply.inj same
  exact Prod.ext (canonical_encoding_injective context Srt.nm
      (List.cons.inj arguments.2).1)
    (canonical_encoding_injective context Srt.pr
      (List.cons.inj (List.cons.inj arguments.2).2).1)

theorem dropPattern_injective (context : Ctx sig) :
    Function.Injective (dropPattern (context := context)) := by
  intro name name' same
  exact canonical_encoding_injective context Srt.nm
    (List.cons.inj (Pattern.apply.inj same).2).1

theorem output_components {context : Ctx sig} (name : Name context) (payload : Process context) :
    components (outputClass name payload) = {outputPattern (name, payload)} := by
  rw [components_bagContents, encode_output]
  rfl

theorem input_components {context : Ctx sig} (name : Name context)
    (body : Process (Srt.nm :: context)) :
    components (inputClass name body) = {inputPattern (name, body)} := by
  rw [components_bagContents, encode_input]
  rfl

def patternSet {context : Ctx sig} (whole : Process context) : Set Pattern :=
  {pattern | pattern ∈ components whole}

theorem patternSet_finite {context : Ctx sig} (whole : Process context) :
    (patternSet whole).Finite := by
  classical
  have same : patternSet whole = ((components whole).toFinset : Set Pattern) := by
    ext pattern
    simp [patternSet]
  rw [same]
  exact (components whole).toFinset.finite_toSet

def inputs {context : Ctx sig} (whole : Process context) : Set (Input context) :=
  inputPattern ⁻¹' patternSet whole

def outputs {context : Ctx sig} (whole : Process context) : Set (Output context) :=
  outputPattern ⁻¹' patternSet whole

def drops {context : Ctx sig} (whole : Process context) : Set (Name context) :=
  dropPattern ⁻¹' patternSet whole

theorem inputs_finite {context : Ctx sig} (whole : Process context) : (inputs whole).Finite :=
  Set.Finite.preimage (inputPattern_injective context).injOn (patternSet_finite whole)

theorem outputs_finite {context : Ctx sig} (whole : Process context) : (outputs whole).Finite :=
  Set.Finite.preimage (outputPattern_injective context).injOn (patternSet_finite whole)

theorem drops_finite {context : Ctx sig} (whole : Process context) : (drops whole).Finite :=
  Set.Finite.preimage (dropPattern_injective context).injOn (patternSet_finite whole)

/-- Component inclusion follows from the actual typed inventory comparison. -/
theorem components_le {context : Ctx sig} {part whole : Process context}
    (included : read part ≤ read whole) : components part ≤ components whole := by
  rw [← values_read, ← values_read]
  exact Multiset.map_le_map included

end Mettapedia.OSLF.Binding.RhoScopedConstructorInventory
