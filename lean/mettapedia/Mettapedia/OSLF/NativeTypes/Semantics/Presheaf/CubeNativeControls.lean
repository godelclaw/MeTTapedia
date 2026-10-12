import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeExtension
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeKindSearch

/-!
# Native cube formation and serialized-certificate controls

A change of input sort rejects a previously valid formation. A change of
output sort changes the witnessed result. The full native checker also rejects
the original serialized certificate after the input rule changes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeControls

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open CubeEnrichment CubeNativeDeclarations CubeNativeKindEncoding CubeNativeKindSearch
open Mettapedia.OSLF.NativeTypes.Certificates

abbrev language : CubeEnrichment.Signature where
  Carrier := Bool
  Former := Bool
  arity declaration := if declaration then 1 else 0
  input _ _ := false
  output declaration := declaration

instance : DecidableEq language.Carrier := inferInstanceAs (DecidableEq Bool)
instance : DecidableEq language.Former := inferInstanceAs (DecidableEq Bool)
instance : Encodable language.Carrier := inferInstanceAs (Encodable Bool)
instance : Encodable language.Former := inferInstanceAs (Encodable Bool)

def boxSlots : Vertex language := fun _ _ => .box

def starInput : Vertex language := fun declaration position =>
  if position.val < language.arity declaration then .star else .box

def starOutput : Vertex language := fun declaration position =>
  if position.val = language.arity declaration then .star else .box

def argument : PureCode (D := language) false := .sort .star

def application : PureCode (D := language) true := .former true (fun _ => argument)

def emptyFormer : PureCode (D := language) false := @CubeEnrichment.Code.former language (fun _ => Empty) false (fun position => Fin.elim0 position)

/-- Whole-family soundness and completeness precede these controls. -/
theorem changed_input_rejects :
    ¬ Nonempty (Kinded starInput application .box) := by
  rw [← CubeEnrichment.inferKind_exact]
  decide

theorem original_input_accepts : Nonempty (Kinded boxSlots application .box) :=
  CubeEnrichment.inferKind_sound (by decide)

theorem changed_output_accepts : Nonempty (Kinded starOutput application .star) :=
  CubeEnrichment.inferKind_sound (by decide)

theorem changed_output_rejects_old_kind :
    ¬ Nonempty (Kinded starOutput application .box) := by
  rw [← CubeEnrichment.inferKind_exact]
  decide

theorem generated_headers_change :
    (signature boxSlots).termParameters (.formation true) ≠
      (signature starInput).termParameters (.formation true) := by decide

theorem generated_results_change :
    (signature boxSlots).termResult (.formation true) ≠
      (signature starOutput).termResult (.formation true) := by decide

/-- An operational value remains a distinct generator, with no implicit kind. -/
theorem operational_not_a_sort (value : Nat) :
    (CubeEnrichment.Code.operational value : CubeEnrichment.Code language (fun _ => Nat) false) ≠ .sort .star :=
  CubeEnrichment.Code.operational_ne_sort (signature := language) (operational := fun _ => Nat) (carrier := false) value .star

theorem operational_not_implicitly_kinded (value : Nat) :
    ¬ Nonempty (Kinded boxSlots
      (CubeEnrichment.Code.operational value : CubeEnrichment.Code language (fun _ => Nat) false) .box) :=
  CubeEnrichment.no_operational_kind (operational := fun _ => Nat) (carrier := false) boxSlots value .box

def emitted := nativeFormation? boxSlots application .box

def output : TermExpr (symbols language) 0 × Refinement.Certificate (signature boxSlots) :=
  emitted.get (by decide)

def outputJudgment : Judgment (symbols language) :=
  .term .nil output.1 (typingType true (encode application) (sortCode true .box 0))

/-- Every node's exact raw payload is encoded and decoded before the changed
signature checks it. Child occurrences retain their original order. -/
def recode : Refinement.Certificate (signature boxSlots) →
    Option (Refinement.Certificate (signature starInput))
  | .node rule children =>
      match (NativeWire.rule (NativeEnumeration.symbolCodecs (S := symbols language)) (signature starInput)).get
          ((NativeWire.rule (NativeEnumeration.symbolCodecs (S := symbols language)) (signature boxSlots)).put rule) with
      | none => none
      | some changed =>
          if same : (RuleCode.premises changed).length = (RuleCode.premises rule).length then
            (collect (fun position : Fin (RuleCode.premises changed).length =>
              recode (children ⟨position.val, by rw [← same]; exact position.isLt⟩))).map
              (fun decoded => .node changed decoded)
          else none

def changedCertificate : Option (Refinement.Certificate (signature starInput)) := recode output.2

#guard emitted.isSome
#guard Refinement.check output.2 outputJudgment
#guard !(nativeFormation? starInput application .box).isSome
#guard (nativeFormation? starOutput application .star).isSome
#guard !(nativeFormation? starOutput application .box).isSome
#guard (nativeFormation? boxSlots emptyFormer .box).isSome
#guard (nativeFormation? starOutput emptyFormer .star).isSome
#guard !(nativeFormation? boxSlots (CubeEnrichment.Code.sort .box : PureCode (D := language) false) .box).isSome
#guard changedCertificate.isSome
#guard match changedCertificate with
  | none => false
  | some certificate => !(Refinement.check certificate outputJudgment)
#guard (CubeNativeDeclarations.search boxSlots outputJudgment 0).found.isNone

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeControls
