import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationCallPrograms
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionRootMap
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeJoins
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeRegularity
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorProgramChecking

/-!
# Completing and calling the recursive dependent append program

The body is the existing five-argument append program. Its retained typing
tree is re-encoded for the declaration prefix checker, which checks the whole
body before publishing its name. A call unfolds that selected body and checks
the five beta steps; the established nil/cons equations then apply in the
extended theory. No new recursive computation rule is postulated.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.AppendDefinitionCompletion

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration
open NativeNaturalVectorFamilies

local instance : DecidableRel Programs.rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred Programs.rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (Programs.rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel Programs.rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel Programs.rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def name : DeclName := `Completed.append
abbrev EntryCode := DeclarationAdmissionReplay.Certificate Tower.Head Programs.decoder.Code
abbrev PrefixRoot := DeclarationConversionCode.RootCode Programs.decoder.Code (fun _ => Empty)

/-- The data transformation retains the entire typing tree and changes only
the root-code address to its inherited position in the extended checker. -/
def bodyEvidence : StructuralTypingReplay.Code Tower.Head
    (StructuralConversionCode.Code Tower.Head PrefixRoot) 0 :=
  Programs.appendEvidence.term.mapConversion (fun code => code.mapRoot .inherited)

def certificate? : Option EntryCode :=
  match bodyEvidence with
  | .lamIntro level formation _ => some ⟨level, formation, some bodyEvidence⟩
  | _ => none

theorem certificate_present : certificate?.isSome = true := by decide +kernel

def certificate : EntryCode := certificate?.get certificate_present

def accepted : Bool := checkComplete Programs.rules Programs.decoder []
  (name, Programs.appendType) (name, Programs.appendTerm) certificate

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem accepted_true : accepted = true := by decide +kernel

def entries : List (DeclName × Entry Tower.Head) := [(name, ⟨Programs.appendType, some Programs.appendTerm⟩)]
def library := Signature.ofList entries
abbrev rules := extendRules Programs.rules library
local instance : DecidableRel rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))
def decoder : StructuralConversionCode.RootDecoder rules.computation :=
  DeclarationConversionCode.ofList Programs.rules Programs.decoder entries

theorem selected_entry : rules.constantType name = some Programs.appendType ∧
    library.valueOf? name = some Programs.appendTerm :=
  checkComplete_selected Programs.rules Programs.decoder accepted_true

def arguments {n : Nat} (element first second left right : Tower.Tm n) : Sub Tower.Head 5 n :=
  fun index => ![right, left, second, first, element] index

def call {n : Nat} (element first second left right : Tower.Tm n) : Tower.Tm n :=
  TelescopeAbstraction.applyClosed Programs.appendContext (arguments element first second left right) (.const name)

def callEvidence {n : Nat} (element first second left right : Tower.Tm n) :
    StructuralConversionCode.Code Tower.Head decoder.Code n :=
  callCode name Programs.appendContext (arguments element first second left right) Programs.appendBody

theorem call_checked {n : Nat} (element first second left right : Tower.Tm n) :
    (callEvidence element first second left right).check rules.headEq decoder.decode
      (call element first second left right) (Programs.append element first second left right) = true := by
  have checked := completed_call_checked Programs.rules Programs.decoder [] name Programs.appendContext
    Programs.appendBody Programs.appendResult certificate accepted_true (arguments element first second left right)
  have result : subst (arguments element first second left right) Programs.appendBody =
      Programs.append element first second left right := by
    simp [Programs.appendBody, Programs.Computation.append_substitute, subst, arguments]
  rw [result] at checked
  exact checked

theorem call_typed {n : Nat} (context : Tower.Ctx n)
    (element first second left right : Tower.Tm n)
    (typed : FormationSensitive.CtxMor rules Programs.appendContext context
      (arguments element first second left right)) :
    FormationSensitive.Typing rules context (call element first second left right)
      (vecApp element (Programs.add first second)) := by
  have judgment := completed_call_typed Programs.rules Programs.decoder [] name Programs.appendContext
    Programs.appendBody Programs.appendResult certificate accepted_true context
    (arguments element first second left right) typed
  have result : subst (arguments element first second left right) Programs.appendResult =
      vecApp element (Programs.add first second) := by
    simp [Programs.appendResult, subst_vecApp, Programs.Computation.add_substitute, subst, arguments]
  rw [result] at judgment
  exact judgment

theorem nil_equation {n : Nat} (element second right : Tower.Tm n) :
    Conv rules.headEq (call element zeroTm second (vnilApp element) right) right rules.computation := by
  have entry := StructuralConversionCode.Code.check_sound (headEq := rules.headEq) decoder
    (call_checked element zeroTm second (vnilApp element) right)
  exact Relation.EqvGen.trans _ _ _ entry
    (Declaration.Conv.includeSignature Programs.rules library (Programs.Computation.append_nil element second right))

theorem cons_equation {n : Nat} (element first second head tail right : Tower.Tm n) :
    Conv rules.headEq
      (call element (succApp first) second (vconsApp element first head tail) right)
      (vconsApp element (Programs.add first second) head (Programs.append element first second tail right))
      rules.computation := by
  have entry := StructuralConversionCode.Code.check_sound (headEq := rules.headEq) decoder
    (call_checked element (succApp first) second (vconsApp element first head tail) right)
  exact Relation.EqvGen.trans _ _ _ entry
    (Declaration.Conv.includeSignature Programs.rules library (Programs.Computation.append_cons element first second head tail right))

theorem selected_steps {n : Nat} (element first second left right : Tower.Tm n) :
    (callEvidence element first second left right).stepCount = 6 :=
  callCode_stepCount name Programs.appendContext _ Programs.appendBody

def replacement : Tower.Tm 0 := .app (.lam (.var 0)) Programs.appendTerm
def changedLibrary := Signature.ofList [(name, ⟨Programs.appendType, some replacement⟩)]
def changedDecoder : StructuralConversionCode.RootDecoder (extendRules Programs.rules changedLibrary).computation :=
  DeclarationConversionCode.ofList Programs.rules Programs.decoder [(name, ⟨Programs.appendType, some replacement⟩)]

theorem replacement_differs : replacement ≠ Programs.appendTerm := by
  intro same
  cases same

theorem replacement_typed :
    FormationSensitive.Typing Programs.rules .nil replacement Programs.appendType := by
  have universes : FormationSensitive.UniverseRegularity Programs.rules :=
    FormationSensitive.towerUniverseRegularity.includeSignature Programs.signature
  obtain ⟨u, isUniverse, formed⟩ := Programs.append_typed.typing.regularity universes .nil
  have context : FormationSensitive.ContextFormation Programs.rules
      (.snoc .nil Programs.appendType) := .snoc .nil formed isUniverse
  have identity : FormationSensitive.Typing Programs.rules .nil (.lam (.var 0))
      (.pi Programs.appendType (rename wk Programs.appendType)) := by
    exact FormationCheckedTelescopePrograms.close_typed universes
      FormationCheckedTelescopePrograms.tower_joins context (FormationSensitive.Typing.var 0)
  have applied := FormationSensitive.Typing.appElim identity Programs.append_typed.typing
  simpa only [replacement, inst0_rename_wk] using applied

theorem replacement_conversion :
    Conv Programs.rules.headEq replacement Programs.appendTerm Programs.rules.computation := by
  apply StructuralConversionCode.Code.check_sound Programs.decoder
    (code := .single (.betaPi (.var 0) Programs.appendTerm))
  simp [replacement, StructuralConversionCode.Code.check, StructuralConversionCode.Code.decode,
    StructuralConversionCode.StepCode.decode, inst0, subst, subst0]

def unfolding : StructuralConversionCode.Code Tower.Head decoder.Code 0 := .single (.root (.delta name))

/-- A previous refusal at a different endpoint is stale after the body
changes: the very same root request now succeeds at that endpoint. -/
theorem stale_negative_changes :
    unfolding.check rules.headEq decoder.decode (.const name) replacement = false ∧
      unfolding.check rules.headEq changedDecoder.decode (.const name) replacement = true := by
  constructor
  · simp [unfolding, decoder, DeclarationConversionCode.ofList, DeclarationConversionCode.rootDecoder,
      StructuralConversionCode.Code.check, StructuralConversionCode.Code.decode,
      StructuralConversionCode.StepCode.decode, DeclarationConversionCode.decode,
      entries, Signature.valueOf?, Signature.ofList, Signature.insert,
      TelescopeAbstraction.liftClosed_zero, Ne.symm replacement_differs]
  · simp [unfolding, changedDecoder, DeclarationConversionCode.ofList, DeclarationConversionCode.rootDecoder,
      StructuralConversionCode.Code.check, StructuralConversionCode.Code.decode,
      StructuralConversionCode.StepCode.decode, DeclarationConversionCode.decode,
      Signature.valueOf?, Signature.ofList, Signature.insert, TelescopeAbstraction.liftClosed_zero]

/-- The edit is beta-equivalent, yet the retained declaration-unfolding
receipt must be regenerated for its new exact intermediate body. -/
theorem stale_call_refused (element first second left right : Tower.Tm 0) :
    (callEvidence element first second left right).check Programs.rules.headEq changedDecoder.decode
      (call element first second left right) (Programs.append element first second left right) = false := by
  have refused := changed_body_refuses_call Programs.rules.headEq changedLibrary Programs.decoder.decode
    (StructuralConversionCode.RootDecoder.ofEmpty
      (Signature.ofList [(name, ⟨Programs.appendType, some replacement⟩)]).computation
      (Signature.computation_ofList _)).decode
    name Programs.appendContext (arguments element first second left right) Programs.appendBody replacement
    (by simp [changedLibrary, Signature.valueOf?, Signature.ofList, Signature.insert]) replacement_differs
  have result : subst (arguments element first second left right) Programs.appendBody =
      Programs.append element first second left right := by
    simp [Programs.appendBody, Programs.Computation.append_substitute, subst, arguments]
  rw [result] at refused
  exact refused

def verdicts : List (String × Bool) := [
  ("complete recursive append body", accepted),
  ("changed return index refuses old body evidence", !checkComplete Programs.rules Programs.decoder []
    (name, Programs.changedType) (name, Programs.appendTerm) certificate),
  ("changed body refuses old evidence", !checkComplete Programs.rules Programs.decoder []
    (name, Programs.appendType) (name, Programs.changedTerm) certificate)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

#print axioms accepted_true
#print axioms call_typed
#print axioms nil_equation
#print axioms cons_equation
#print axioms stale_call_refused
#print axioms replacement_typed
#print axioms replacement_conversion
#print axioms stale_negative_changes

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.AppendDefinitionCompletion
