import Mettapedia.GSLT.LanguageDef.ModuleSource.ReplacementTransport
import Mettapedia.GSLT.LanguageDef.ModuleSource.ReplacementTypingControls
import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceAdmission

/-!
# Whole-pattern replacement controls and a text-authored execution consumer

The generic transport theorem is instantiated from the actual replacement
producer. Nested terms and open binder bodies use that theorem. The separate
authored module exercises inference and execution after a heterogeneous
argument permutation. These controls do not license binary collection packing
or identify raw declaration typing with full core-lowering adequacy.
-/

set_option autoImplicit false
open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
#module_file "../../../../../../metta/gslt/module/NamedReplacementControl.module"

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.ReplacementTransportControls

open Mettapedia.OSLF.MeTTaIL Syntax WellSorted ReplacementTransport

def row : Replacement := ⟨"K", ReplacementTypingControls.reordered⟩
def result : Value := (replaceRow ReplacementTypingControls.value row).toOption.getD ReplacementTypingControls.value
def source : LanguageDef := flattenRaw "Source" ReplacementTypingControls.value
def target : LanguageDef := flattenRaw "Target" result
def mapper (arguments : List Pattern) : List Pattern :=
  [arguments[1]?.getD (.fvar "y"), arguments[0]?.getD (.fvar "x")]
def renamed : Pattern → Pattern := renameConstructor "K" "L" mapper

theorem accepted : replaceRow ReplacementTypingControls.value row = .ok result := by rfl
theorem source_coherent : TermLabelsCoherent ReplacementTypingControls.value :=
  (checkTermLabelsCoherent_iff _).mp (by decide +kernel)
theorem source_valid : ModuleAlgebra.Valid ReplacementTypingControls.value.entries.toFinset := by decide +kernel

private theorem selected_original {rule : GrammarRule} (member : rule ∈ source.terms)
    (label : rule.label = "K") : rule = ReplacementTypingControls.original := by
  change rule ∈ [ReplacementTypingControls.atom "A0" "A", ReplacementTypingControls.atom "B0" "B", ReplacementTypingControls.original] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · simp [ReplacementTypingControls.atom] at label
  · simp [ReplacementTypingControls.atom] at label
  · rfl

/-- This instance obtains its whole signature comparison from replaceRow,
rather than supplying the preservation conclusion as a certificate. -/
theorem all_patterns_typed {free : FreeTypeContext} {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr} (original : HasType source free bound pattern type) :
    HasType target free bound (renamed pattern) type := by
  obtain ⟨old, map, oldLabel, computed, checked, signature⟩ :=
    signature_of_replaceRow ReplacementTypingControls.value row accepted source_coherent source_valid "Source" "Target"
  have oldEq : old = ReplacementTypingControls.original := selected_original signature.selected oldLabel
  subst old
  have actual : argumentMap ReplacementTypingControls.original ReplacementTypingControls.reordered = some mapper := rfl
  change argumentMap ReplacementTypingControls.original ReplacementTypingControls.reordered = some map at computed
  rw [actual] at computed
  cases Option.some.inj computed
  exact typed signature checked (by decide +kernel) rfl bound original

def nested : Pattern := .apply "K" [.apply "K" [.apply "A0" [], .apply "B0" []], .apply "B0" []]
def underBinder : Pattern := .lambda none (.apply "K" [.bvar 0, .apply "B0" []])

theorem nested_source_typed : HasType source FreeTypeContext.empty [] nested ReplacementTypingControls.a :=
  checkHasType_sound (by decide +kernel)

theorem nested_target_typed :
    HasType target FreeTypeContext.empty []
      (.apply "L" [.apply "B0" [], .apply "L" [.apply "B0" [], .apply "A0" []]]) ReplacementTypingControls.a := by
  simpa [renamed, nested, mapper, renameConstructor] using
    all_patterns_typed nested_source_typed

theorem binder_source_typed : HasType source FreeTypeContext.empty [] underBinder (.arrow ReplacementTypingControls.a ReplacementTypingControls.a) :=
  checkHasType_sound (by decide +kernel)

theorem binder_target_typed :
    HasType target FreeTypeContext.empty [] (.lambda none (.apply "L" [.apply "B0" [], .bvar 0])) (.arrow ReplacementTypingControls.a ReplacementTypingControls.a) := by
  simpa [renamed, underBinder, mapper, renameConstructor] using
    all_patterns_typed binder_source_typed

theorem wrong_order_refused :
    checkHasType target FreeTypeContext.empty [] (.apply "L" [.apply "A0" [], .apply "B0" []]) ReplacementTypingControls.a = false := by
  decide +kernel

def badLabels : Value :=
  { ReplacementTypingControls.value with entries := ReplacementTypingControls.value.entries.map fun item =>
      if item.label = (.term, "K") then { item with label := (.term, "Wrong") } else item }

theorem bad_label_check_refused : checkTermLabelsCoherent badLabels = false := by decide +kernel

def authored : LanguageDef := NamedReplacementControl.language.toOption.getD (LanguageDef.empty "")
def language : LanguageDef := (authored.toCore.toOption.map (·.language)).getD (LanguageDef.empty "")

#guard NamedReplacementControl.language.isOk
#guard authored.toCore.isOk
#guard language.terms.any (fun rule => rule.label == "L" && rule.params.map paramName == ["y", "x"])
#guard !language.terms.any (fun rule => rule.label == "K")
#guard language.rewrites.map (fun rule => (rule.left, rule.right)) ==
  [(.apply "L" [.fvar "y", .fvar "x"], .fvar "x")]

def plan : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile ⟨language, [], ⟨[], [], []⟩⟩
    { sites := .all, includeDerivedEquations := false }

#guard CollectionOccurrenceAdmission.check plan

end Mettapedia.GSLT.LanguageDef.ModuleSource.ReplacementTransportControls
