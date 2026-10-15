import Mettapedia.Languages.MM0.Translation.FirstOrderCertificates
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Presentation
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SortedFirstOrderAuthoring

/-!
# Origin-sensitive modules compiled to MM0 declarations

Module entries carry the existing syntax declarations and typed rule rows.
A defined constructor is one entry: its declaration together with the row
that defines it, compiled to one MM0 definition. Origins and exposed names
survive compilation. A shared ancestor is retained once; conflicting entries
are checked before notation and formal names can be erased by the MM0
backend.

An ambient admitted presentation supplies the ordered inventory of the
assembled module. Numeric references in a separately compiled fragment move
by named lookup into that inventory. Constructor and axiom relocation are
proved against the actual compiled declarations, not an abstract table map.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.FirstOrderModules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.DefinitionalEquations
open Kernel FirstOrderSyntax FirstOrderTyping FirstOrderConversion FirstOrderRules

deriving instance DecidableEq for Definition.Body

instance (rows : List Row) (label : String) : Decidable (Primitive rows label) :=
  decidable_of_iff _ (checkPrimitive_iff rows label)

/-- Admit the shared quotation, including its independent visibility layer. -/
def admitQuotation? (source : ModuleAlgebra.SortedFirstOrderAuthoring.QuotedInferenceTheory) :
    Option Presentation :=
  if ModuleAlgebra.UpstreamTheoryQuotation.exportsValid
      (ModuleAlgebra.SortedFirstOrderAuthoring.core source) then
    Presentation.admit? source.toLanguageDef
      (ModuleAlgebra.SortedFirstOrderAuthoring.judgmentSorts source)
      (ModuleAlgebra.SortedFirstOrderAuthoring.rules source)
  else none

theorem admitQuotation?_retains
    {source : ModuleAlgebra.SortedFirstOrderAuthoring.QuotedInferenceTheory} {admitted : Presentation}
    (accepted : admitQuotation? source = some admitted) :
    admitted.syntaxSignature.language = source.toLanguageDef ∧
      admitted.judgmentSorts = ModuleAlgebra.SortedFirstOrderAuthoring.judgmentSorts source ∧
      admitted.rules = ModuleAlgebra.SortedFirstOrderAuthoring.rules source := by
  unfold admitQuotation? at accepted
  split at accepted
  · exact Presentation.admit?_retains accepted
  · contradiction

inductive Declaration where
  | sort (row : TypeDecl) (judgment : Bool)
  | constructor (row : GrammarRule)
  | definition (declared : GrammarRule) (row : Row)
  | axiom (row : Rule)
  deriving DecidableEq

def Declaration.exposedName : Declaration → String
  | .sort row _ => row.name
  | .constructor row => row.label
  | .definition declared _ => declared.label
  | .axiom row => row.row.id

/-- The backend payload is an actual MM0 declaration at an explicit index. -/
inductive Payload where
  | sort (row : SortInfo)
  | constructor (row : TermDecl)
  | definition (row : TermDecl) (body : Definition.Body)
  | axiom (row : TheoremDecl)
  deriving DecidableEq

/-- Move the constructor references of a body; its dummy sorts move too. -/
def relocateBody? (sorts terms : Nat → Option Nat) (body : Definition.Body) :
    Option Definition.Body := do
  let dummies ← body.dummies.mapM sorts
  let expression ← body.expression.relocateTerms? terms
  pure ⟨dummies, expression⟩

/-- Relocation operates on the actual MM0 declarations, including their
contexts and statement expressions, and changes their global table positions. -/
def relocateEntry? (sorts terms rules : Nat → Option Nat) (entry : Nat × Payload) :
    Option (Nat × Payload) :=
  match entry.2 with
  | .sort row => do
      let index ← sorts entry.1
      pure (index, .sort row)
  | .constructor row => do
      let index ← terms entry.1
      let image ← row.relocate? sorts
      pure (index, .constructor image)
  | .definition row body => do
      let index ← terms entry.1
      let image ← row.relocate? sorts
      let bodyImage ← relocateBody? sorts terms body
      pure (index, .definition image bodyImage)
  | .axiom row => do
      let index ← rules entry.1
      let image ← row.relocate? sorts terms
      pure (index, .axiom image)

/-- A constructor entry is a primitive constructor of the ambient
presentation; a definition entry is a defined constructor with its row. -/
def Supported (ambient : Presentation) : Declaration → Prop
  | .sort row judgment => List.Mem row ambient.syntaxSignature.language.types ∧
      judgment = decide (row.name ∈ ambient.judgmentSorts)
  | .constructor row => row ∈ ambient.syntaxSignature.language.terms ∧
      Primitive ambient.rows row.label
  | .definition declared row => declared ∈ ambient.syntaxSignature.language.terms ∧
      row ∈ ambient.rows ∧ row.head = declared.label
  | .axiom row => row ∈ ambient.rules

instance (ambient : Presentation) (row : Declaration) : Decidable (Supported ambient row) := by
  cases row with
  | sort row judgment =>
      letI : Decidable (List.Mem row ambient.syntaxSignature.language.types) :=
        decidable_of_iff (ambient.syntaxSignature.language.types.contains row = true)
          (List.contains_iff_mem : ambient.syntaxSignature.language.types.contains row = true ↔
            List.Mem row ambient.syntaxSignature.language.types)
      change Decidable (List.Mem row ambient.syntaxSignature.language.types ∧
        judgment = decide (row.name ∈ ambient.judgmentSorts))
      infer_instance
  | constructor row =>
      change Decidable (row ∈ ambient.syntaxSignature.language.terms ∧
        Primitive ambient.rows row.label)
      infer_instance
  | definition declared row =>
      change Decidable (declared ∈ ambient.syntaxSignature.language.terms ∧
        row ∈ ambient.rows ∧ row.head = declared.label)
      infer_instance
  | «axiom» row => change Decidable (row ∈ ambient.rules); infer_instance

/-- Unsupported rows refuse; supported rows keep their position in the joined inventory. -/
def compile? (ambient : Presentation) (row : Declaration) : Option (Nat × Payload) :=
  if Supported ambient row then
    match row with
    | .sort row _ => do
        let index ← index? ambient.syntaxSignature.sorts row.name
        pure (index, .sort (ambient.sortInfo row.name))
    | .constructor row => do
        let index ← index? ambient.syntaxSignature.names row.label
        let declaration ← declaration? ambient.syntaxSignature.sorts row
        pure (index, .constructor declaration)
    | .definition declared _ => do
        let index ← index? ambient.syntaxSignature.names declared.label
        let declaration ← declaration? ambient.syntaxSignature.sorts declared
        let body ← body? ambient.syntaxSignature.names ambient.rows declared
        pure (index, .definition declaration body)
    | .axiom row => do
        let index ← index? (ambient.rules.map (fun row => row.row.id)) row.row.id
        let declaration ← rule? ambient.syntaxSignature row
        pure (index, .axiom declaration)
  else none

/-- The body of a supported definition entry is the encoding of its row. -/
theorem body?_of_supported {ambient : Presentation} {declared : GrammarRule} {row : Row}
    (member : row ∈ ambient.rows) (head : row.head = declared.label) :
    ∃ expression, body? ambient.syntaxSignature.names ambient.rows declared =
        some ⟨[], expression⟩ ∧
      Encodes ambient.syntaxSignature.names (numbered row.formals row.body) expression := by
  obtain ⟨index, declaration, expression, compiled⟩ :=
    compiled_exists ambient.definitionalRows member
  have located : ambient.rows.find? (fun other => other.head == declared.label) = some row := by
    rw [← head]
    exact find?_of_distinct_heads ambient.definitionalRows.acyclic.distinctHeads member
  exact ⟨expression, by simp [body?, located, compiled.encoded.eval], compiled.encoded⟩

theorem compile?_total {ambient : Presentation} {row : Declaration}
    (supported : Supported ambient row) : ∃ payload, compile? ambient row = some payload := by
  cases row with
  | sort row judgment =>
      have member : row.name ∈ ambient.syntaxSignature.sorts := List.mem_map_of_mem supported.1
      exact ⟨(ambient.syntaxSignature.sorts.idxOf row.name, .sort (ambient.sortInfo row.name)), by
        simp [compile?, supported, index?_some _ _ member]⟩
  | constructor row =>
      have member : row.label ∈ ambient.syntaxSignature.names := List.mem_map_of_mem supported.1
      obtain ⟨declaration, compiled⟩ := ambient.syntaxSignature.ordinaryConstructors row supported.1
      change declaration? ambient.syntaxSignature.sorts row = some declaration at compiled
      exact ⟨(ambient.syntaxSignature.names.idxOf row.label, .constructor declaration), by
        simp [compile?, supported, index?_some _ _ member, compiled]⟩
  | definition declared row =>
      have member : declared.label ∈ ambient.syntaxSignature.names :=
        List.mem_map_of_mem supported.1
      obtain ⟨declaration, compiled⟩ :=
        ambient.syntaxSignature.ordinaryConstructors declared supported.1
      change declaration? ambient.syntaxSignature.sorts declared = some declaration at compiled
      obtain ⟨expression, bodyFound, -⟩ := body?_of_supported supported.2.1 supported.2.2
      exact ⟨(ambient.syntaxSignature.names.idxOf declared.label,
          .definition declaration ⟨[], expression⟩), by
        simp [compile?, supported, index?_some _ _ member, compiled, bodyFound]⟩
  | «axiom» row =>
      have member : row.row.id ∈ ambient.rules.map (fun row => row.row.id) :=
        List.mem_map_of_mem supported
      obtain ⟨declaration, compiled⟩ := ambient.rule_compiles supported
      exact ⟨((ambient.rules.map (fun row => row.row.id)).idxOf row.row.id, .axiom declaration), by
        simp [compile?, supported, index?_some _ _ member,
          (rule?_eq_some_iff _ _ _).mpr compiled]⟩

def InTheory (theory : Theory) (entry : Nat × Payload) : Prop :=
  match entry.2 with
  | .sort row => theory.sortSignature entry.1 = some row
  | .constructor row => theory.termSignature entry.1 = some row
  | .definition row body => theory.termSignature entry.1 = some row ∧
      theory.definitionSignature entry.1 = some body
  | .axiom row => theory.theoremSignature entry.1 = some row

/-- Every emitted payload is the declaration at that index in the generated theory. -/
theorem compile?_sound {ambient : Presentation} {row : Declaration} {entry : Nat × Payload}
    (compiled : compile? ambient row = some entry) : InTheory ambient.theory entry := by
  unfold compile? at compiled
  split at compiled
  next supported =>
    cases row with
    | sort row judgment =>
        cases found : index? ambient.syntaxSignature.sorts row.name with
        | none => simp [found] at compiled
        | some index =>
            have same : (index, Payload.sort (ambient.sortInfo row.name)) = entry := by
              simpa [found] using compiled
            subst entry
            simp [InTheory, ambient.theory_sortSignature, getElem?_index? found]
    | constructor row =>
        cases found : index? ambient.syntaxSignature.names row.label with
        | none => simp [found] at compiled
        | some index =>
            cases result : declaration? ambient.syntaxSignature.sorts row with
            | none => simp [found, result] at compiled
            | some declaration =>
                have same : (index, Payload.constructor declaration) = entry := by
                  simpa [found, result] using compiled
                subst entry
                change ambient.theory.termSignature index = some declaration
                rw [ambient.theory_termSignature, ambient.syntaxSignature.lookup supported.1 found]
                exact result
    | definition declared row =>
        cases found : index? ambient.syntaxSignature.names declared.label with
        | none => simp [found] at compiled
        | some index =>
            cases result : declaration? ambient.syntaxSignature.sorts declared with
            | none => simp [found, result] at compiled
            | some declaration =>
                cases bodyFound : body? ambient.syntaxSignature.names ambient.rows declared with
                | none => simp [found, result, bodyFound] at compiled
                | some body =>
                    have same : (index, Payload.definition declaration body) = entry := by
                      simpa [found, result, bodyFound] using compiled
                    subst entry
                    have position := getElem?_named ambient.syntaxSignature.language.terms
                      GrammarRule.label ambient.syntaxSignature.distinctConstructors supported.1 found
                    refine ⟨?_, ?_⟩
                    · change ambient.theory.termSignature index = some declaration
                      rw [ambient.theory_termSignature,
                        ambient.syntaxSignature.lookup supported.1 found]
                      exact result
                    · change ambient.theory.definitionSignature index = some body
                      rw [ambient.theory_definitionSignature]
                      simp [definitionSignature, position, bodyFound]
    | «axiom» row =>
        cases found : index? (ambient.rules.map (fun row => row.row.id)) row.row.id with
        | none => simp [found] at compiled
        | some index =>
            cases result : rule? ambient.syntaxSignature row with
            | none => simp [found, result] at compiled
            | some declaration =>
                have same : (index, Payload.axiom declaration) = entry := by
                  simpa [found, result] using compiled
                subst entry
                exact ambient.rule_lookup supported found ((rule?_eq_some_iff _ _ _).mp result)
  next unsupported => simp at compiled

/-- Compiling a retained declaration on either side of an inventory change
commutes with explicit sort, constructor and rule relocation. -/
theorem compile?_relocate {originalSource joinedSource : Presentation} {row : Declaration}
    (localSupport : Supported originalSource row) (joinedSupport : Supported joinedSource row)
    {original image : Nat × Payload}
    (before : compile? originalSource row = some original)
    (after : compile? joinedSource row = some image) :
    relocateEntry? (references? originalSource.syntaxSignature.sorts joinedSource.syntaxSignature.sorts)
      (references? originalSource.syntaxSignature.names joinedSource.syntaxSignature.names)
      (references? (originalSource.rules.map (fun row => row.row.id))
        (joinedSource.rules.map (fun row => row.row.id))) original = some image := by
  cases row with
  | sort row judgment =>
      simp only [compile?, if_pos localSupport, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at before
      simp only [compile?, if_pos joinedSupport, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at after
      obtain ⟨oldIndex, oldName, oldShape⟩ := before
      obtain ⟨newIndex, newName, newShape⟩ := after
      have flags : originalSource.sortInfo row.name = joinedSource.sortInfo row.name := by
        simp only [Presentation.sortInfo]
        rw [← localSupport.2, ← joinedSupport.2]
      subst original
      subst image
      simp [relocateEntry?, references?_of_name oldName newName, flags]
  | constructor row =>
      simp only [compile?, if_pos localSupport, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at before
      simp only [compile?, if_pos joinedSupport, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at after
      obtain ⟨oldIndex, oldName, oldDeclaration, oldTerms, oldShape⟩ := before
      obtain ⟨newIndex, newName, newDeclaration, newTerms, newShape⟩ := after
      subst original
      subst image
      simp [relocateEntry?, references?_of_name oldName newName,
        declaration?_relocate oldTerms newTerms]
  | definition declared row =>
      obtain ⟨oldExpression, oldBodyFound, oldEncoded⟩ :=
        body?_of_supported localSupport.2.1 localSupport.2.2
      obtain ⟨newExpression, newBodyFound, newEncoded⟩ :=
        body?_of_supported joinedSupport.2.1 joinedSupport.2.2
      simp only [compile?, if_pos localSupport, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq, oldBodyFound] at before
      simp only [compile?, if_pos joinedSupport, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq, newBodyFound] at after
      obtain ⟨oldIndex, oldName, oldDeclaration, oldTerms, oldBody, rfl, oldShape⟩ := before
      obtain ⟨newIndex, newName, newDeclaration, newTerms, newBody, rfl, newShape⟩ := after
      subst original
      subst image
      simp [relocateEntry?, relocateBody?, references?_of_name oldName newName,
        declaration?_relocate oldTerms newTerms, oldEncoded.relocate newEncoded]
  | «axiom» row =>
      simp only [compile?, if_pos localSupport, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at before
      simp only [compile?, if_pos joinedSupport, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at after
      obtain ⟨oldIndex, oldName, oldDeclaration, oldTerms, oldShape⟩ := before
      obtain ⟨newIndex, newName, newDeclaration, newTerms, newShape⟩ := after
      subst original
      subst image
      simp [relocateEntry?, references?_of_name oldName newName,
        ((rule?_eq_some_iff _ _ _).mp oldTerms).relocate
          ((rule?_eq_some_iff _ _ _).mp newTerms)]

abbrev Module (Origin : Type) [DecidableEq Origin] :=
  ModuleAlgebra.Presentation Origin String Declaration

abbrev CompiledModule (Origin : Type) [DecidableEq Origin] :=
  ModuleAlgebra.Presentation Origin String (Option (Nat × Payload))

def SupportedModule {Origin : Type} [DecidableEq Origin]
    (ambient : Presentation) (source : Module Origin) : Prop :=
  ∀ entry ∈ source.val, Supported ambient entry.body ∧ entry.label = entry.body.exposedName

instance {Origin : Type} [DecidableEq Origin] (ambient : Presentation) (source : Module Origin) :
    Decidable (SupportedModule ambient source) := by unfold SupportedModule; infer_instance

def compileModule? {Origin : Type} [DecidableEq Origin] (ambient : Presentation)
    (source : Module Origin) : Option (CompiledModule Origin) :=
  if SupportedModule ambient source then some (ModuleAlgebra.mapBodies (compile? ambient) source)
  else none

def relocateModule {Origin : Type} [DecidableEq Origin]
    (originalSource joinedSource : Presentation) (source : CompiledModule Origin) : CompiledModule Origin :=
  ModuleAlgebra.mapBodies (fun entry => entry.bind
    (relocateEntry? (references? originalSource.syntaxSignature.sorts joinedSource.syntaxSignature.sorts)
      (references? originalSource.syntaxSignature.names joinedSource.syntaxSignature.names)
      (references? (originalSource.rules.map (fun row => row.row.id))
        (joinedSource.rules.map (fun row => row.row.id))))) source

theorem relocate_compiled_module {Origin : Type} [DecidableEq Origin]
    {originalSource joinedSource : Presentation} {source : Module Origin}
    (localSupport : SupportedModule originalSource source)
    (joinedSupport : SupportedModule joinedSource source) :
    relocateModule originalSource joinedSource
      (ModuleAlgebra.mapBodies (compile? originalSource) source) =
      ModuleAlgebra.mapBodies (compile? joinedSource) source := by
  unfold relocateModule
  rw [ModuleAlgebra.mapBodies_comp]
  apply ModuleAlgebra.mapBodies_congr
  intro entry member
  obtain ⟨original, before⟩ := compile?_total (localSupport entry member).1
  obtain ⟨image, after⟩ := compile?_total (joinedSupport entry member).1
  simp only [Function.comp_apply, before, after, Option.bind_some]
  exact compile?_relocate (localSupport entry member).1 (joinedSupport entry member).1 before after

theorem compileModule?_of_supported {Origin : Type} [DecidableEq Origin]
    {ambient : Presentation} {source : Module Origin} (supported : SupportedModule ambient source) :
    compileModule? ambient source = some (ModuleAlgebra.mapBodies (compile? ambient) source) := by
  simp [compileModule?, supported]

theorem SupportedModule.join {Origin : Type} [DecidableEq Origin]
    {ambient : Presentation} {left right joined : Module Origin}
    (first : SupportedModule ambient left) (second : SupportedModule ambient right)
    (assembled : ModuleAlgebra.join left right = some joined) : SupportedModule ambient joined := by
  intro entry member
  rw [← ModuleAlgebra.join_eq_some_iff.mp assembled] at member
  rcases Finset.mem_union.mp member with member | member
  · exact first entry member
  · exact second entry member

/-- Compiling the checked source join agrees with joining its compiled fragments. -/
theorem compile_join {Origin : Type} [DecidableEq Origin]
    {ambient : Presentation} {left right joined : Module Origin}
    (first : SupportedModule ambient left) (second : SupportedModule ambient right)
    (assembled : ModuleAlgebra.join left right = some joined) :
    (compileModule? ambient left).bind (fun a =>
      (compileModule? ambient right).bind (ModuleAlgebra.join a)) = compileModule? ambient joined := by
  rw [compileModule?_of_supported first, compileModule?_of_supported second,
    compileModule?_of_supported (first.join second assembled)]
  exact ModuleAlgebra.mapBodies_join_of_success (compile? ambient) assembled

/-- Separate compilation and compatible assembly commute up to the actual
numeric reference maps into the admitted joined inventory. Origins survive. -/
theorem compile_join_relocated {Origin : Type} [DecidableEq Origin]
    {leftSource rightSource joinedSource : Presentation} {left right joined : Module Origin}
    (leftLocal : SupportedModule leftSource left) (rightLocal : SupportedModule rightSource right)
    (leftJoined : SupportedModule joinedSource left) (rightJoined : SupportedModule joinedSource right)
    (assembled : ModuleAlgebra.join left right = some joined) :
    ModuleAlgebra.join
      (relocateModule leftSource joinedSource (ModuleAlgebra.mapBodies (compile? leftSource) left))
      (relocateModule rightSource joinedSource (ModuleAlgebra.mapBodies (compile? rightSource) right)) =
      some (ModuleAlgebra.mapBodies (compile? joinedSource) joined) := by
  rw [relocate_compiled_module leftLocal leftJoined,
    relocate_compiled_module rightLocal rightJoined]
  exact ModuleAlgebra.mapBodies_join_of_success _ assembled

theorem compiled_origins {Origin : Type} [DecidableEq Origin]
    (ambient : Presentation) (source : Module Origin) :
    ModuleAlgebra.origins (ModuleAlgebra.mapBodies (compile? ambient) source).val =
      ModuleAlgebra.origins source.val := ModuleAlgebra.origins_mapBodies _ _

end Mettapedia.Languages.MM0.Translation.FirstOrderModules
