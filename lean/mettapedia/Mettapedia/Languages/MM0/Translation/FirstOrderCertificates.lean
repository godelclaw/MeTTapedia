import Mettapedia.Languages.MM0.Translation.FirstOrderRules
import Mettapedia.GSLT.LanguageDef.SortedFirstOrderCertificates
import Mettapedia.GSLT.LanguageDef.SortedFirstOrderConversionCertificates

/-!
# Translating named, open inference certificates to MM0

A source certificate cites a local assumption, applies a named rule, or
converts the conclusion of its child to a named term. Local assumption
references retain their occurrence positions; rule references are resolved
against the actual ordered source inventory. Arguments use the existing term
translation and children retain their order. A conversion node compiles to
an MM0 conversion whose evidence is computed from the two terms and ends by
stating its target. The result is an ordinary MM0 `ProofWitness`, checked by
the existing kernel.

`checksModulo_iff_compiled` is the exact correspondence for certificates
with conversion steps. The library's `RawOpenProof`, which has none, is the
special case `checks_iff_compiled`; it holds for every presentation, with or
without definitions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.FirstOrderCertificates

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.GSLT.LanguageDef.DefinitionalEquations
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderConversion
open Kernel FirstOrderSyntax FirstOrderTyping FirstOrderConversion FirstOrderRules

mutual
  def compile? (presentation : Presentation) : RawOpenProof → Option ProofWitness
    | .premise index => some (.hyp index)
    | .node invocation children => do
        let index ← index? (presentation.rules.map (fun rule => rule.row.id)) invocation.ruleId.value
        let arguments ← encodeList presentation.syntaxSignature.names invocation.arguments
        let children' ← compileChildren? presentation children
        pure (.theoremApp index arguments children')
  termination_by proof => sizeOf proof

  def compileChildren? (presentation : Presentation) : List RawOpenProof → Option (List ProofWitness)
    | [] => some []
    | child :: children => do
        let first ← compile? presentation child
        let rest ← compileChildren? presentation children
        pure (first :: rest)
  termination_by children => sizeOf children
end

mutual
  /-- Relocate an ordinary definition-free certificate. Local hypotheses retain
  their occurrence positions; global constructor and rule references are mapped
  independently. Conversion nodes are outside this canonical certificate image. -/
  def relocate? (terms rules : Nat → Option Nat) : ProofWitness → Option ProofWitness
    | .hyp index => some (.hyp index)
    | .theoremApp index arguments children => do
        let index' ← rules index
        let arguments' ← arguments.mapM (Preterm.relocateTerms? terms)
        let children' ← relocateChildren? terms rules children
        pure (.theoremApp index' arguments' children')
    | .conversion _ _ => none
  termination_by witness => sizeOf witness

  def relocateChildren? (terms rules : Nat → Option Nat) :
      List ProofWitness → Option (List ProofWitness)
    | [] => some []
    | witness :: witnesses => do
        let first ← relocate? terms rules witness
        let rest ← relocateChildren? terms rules witnesses
        pure (first :: rest)
  termination_by witnesses => sizeOf witnesses
end

theorem compile_node_eq_some_iff (presentation : Presentation)
    (invocation : InferenceChecker.RuleInstance) (children : List RawOpenProof) (witness : ProofWitness) :
    compile? presentation (.node invocation children) = some witness ↔
    ∃ index arguments witnesses,
      index? (presentation.rules.map (fun rule => rule.row.id)) invocation.ruleId.value = some index ∧
      encodeList presentation.syntaxSignature.names invocation.arguments = some arguments ∧
      compileChildren? presentation children = some witnesses ∧
      witness = .theoremApp index arguments witnesses := by
  simp only [compile?, bind, pure, Option.bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨index, found, arguments, encoded, witnesses, childrenCompiled, same⟩
    exact ⟨index, arguments, witnesses, found, encoded, childrenCompiled, same.symm⟩
  · rintro ⟨index, arguments, witnesses, found, encoded, childrenCompiled, same⟩
    exact ⟨index, found, arguments, encoded, witnesses, childrenCompiled, same.symm⟩

theorem compileChildren_cons_eq_some_iff (presentation : Presentation)
    (head : RawOpenProof) (tail : List RawOpenProof) (witnesses : List ProofWitness) :
    compileChildren? presentation (head :: tail) = some witnesses ↔
      ∃ first rest, compile? presentation head = some first ∧
        compileChildren? presentation tail = some rest ∧ witnesses = first :: rest := by
  simp only [compileChildren?, bind, pure, Option.bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨first, compiled, rest, restCompiled, same⟩
    exact ⟨first, rest, compiled, restCompiled, same.symm⟩
  · rintro ⟨first, rest, compiled, restCompiled, same⟩
    exact ⟨first, compiled, rest, restCompiled, same.symm⟩

mutual
  /-- Separate compilation followed by a join agrees with actual certificate
  relocation. This theorem does not assume the old numeric inventories agree. -/
  theorem compile_relocate {originalSource joinedSource : Presentation}
      {proof : RawOpenProof} {original image : ProofWitness}
      (before : compile? originalSource proof = some original)
      (after : compile? joinedSource proof = some image) :
      relocate? (references? originalSource.syntaxSignature.names joinedSource.syntaxSignature.names)
        (references? (originalSource.rules.map (fun row => row.row.id))
          (joinedSource.rules.map (fun row => row.row.id))) original = some image := by
    cases proof with
    | premise index =>
        have originalShape : ProofWitness.hyp index = original := by simpa [compile?] using before
        have imageShape : ProofWitness.hyp index = image := by simpa [compile?] using after
        subst original
        subst image
        simp [relocate?]
    | node invocation children =>
        obtain ⟨oldIndex, oldArguments, oldChildren, oldName, oldTerms, oldTail, oldShape⟩ :=
          (compile_node_eq_some_iff _ _ _ _).mp before
        obtain ⟨newIndex, newArguments, newChildren, newName, newTerms, newTail, newShape⟩ :=
          (compile_node_eq_some_iff _ _ _ _).mp after
        subst original
        subst image
        simp [relocate?, references?_of_name oldName newName,
          encodesList_relocate_eval (encodeList_sound oldTerms) (encodeList_sound newTerms),
          compileChildren_relocate oldTail newTail]
  termination_by sizeOf proof

  theorem compileChildren_relocate {originalSource joinedSource : Presentation}
      {proofs : List RawOpenProof} {original image : List ProofWitness}
      (before : compileChildren? originalSource proofs = some original)
      (after : compileChildren? joinedSource proofs = some image) :
      relocateChildren? (references? originalSource.syntaxSignature.names joinedSource.syntaxSignature.names)
        (references? (originalSource.rules.map (fun row => row.row.id))
          (joinedSource.rules.map (fun row => row.row.id))) original = some image := by
    cases proofs with
    | nil =>
        have originalShape : ([] : List ProofWitness) = original := by simpa [compileChildren?] using before
        have imageShape : ([] : List ProofWitness) = image := by simpa [compileChildren?] using after
        subst original
        subst image
        simp [relocateChildren?]
    | cons proof proofs =>
        obtain ⟨oldFirst, oldTail, oldHead, oldRest, oldShape⟩ :=
          (compileChildren_cons_eq_some_iff _ _ _ _).mp before
        obtain ⟨newFirst, newTail, newHead, newRest, newShape⟩ :=
          (compileChildren_cons_eq_some_iff _ _ _ _).mp after
        subst original
        subst image
        simp [relocateChildren?, compile_relocate oldHead newHead,
          compileChildren_relocate oldRest newRest]
  termination_by sizeOf proofs
end

theorem encodesList_lookup_left {names : List String} {patterns : List Pattern}
    {expressions : List Preterm} (encoded : List.Forall₂ (Encodes names) patterns expressions)
    {index : Nat} {pattern : Pattern} (lookup : patterns[index]? = some pattern) :
    ∃ expression, expressions[index]? = some expression ∧ Encodes names pattern expression := by
  induction encoded generalizing index with
  | nil => simp at lookup
  | cons first rest ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
          subst pattern
          exact ⟨_, rfl, first⟩
      | succ index =>
          exact ih (by simpa only [List.getElem?_cons_succ] using lookup)

theorem encodesList_lookup_right {names : List String} {patterns : List Pattern}
    {expressions : List Preterm} (encoded : List.Forall₂ (Encodes names) patterns expressions)
    {index : Nat} {expression : Preterm} (lookup : expressions[index]? = some expression) :
    ∃ pattern, patterns[index]? = some pattern ∧ Encodes names pattern expression := by
  induction encoded generalizing index with
  | nil => simp at lookup
  | cons first rest ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
          subst expression
          exact ⟨_, rfl, first⟩
      | succ index =>
          exact ih (by simpa only [List.getElem?_cons_succ] using lookup)

/-! ## Certificates with conversion steps -/

mutual
  /-- Compile a certificate modulo the definitions. A conversion node reads
  the conclusion of its child off the child's root, computes the conversion
  evidence between the two terms, and states the target. -/
  def compileModulo? (presentation : Presentation) (hypotheses : List Pattern) :
      ModuloProof → Option ProofWitness
    | .premise index => some (.hyp index)
    | .node invocation children => do
        let index ← index? (presentation.rules.map (fun rule => rule.row.id)) invocation.ruleId.value
        let arguments ← encodeList presentation.syntaxSignature.names invocation.arguments
        let children' ← compileModuloChildren? presentation hypotheses children
        pure (.theoremApp index arguments children')
    | .convert target child => do
        let source ← conclusion? presentation.rules hypotheses child
        let evidence ← conversionWitness? presentation.syntaxSignature.names presentation.rows
          source target
        let stated ← encode presentation.syntaxSignature.names target
        let child' ← compileModulo? presentation hypotheses child
        pure (.conversion (.trans evidence (.refl stated)) child')
  termination_by proof => sizeOf proof

  def compileModuloChildren? (presentation : Presentation) (hypotheses : List Pattern) :
      List ModuloProof → Option (List ProofWitness)
    | [] => some []
    | child :: children => do
        let first ← compileModulo? presentation hypotheses child
        let rest ← compileModuloChildren? presentation hypotheses children
        pure (first :: rest)
  termination_by children => sizeOf children
end

mutual
  /-- On a certificate without conversion steps, the two compilers agree. -/
  theorem compileModulo?_ofRaw (presentation : Presentation) (hypotheses : List Pattern)
      (proof : RawOpenProof) :
      compileModulo? presentation hypotheses (ModuloProof.ofRaw proof) =
        compile? presentation proof := by
    cases proof with
    | premise index => simp only [ModuloProof.ofRaw, compileModulo?, compile?]
    | node invocation children =>
      simp only [ModuloProof.ofRaw, compileModulo?, compile?,
        compileModuloChildren?_ofRawList presentation hypotheses children]
  termination_by sizeOf proof

  theorem compileModuloChildren?_ofRawList (presentation : Presentation)
      (hypotheses : List Pattern) (proofs : List RawOpenProof) :
      compileModuloChildren? presentation hypotheses (ModuloProof.ofRawList proofs) =
        compileChildren? presentation proofs := by
    cases proofs with
    | nil => simp only [ModuloProof.ofRawList, compileModuloChildren?, compileChildren?]
    | cons proof proofs =>
      simp only [ModuloProof.ofRawList, compileModuloChildren?, compileChildren?,
        compileModulo?_ofRaw presentation hypotheses proof,
        compileModuloChildren?_ofRawList presentation hypotheses proofs]
  termination_by sizeOf proofs
end

/-- Every accepted source tree compiles to a checked MM0 tree with the same
ordered nodes, and each conversion step to an accepted MM0 conversion. -/
theorem compileModulo_preserves {presentation : Presentation} {bound : List TypeExpr}
    {context : Context} {hypotheses : List Pattern} {targetHypotheses : List Preterm}
    (contexts : ContextEncodes presentation.syntaxSignature.sorts bound context)
    (localScope : List.Forall₂ (Encodes presentation.syntaxSignature.names) hypotheses targetHypotheses)
    {proof : ModuloProof} {pattern : Pattern}
    (checked : ChecksModulo presentation.rows presentation.syntaxSignature.language
      presentation.rules bound hypotheses proof pattern) :
    ∃ witness expression, compileModulo? presentation hypotheses proof = some witness ∧
      Encodes presentation.syntaxSignature.names pattern expression ∧
      ProofWitness.Checks presentation.syntaxSignature.termSignature
        (definitionSignature presentation.syntaxSignature presentation.rows)
        presentation.theory.theoremSignature context targetHypotheses witness expression := by
  induction checked using ChecksModulo.rec
      (motive_2 := fun proofs patterns _ =>
        ∃ witnesses expressions,
          compileModuloChildren? presentation hypotheses proofs = some witnesses ∧
          List.Forall₂ (Encodes presentation.syntaxSignature.names) patterns expressions ∧
          ProofWitness.ChecksList presentation.syntaxSignature.termSignature
            (definitionSignature presentation.syntaxSignature presentation.rows)
            presentation.theory.theoremSignature context targetHypotheses witnesses expressions) with
  | premise lookup =>
      obtain ⟨expression, targetLookup, encoded⟩ := encodesList_lookup_left localScope lookup
      exact ⟨_, expression, by simp [compileModulo?], encoded, .hyp targetLookup⟩
  | @rule invocation rule children found arity typed fragments _ ih =>
      have sourceLookup := SortedFirstOrderRules.lookupRule?_member found
      have formed := presentation.formedRules rule sourceLookup.1
      obtain ⟨declaration, compiled⟩ := presentation.rule_compiles sourceLookup.1
      obtain ⟨arguments, argumentsEncoded⟩ := typed_source_vector typed compiled.contexts fragments
      have admitted := (vector_admissibility_iff argumentsEncoded contexts compiled.contexts).mp typed
      have declared := presentation.compiled_admitted compiled formed
      obtain ⟨instantiation, instantiated⟩ := declared.instantiates admitted
      have instanceEncoding := compiled.instance_encodes formed argumentsEncoded arity instantiated
      obtain ⟨witnesses, expressions, childrenCompiled, childrenEncoded, childrenChecked⟩ := ih
      have sameExpressions : expressions = instantiation.hypotheses := by
        exact Option.some.inj ((encodesList_eval childrenEncoded).symm.trans
          (encodesList_eval instanceEncoding.1))
      subst expressions
      have nameMember : rule.row.id ∈ presentation.rules.map (fun rule => rule.row.id) :=
        List.mem_map_of_mem sourceLookup.1
      have indexFound := index?_some _ _ nameMember
      have targetLookup := presentation.rule_lookup sourceLookup.1 indexFound compiled
      have wireFound : index? (presentation.rules.map (fun rule => rule.row.id)) invocation.ruleId.value =
          some ((presentation.rules.map (fun rule => rule.row.id)).idxOf rule.row.id) := by
        rw [← sourceLookup.2]
        exact indexFound
      refine ⟨.theoremApp _ arguments witnesses, _, ?_, instanceEncoding.2,
        .theoremApp targetLookup instantiated childrenChecked⟩
      simp [compileModulo?, wireFound, encodesList_eval argumentsEncoded, childrenCompiled]
  | @convert target source child type childChecked same sourceFragment targetFragment
      sourceTyped targetTyped ih =>
      obtain ⟨witness, sourceExpression, compiled, sourceEncoded, targetChild⟩ := ih
      obtain ⟨sort, sortEncoding⟩ := source_sort_exists contexts sourceTyped sourceFragment
      obtain ⟨targetExpression, targetEncoded⟩ :=
        typed_source_image targetTyped targetFragment sortEncoding
      obtain ⟨evidence, computed, evidenceChecked⟩ :=
        conversionWitness_checks presentation.definitionalRows contexts sourceTyped targetTyped
          sourceFragment targetFragment sortEncoding sourceEncoded targetEncoded same
      refine ⟨.conversion (.trans evidence (.refl targetExpression)) witness, targetExpression,
        ?_, targetEncoded,
        .conversion
          (.trans evidenceChecked
            (.refl (preserves_type targetEncoded contexts targetTyped sortEncoding)))
          targetChild⟩
      simp [compileModulo?, childChecked.conclusion, computed, targetEncoded.eval, compiled]
  | nil => exact ⟨[], [], by simp [compileModuloChildren?], .nil, .nil⟩
  | cons _ _ first rest =>
      obtain ⟨witness, expression, compiled, encoded, checked⟩ := first
      obtain ⟨witnesses, expressions, restCompiled, restEncoded, restChecked⟩ := rest
      exact ⟨witness :: witnesses, expression :: expressions,
        by simp [compileModuloChildren?, compiled, restCompiled], .cons encoded restEncoded,
        .cons checked restChecked⟩

mutual
  /-- Acceptance of a compiled tree reconstructs the same source tree, with
  typed arguments and typed conversion endpoints. -/
  theorem compileModulo_reflects {presentation : Presentation} {bound : List TypeExpr}
      {context : Context} {hypotheses : List Pattern} {targetHypotheses : List Preterm}
      (contexts : ContextEncodes presentation.syntaxSignature.sorts bound context)
      (localScope : List.Forall₂ (Encodes presentation.syntaxSignature.names) hypotheses targetHypotheses)
      {proof : ModuloProof} {witness : ProofWitness} {expression : Preterm}
      (compiled : compileModulo? presentation hypotheses proof = some witness)
      (checked : ProofWitness.Checks presentation.syntaxSignature.termSignature
        (definitionSignature presentation.syntaxSignature presentation.rows)
        presentation.theory.theoremSignature context targetHypotheses witness expression) :
      ∃ pattern, Encodes presentation.syntaxSignature.names pattern expression ∧
        ChecksModulo presentation.rows presentation.syntaxSignature.language presentation.rules
          bound hypotheses proof pattern := by
    cases proof with
    | premise index =>
        have same : ProofWitness.hyp index = witness := by simpa [compileModulo?] using compiled
        subst witness
        cases checked with
        | hyp lookup =>
            obtain ⟨pattern, sourceLookup, encoded⟩ := encodesList_lookup_right localScope lookup
            exact ⟨pattern, encoded, .premise sourceLookup⟩
    | node invocation children =>
        cases indexFound : index? (presentation.rules.map (fun rule => rule.row.id)) invocation.ruleId.value with
        | none => simp [compileModulo?, indexFound] at compiled
        | some index =>
            cases argumentsFound : encodeList presentation.syntaxSignature.names invocation.arguments with
            | none => simp [compileModulo?, indexFound, argumentsFound] at compiled
            | some arguments =>
                cases childrenFound : compileModuloChildren? presentation hypotheses children with
                | none => simp [compileModulo?, indexFound, argumentsFound, childrenFound] at compiled
                | some witnesses =>
                    have same : ProofWitness.theoremApp index arguments witnesses = witness := by
                      simpa [compileModulo?, indexFound, argumentsFound, childrenFound] using compiled
                    subst witness
                    cases checked with
                    | @theoremApp _ declaration _ _ instantiation lookup instantiated childrenChecked =>
                        obtain ⟨rule, sourceLookup, declarationCompiled⟩ := Presentation.rule_of_lookup lookup
                        have member := List.mem_of_getElem? sourceLookup
                        have formed := presentation.formedRules rule member
                        have nameFound := getElem?_index? indexFound
                        have nameFromRule :
                            (presentation.rules.map (fun rule => rule.row.id))[index]? = some rule.row.id := by
                          simp only [List.getElem?_map, sourceLookup, Option.map_some]
                        have sameName : rule.row.id = invocation.ruleId.value :=
                          Option.some.inj (nameFromRule.symm.trans nameFound)
                        have rawLookup : SortedFirstOrderRules.lookupRule? presentation.rules
                            invocation.ruleId.value = some rule := by
                          rw [← sameName]
                          exact SortedFirstOrderRules.lookupRule?_of_member presentation.distinctRules member
                        have argumentsEncoded := encodeList_sound argumentsFound
                        have arity : invocation.arguments.length = rule.row.vars.length :=
                          argumentsEncoded.length_eq.trans (instantiated.admissible.length_eq.trans
                            (declarationCompiled.contexts.length_eq.symm.trans formed.arity))
                        have typed := (vector_admissibility_iff argumentsEncoded contexts
                          declarationCompiled.contexts).mpr instantiated.admissible
                        have instances := declarationCompiled.instance_encodes formed argumentsEncoded arity instantiated
                        obtain ⟨patterns, patternsEncoded, sourceChildren⟩ :=
                          compileModuloChildren_reflects contexts localScope childrenFound childrenChecked
                        have samePatterns : patterns = rule.row.instPremises invocation.arguments := by
                          apply List.left_unique_forall₂' (R := Encodes presentation.syntaxSignature.names)
                            (fun _ _ _ left right => encoded_injective left right)
                            patternsEncoded instances.1
                        subst patterns
                        exact ⟨_, instances.2, .rule rawLookup arity typed
                          (by
                            intro argument argumentMember
                            obtain ⟨target, _, argumentEncoded⟩ :=
                              encodesList_left_member argumentsEncoded argumentMember
                            exact encoded_matchCorrect argumentEncoded)
                          sourceChildren⟩
    | convert target child =>
        cases conclusionFound : conclusion? presentation.rules hypotheses child with
        | none => simp [compileModulo?, conclusionFound] at compiled
        | some source =>
            cases evidenceFound : conversionWitness? presentation.syntaxSignature.names
                presentation.rows source target with
            | none => simp [compileModulo?, conclusionFound, evidenceFound] at compiled
            | some evidence =>
                cases statedFound : encode presentation.syntaxSignature.names target with
                | none =>
                    simp [compileModulo?, conclusionFound, statedFound] at compiled
                | some stated =>
                    cases childFound : compileModulo? presentation hypotheses child with
                    | none =>
                        simp [compileModulo?, conclusionFound, statedFound, childFound] at compiled
                    | some childWitness =>
                        have same : ProofWitness.conversion (.trans evidence (.refl stated))
                            childWitness = witness := by
                          simpa [compileModulo?, conclusionFound, evidenceFound, statedFound,
                            childFound] using compiled
                        subst witness
                        cases checked with
                        | conversion converted childChecked =>
                            obtain ⟨sourcePattern, sourceEncoded, sourceChecked⟩ :=
                              compileModulo_reflects contexts localScope childFound childChecked
                            cases converted with
                            | trans first second =>
                                cases second with
                                | refl statedTyped =>
                                    have targetEncoded := encode_sound statedFound
                                    have converts := first.derives
                                    obtain ⟨leftPattern, rightPattern, leftDecoded, rightDecoded,
                                        equivalent⟩ :=
                                      converts_reflected (base := fun _ _ _ => [])
                                        presentation.definitionalRows converts
                                    have sameLeft := encoded_injective leftDecoded sourceEncoded
                                    have sameRight := encoded_injective rightDecoded targetEncoded
                                    subst sameLeft
                                    subst sameRight
                                    obtain ⟨leftTyped, rightTyped⟩ := converts.typed
                                    obtain ⟨type, sortEncoding⟩ := target_type_exists contexts leftTyped
                                    exact ⟨_, targetEncoded,
                                      .convert sourceChecked
                                        ((presentation.definitionalRows.equationEquiv_iff _ _).mp
                                          equivalent)
                                        (encoded_matchCorrect sourceEncoded)
                                        (encoded_matchCorrect targetEncoded)
                                        (reflects_type sourceEncoded contexts leftTyped sortEncoding)
                                        (reflects_type targetEncoded contexts rightTyped sortEncoding)⟩
  termination_by sizeOf proof

  theorem compileModuloChildren_reflects {presentation : Presentation} {bound : List TypeExpr}
      {context : Context} {hypotheses : List Pattern} {targetHypotheses : List Preterm}
      (contexts : ContextEncodes presentation.syntaxSignature.sorts bound context)
      (localScope : List.Forall₂ (Encodes presentation.syntaxSignature.names) hypotheses targetHypotheses)
      {proofs : List ModuloProof} {witnesses : List ProofWitness} {expressions : List Preterm}
      (compiled : compileModuloChildren? presentation hypotheses proofs = some witnesses)
      (checked : ProofWitness.ChecksList presentation.syntaxSignature.termSignature
        (definitionSignature presentation.syntaxSignature presentation.rows)
        presentation.theory.theoremSignature context targetHypotheses witnesses expressions) :
      ∃ patterns, List.Forall₂ (Encodes presentation.syntaxSignature.names) patterns expressions ∧
        ChecksModuloList presentation.rows presentation.syntaxSignature.language presentation.rules
          bound hypotheses proofs patterns := by
    cases proofs with
    | nil =>
        have same : ([] : List ProofWitness) = witnesses := by
          simpa [compileModuloChildren?] using compiled
        subst witnesses
        cases checked
        exact ⟨[], .nil, .nil⟩
    | cons proof proofs =>
        cases first : compileModulo? presentation hypotheses proof with
        | none => simp [compileModuloChildren?, first] at compiled
        | some witness =>
            cases rest : compileModuloChildren? presentation hypotheses proofs with
            | none => simp [compileModuloChildren?, first, rest] at compiled
            | some tail =>
                have same : witness :: tail = witnesses := by
                  simpa [compileModuloChildren?, first, rest] using compiled
                subst witnesses
                cases checked with
                | cons head tail =>
                    obtain ⟨pattern, encoded, sourceChecked⟩ :=
                      compileModulo_reflects contexts localScope first head
                    obtain ⟨patterns, encodedTail, sourceTail⟩ :=
                      compileModuloChildren_reflects contexts localScope rest tail
                    exact ⟨pattern :: patterns, .cons encoded encodedTail, .cons sourceChecked sourceTail⟩
  termination_by sizeOf proofs
end

/-- **Certificates modulo the definitions are MM0 certificates.**
Translation preserves and reflects acceptance of the submitted certificate
itself, conversion steps included. -/
theorem checksModulo_iff_compiled {presentation : Presentation} {bound : List TypeExpr}
    {context : Context} {hypotheses : List Pattern} {targetHypotheses : List Preterm}
    {proof : ModuloProof} {pattern : Pattern} {expression : Preterm}
    (contexts : ContextEncodes presentation.syntaxSignature.sorts bound context)
    (localScope : List.Forall₂ (Encodes presentation.syntaxSignature.names) hypotheses targetHypotheses)
    (encoded : Encodes presentation.syntaxSignature.names pattern expression) :
    ChecksModulo presentation.rows presentation.syntaxSignature.language presentation.rules
      bound hypotheses proof pattern ↔
    ∃ witness, compileModulo? presentation hypotheses proof = some witness ∧
      ProofWitness.Checks presentation.theory.termSignature presentation.theory.definitionSignature
        presentation.theory.theoremSignature context targetHypotheses witness expression := by
  rw [presentation.theory_termSignature, presentation.theory_definitionSignature]
  constructor
  · intro checked
    obtain ⟨witness, target, compiled, targetEncoded, targetChecked⟩ :=
      compileModulo_preserves contexts localScope checked
    have same : target = expression := Option.some.inj (targetEncoded.eval.symm.trans encoded.eval)
    subst target
    exact ⟨witness, compiled, targetChecked⟩
  · rintro ⟨witness, compiled, checked⟩
    obtain ⟨source, sourceEncoded, sourceChecked⟩ :=
      compileModulo_reflects contexts localScope compiled checked
    have same := encoded_injective sourceEncoded encoded
    simpa only [same] using sourceChecked

/-- Translation preserves and reflects acceptance of a certificate without
conversion steps. This is the case of `checksModulo_iff_compiled` at the
library's `RawOpenProof`. -/
theorem checks_iff_compiled {presentation : Presentation} {bound : List TypeExpr} {context : Context}
    {hypotheses : List Pattern} {targetHypotheses : List Preterm} {proof : RawOpenProof}
    {pattern : Pattern} {expression : Preterm}
    (contexts : ContextEncodes presentation.syntaxSignature.sorts bound context)
    (localScope : List.Forall₂ (Encodes presentation.syntaxSignature.names) hypotheses targetHypotheses)
    (encoded : Encodes presentation.syntaxSignature.names pattern expression) :
    SortedFirstOrderRules.Checks presentation.syntaxSignature.language presentation.rules
      bound hypotheses proof pattern ↔
    ∃ witness, compile? presentation proof = some witness ∧
      ProofWitness.Checks presentation.theory.termSignature presentation.theory.definitionSignature
        presentation.theory.theoremSignature context targetHypotheses witness expression := by
  rw [← checksModulo_ofRaw_iff (rows := presentation.rows),
    checksModulo_iff_compiled contexts localScope encoded, compileModulo?_ofRaw]

def checkCompiled (presentation : Presentation) (context : Context) (hypotheses : List Preterm)
    (proof : RawOpenProof) (expression : Preterm) : Bool :=
  match compile? presentation proof with
  | none => false
  | some witness => ProofWitness.check presentation.theory.termSignature presentation.theory.definitionSignature
      presentation.theory.theoremSignature context hypotheses witness expression

theorem checkCompiled_iff {presentation : Presentation} {bound : List TypeExpr} {context : Context}
    {hypotheses : List Pattern} {targetHypotheses : List Preterm} {proof : RawOpenProof}
    {pattern : Pattern} {expression : Preterm}
    (contexts : ContextEncodes presentation.syntaxSignature.sorts bound context)
    (localScope : List.Forall₂ (Encodes presentation.syntaxSignature.names) hypotheses targetHypotheses)
    (encoded : Encodes presentation.syntaxSignature.names pattern expression) :
    checkCompiled presentation context targetHypotheses proof expression = true ↔
      SortedFirstOrderRules.proof? presentation.syntaxSignature.language presentation.rules
        bound hypotheses proof = some pattern := by
  rw [SortedFirstOrderRules.proof?_eq_some_iff, checks_iff_compiled contexts localScope encoded]
  cases compiled : compile? presentation proof with
  | none => simp [checkCompiled, compiled]
  | some witness => simp [checkCompiled, compiled, ProofWitness.check_iff]

/-- Compile a certificate with conversion steps and run the MM0 checker on
the result. -/
def checkCompiledModulo (presentation : Presentation) (hypotheses : List Pattern)
    (context : Context) (targetHypotheses : List Preterm) (proof : ModuloProof)
    (expression : Preterm) : Bool :=
  match compileModulo? presentation hypotheses proof with
  | none => false
  | some witness => ProofWitness.check presentation.theory.termSignature
      presentation.theory.definitionSignature presentation.theory.theoremSignature context
      targetHypotheses witness expression

/-- The MM0 checker accepts the compiled certificate exactly when the
source checker accepts the certificate. -/
theorem checkCompiledModulo_iff {presentation : Presentation} {bound : List TypeExpr}
    {context : Context} {hypotheses : List Pattern} {targetHypotheses : List Preterm}
    {proof : ModuloProof} {pattern : Pattern} {expression : Preterm}
    (contexts : ContextEncodes presentation.syntaxSignature.sorts bound context)
    (localScope : List.Forall₂ (Encodes presentation.syntaxSignature.names) hypotheses targetHypotheses)
    (encoded : Encodes presentation.syntaxSignature.names pattern expression) :
    checkCompiledModulo presentation hypotheses context targetHypotheses proof expression = true ↔
      proofModulo? presentation.rows presentation.syntaxSignature.language presentation.rules
        bound hypotheses proof = some pattern := by
  rw [proofModulo?_eq_some_iff, checksModulo_iff_compiled contexts localScope encoded]
  cases compiled : compileModulo? presentation hypotheses proof with
  | none => simp [checkCompiledModulo, compiled]
  | some witness => simp [checkCompiledModulo, compiled, ProofWitness.check_iff]

end Mettapedia.Languages.MM0.Translation.FirstOrderCertificates
