import Mettapedia.Languages.MM0.Translation.CertificateSimulation
import Mettapedia.Languages.MM0.Kernel.DefinitionFreeConversion

/-!
# MM0 and a presentation without definitions are p-equivalent

`CertificateSimulation` turns a presentation's raw proof trees into MM0 witnesses. This
module goes back. For a presentation without equations, and so without definitions,
`decompile` reads an MM0 witness as a raw proof tree. A theorem application becomes the
rule at the same position with its arguments decoded, and a conversion step is dropped,
since without definitions every conversion relates an expression to itself.

If the MM0 kernel accepts a witness for the rendering of a sequent, the presentation
accepts the decompiled tree for the sequent itself (`decompile_accepted`). The tree is
no larger than the witness (`decompile_size`), and decompiling takes time polynomial in
the witness (`decompileTime_le`). So the presentation's checker p-simulates MM0 on these
sequents (`decompileSimulation`), and with `compileSimulation` the two checkers are
p-equivalent (`pEquivalent`).

The proof goes through compilation. Every argument the kernel accepts is well typed,
so it decodes and re-encodes to itself (`decode_of_hasType`). Distinct rule names
send each rule back to its own position. So compiling the decompiled tree gives the
witness with its conversion steps removed (`compile_decompile`), which the kernel
still accepts (`strip_checks`), and `checks_iff_compiled` transfers acceptance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.CertificateEquivalence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.GSLT.LanguageDef.ProofSystems
open Kernel FirstOrderSyntax FirstOrderTyping FirstOrderRules FirstOrderCertificates
open CertificateSimulation
open Polynomial

/-! ## Removing conversion steps -/

mutual

/-- The witness with its conversion steps removed. -/
def strip (witness : ProofWitness) : ProofWitness :=
  match witness with
  | .hyp index => .hyp index
  | .theoremApp index arguments children => .theoremApp index arguments (stripChildren children)
  | .conversion _ child => strip child
termination_by structural witness

def stripChildren (children : List ProofWitness) : List ProofWitness :=
  match children with
  | [] => []
  | child :: children => strip child :: stripChildren children
termination_by structural children

end

/-- Without definitions, a witness proves what it proved with its conversion steps
removed. -/
theorem strip_checks {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
    (noDefinitions : ∀ symbol, definitions symbol = none)
    {witness : ProofWitness} {expression : Preterm}
    (checked : ProofWitness.Checks signature definitions theorems context hypotheses witness expression) :
    ProofWitness.Checks signature definitions theorems context hypotheses (strip witness) expression := by
  induction checked using ProofWitness.Checks.rec
      (motive_2 := fun children expressions _ =>
        ProofWitness.ChecksList signature definitions theorems context hypotheses
          (stripChildren children) expressions) with
  | hyp lookup => exact .hyp lookup
  | theoremApp lookup instantiated _ ih =>
      simp only [strip]
      exact .theoremApp lookup instantiated ih
  | conversion converted _ ih =>
      have same := Converts.eq_of_no_definitions noDefinitions converted.derives
      simp only [strip]
      exact same ▸ ih
  | nil => exact .nil
  | cons _ _ ihHead ihTail => exact .cons ihHead ihTail

/-! ## Well-typed expressions decode -/

theorem names_getElem? {source : Signature} {index : Nat} {declaration : TermDecl}
    (declared : source.termSignature index = some declaration) :
    ∃ name, source.names[index]? = some name := by
  unfold Signature.termSignature at declared
  cases found : source.language.terms[index]? with
  | none => simp [found] at declared
  | some rule =>
      refine ⟨rule.label, ?_⟩
      simp [Signature.names, constructorNames, found]

/-- A well-typed expression decodes, and to an application form unless it is a
variable. -/
theorem decode_of_hasType {source : Signature} {context : Context} {expression : Preterm}
    {remaining : Context} {sort : Nat}
    (typed : Preterm.HasType source.termSignature context expression remaining sort) :
    ∃ pattern, decode source.names expression = some pattern ∧
      (remaining ≠ [] → ∃ name arguments, pattern = .apply name arguments) := by
  induction typed with
  | var lookup => exact ⟨_, rfl, fun nonempty => absurd rfl nonempty⟩
  | term declared =>
      obtain ⟨name, named⟩ := names_getElem? declared
      exact ⟨.apply name [], by simp [decode, named], fun _ => ⟨name, [], rfl⟩⟩
  | @bound function index sort result remaining _ _ ih =>
      obtain ⟨pattern, decoded, shape⟩ := ih
      obtain ⟨name, arguments, rfl⟩ := shape (List.cons_ne_nil _ _)
      exact ⟨.apply name (arguments ++ [.bvar index]), by simp [decode, decoded],
        fun _ => ⟨name, _, rfl⟩⟩
  | @regular function argument sort result dependencies remaining _ _ ihFunction ihArgument =>
      obtain ⟨pattern, decoded, shape⟩ := ihFunction
      obtain ⟨name, arguments, rfl⟩ := shape (List.cons_ne_nil _ _)
      obtain ⟨argumentPattern, decodedArgument, _⟩ := ihArgument
      exact ⟨.apply name (arguments ++ [argumentPattern]), by simp [decode, decoded, decodedArgument],
        fun _ => ⟨name, _, rfl⟩⟩

theorem decode_of_fits {source : Signature} {context : Context} {expression : Preterm}
    {binder : Binder} (fits : Preterm.FitsBinder source.termSignature context expression binder) :
    ∃ pattern, decode source.names expression = some pattern := by
  cases fits with
  | bound _ => exact ⟨_, rfl⟩
  | regular typed =>
      obtain ⟨pattern, decoded, _⟩ := decode_of_hasType typed
      exact ⟨pattern, decoded⟩

/-- Decode a list of expressions. -/
def decodeList (names : List String) (expressions : List Preterm) : Option (List Pattern) :=
  expressions.mapM (decode names)

theorem decodeList_of_fits {source : Signature} {context : Context} :
    ∀ {expressions : List Preterm} {binders : Context},
      List.Forall₂ (Preterm.FitsBinder source.termSignature context) expressions binders →
        ∃ patterns, decodeList source.names expressions = some patterns ∧
          List.Forall₂ (fun expression pattern => decode source.names expression = some pattern)
            expressions patterns
  | [], [], .nil => ⟨[], rfl, .nil⟩
  | _ :: _, _ :: _, .cons head tail => by
      obtain ⟨pattern, decoded⟩ := decode_of_fits head
      obtain ⟨patterns, decodedList, related⟩ := decodeList_of_fits tail
      refine ⟨pattern :: patterns, ?_, .cons decoded related⟩
      simp only [decodeList, List.mapM_cons] at decodedList ⊢
      simp [decoded, decodedList]

/-- Decoded expressions encode back to themselves. -/
theorem encodeList_decoded {names : List String} (distinct : names.Nodup) :
    ∀ {expressions : List Preterm} {patterns : List Pattern},
      List.Forall₂ (fun expression pattern => decode names expression = some pattern)
        expressions patterns → encodeList names patterns = some expressions
  | [], [], .nil => by simp [encodeList]
  | _ :: _, _ :: _, .cons head tail => by
      have first := (decode_sound distinct head).eval
      have rest := encodeList_decoded distinct tail
      simp [encodeList, first, rest]

/-! ## Decompiling witnesses -/

mutual

/-- Read an MM0 witness as a raw proof tree of the presentation. -/
def decompile (presentation : Presentation) (witness : ProofWitness) : Option RawOpenProof :=
  match witness with
  | .hyp index => some (.premise index)
  | .theoremApp index arguments children =>
      match presentation.rules[index]?, decodeList presentation.syntaxSignature.names arguments,
          decompileChildren presentation children with
      | some rule, some patterns, some children' => some (.node ⟨⟨rule.row.id⟩, patterns⟩ children')
      | _, _, _ => none
  | .conversion _ child => decompile presentation child
termination_by structural witness

def decompileChildren (presentation : Presentation) (children : List ProofWitness) :
    Option (List RawOpenProof) :=
  match children with
  | [] => some []
  | child :: children =>
      match decompile presentation child, decompileChildren presentation children with
      | some first, some rest => some (first :: rest)
      | _, _ => none
termination_by structural children

end

theorem index?_rule {presentation : Presentation} {index : Nat}
    {rule : Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules.Rule}
    (found : presentation.rules[index]? = some rule) :
    index? (presentation.rules.map fun rule => rule.row.id) rule.row.id = some index := by
  have bound : index < presentation.rules.length := (List.getElem?_eq_some_iff.mp found).1
  have same : presentation.rules[index] = rule := (List.getElem?_eq_some_iff.mp found).2
  have mappedBound : index < (presentation.rules.map fun rule => rule.row.id).length := by simpa using bound
  have element : (presentation.rules.map fun rule => rule.row.id)[index] = rule.row.id := by
    simp [same]
  have member : rule.row.id ∈ presentation.rules.map fun rule => rule.row.id :=
    element ▸ List.getElem_mem mappedBound
  rw [index?_some _ _ member, ← element, presentation.distinctRules.idxOf_getElem]

/-- Compiling the decompiled tree of an accepted witness gives the witness without its
conversion steps. -/
theorem compile_decompile {presentation : Presentation} {context : Context}
    {hypotheses : List Preterm} {witness : ProofWitness} {expression : Preterm}
    (checked : ProofWitness.Checks presentation.theory.termSignature presentation.theory.definitionSignature
      presentation.theory.theoremSignature context hypotheses witness expression) :
    ∃ tree, decompile presentation witness = some tree ∧
      compile? presentation tree = some (strip witness) := by
  induction checked using ProofWitness.Checks.rec
      (motive_2 := fun children _ _ =>
        ∃ trees, decompileChildren presentation children = some trees ∧
          compileChildren? presentation trees = some (stripChildren children)) with
  | @hyp index _ _ => exact ⟨.premise index, rfl, by simp [compile?, strip]⟩
  | @theoremApp index declaration arguments children instance_ lookup instantiated _ ih =>
      obtain ⟨trees, decompiled, compiled⟩ := ih
      rw [presentation.theory_theoremSignature] at lookup
      cases found : presentation.rules[index]? with
      | none => simp [found] at lookup
      | some rule =>
          have typed := instantiated.admissible.typed
          rw [presentation.theory_termSignature] at typed
          obtain ⟨patterns, decodedList, related⟩ := decodeList_of_fits typed
          have encoded := encodeList_decoded presentation.syntaxSignature.distinctConstructors related
          refine ⟨.node ⟨⟨rule.row.id⟩, patterns⟩ trees, ?_, ?_⟩
          · simp only [decompile, found, decodedList, decompiled]
          · simp only [compile?, Option.bind_eq_bind, strip]
            rw [index?_rule found]
            simp only [Option.bind_some]
            rw [show encodeList presentation.syntaxSignature.names patterns = some arguments from encoded]
            simp [compiled]
  | conversion _ _ ih =>
      obtain ⟨tree, decompiled, compiled⟩ := ih
      exact ⟨tree, by simpa [decompile] using decompiled, by simpa [strip] using compiled⟩
  | nil => exact ⟨[], rfl, by simp [compileChildren?, stripChildren]⟩
  | cons _ _ ihHead ihTail =>
      obtain ⟨tree, decompiled, compiled⟩ := ihHead
      obtain ⟨trees, decompiledRest, compiledRest⟩ := ihTail
      refine ⟨tree :: trees, ?_, ?_⟩
      · simp [decompileChildren, decompiled, decompiledRest]
      · simp [compileChildren?, compiled, compiledRest, stripChildren]

/-- **Read-back.** For a presentation without equations, if the MM0 kernel accepts a
witness for the rendering of a sequent, the presentation accepts the decompiled tree
for the sequent. -/
theorem decompile_accepted {presentation : Presentation}
    (equationFree : presentation.syntaxSignature.language.equations = [])
    {bound : List TypeExpr} {context : Context} {hypotheses : List Pattern}
    {targetHypotheses : List Preterm} {pattern : Pattern} {expression : Preterm}
    (contexts : ContextEncodes presentation.syntaxSignature.sorts bound context)
    (localScope : List.Forall₂ (Encodes presentation.syntaxSignature.names) hypotheses targetHypotheses)
    (encoded : Encodes presentation.syntaxSignature.names pattern expression)
    {witness : ProofWitness}
    (checked : ProofWitness.Checks presentation.theory.termSignature presentation.theory.definitionSignature
      presentation.theory.theoremSignature context targetHypotheses witness expression) :
    ∃ tree, decompile presentation witness = some tree ∧
      SortedFirstOrderRules.Checks presentation.syntaxSignature.language presentation.rules bound
        hypotheses tree pattern := by
  obtain ⟨tree, decompiled, compiled⟩ := compile_decompile checked
  have stripped := strip_checks (presentation.theory_definitionSignature_eq_none equationFree) checked
  exact ⟨tree, decompiled, (checks_iff_compiled contexts localScope encoded).mpr ⟨_, compiled, stripped⟩⟩

/-! ## Sizes and time -/

theorem patternSizes_append (first second : List Pattern) :
    patternSizes (first ++ second) = patternSizes first + patternSizes second := by
  induction first with
  | nil => simp [patternSizes]
  | cons pattern patterns ih => simp only [List.cons_append, patternSizes, ih]; omega

theorem decode_size {names : List String} :
    ∀ {expression : Preterm} {pattern : Pattern}, decode names expression = some pattern →
      patternSize pattern ≤ expression.size
  | .var index, pattern, decoded => by
      simp only [decode, Option.some.injEq] at decoded
      subst decoded
      simp [patternSize, Preterm.size]
  | .term index, pattern, decoded => by
      simp only [decode, Option.bind_eq_bind] at decoded
      cases named : names[index]? with
      | none => simp [named] at decoded
      | some name =>
          simp only [named, Option.bind_some, Option.pure_def, Option.some.injEq] at decoded
          subst decoded
          simp [patternSize, patternSizes, Preterm.size]
  | .app function argument, pattern, decoded => by
      simp only [decode, Option.bind_eq_bind] at decoded
      cases first : decode names function with
      | none => simp [first] at decoded
      | some functionPattern =>
          cases second : decode names argument with
          | none => simp [first, second] at decoded
          | some argumentPattern =>
              simp only [first, second, Option.bind_some] at decoded
              cases functionPattern with
              | apply name arguments =>
                  simp only [Option.pure_def, Option.some.injEq] at decoded
                  subst decoded
                  have left := decode_size first
                  have right := decode_size second
                  simp only [patternSize, patternSizes_append, patternSizes, Preterm.size] at left ⊢
                  omega
              | _ => simp at decoded

theorem decodeList_size {names : List String} :
    ∀ {expressions : List Preterm} {patterns : List Pattern},
      decodeList names expressions = some patterns → patternSizes patterns ≤ sizes expressions
  | [], patterns, decoded => by
      simp only [decodeList, List.mapM_nil, Option.pure_def, Option.some.injEq] at decoded
      subst decoded
      simp [patternSizes, sizes]
  | expression :: expressions, patterns, decoded => by
      simp only [decodeList, List.mapM_cons, Option.bind_eq_bind] at decoded
      cases first : decode names expression with
      | none => simp [first] at decoded
      | some pattern =>
          cases rest : expressions.mapM (decode names) with
          | none => simp [first, rest] at decoded
          | some others =>
              simp only [first, rest, Option.bind_some, Option.pure_def, Option.some.injEq] at decoded
              subst decoded
              have head := decode_size first
              have tail := decodeList_size (expressions := expressions) (show decodeList names expressions = some others from rest)
              simp only [patternSizes, sizes_cons]
              omega

mutual

theorem decompile_size {presentation : Presentation} (witness : ProofWitness) {tree : RawOpenProof}
    (decompiled : decompile presentation witness = some tree) :
    rawSize tree ≤ Cost.proofSize witness := by
  match witness with
  | .hyp index =>
      simp only [decompile, Option.some.injEq] at decompiled
      subst decompiled
      simp [rawSize, Cost.proofSize]
  | .theoremApp index arguments children =>
      simp only [decompile] at decompiled
      cases found : presentation.rules[index]? with
      | none => simp [found] at decompiled
      | some rule =>
          cases decodedList : decodeList presentation.syntaxSignature.names arguments with
          | none => simp [found, decodedList] at decompiled
          | some patterns =>
              cases decompiledChildren : decompileChildren presentation children with
              | none => simp [found, decodedList, decompiledChildren] at decompiled
              | some trees =>
                  simp only [found, decodedList, decompiledChildren, Option.some.injEq] at decompiled
                  subst decompiled
                  have argumentsSize := decodeList_size decodedList
                  have childrenSize := decompileChildren_size children decompiledChildren
                  simp only [rawSize, Cost.proofSize]
                  omega
  | .conversion step child =>
      simp only [decompile] at decompiled
      have := decompile_size child decompiled
      simp only [Cost.proofSize]
      omega
termination_by structural witness

theorem decompileChildren_size {presentation : Presentation} (children : List ProofWitness)
    {trees : List RawOpenProof} (decompiled : decompileChildren presentation children = some trees) :
    rawSizes trees ≤ Cost.proofSizes children := by
  match children with
  | [] =>
      simp only [decompileChildren, Option.some.injEq] at decompiled
      subst decompiled
      simp [rawSizes, Cost.proofSizes]
  | child :: children =>
      simp only [decompileChildren] at decompiled
      cases head : decompile presentation child with
      | none => simp [head] at decompiled
      | some first =>
          cases tail : decompileChildren presentation children with
          | none => simp [head, tail] at decompiled
          | some rest =>
              simp only [head, tail, Option.some.injEq] at decompiled
              subst decompiled
              have headSize := decompile_size child head
              have tailSize := decompileChildren_size children tail
              simp only [rawSizes, Cost.proofSizes]
              omega
termination_by structural children

end

/-- Time of `decode`: a name lookup per constructor, and an append per argument. -/
def decodeTime (names : List String) : Preterm → Nat
  | .var _ => 1
  | .term index => Cost.lookupTime names index + 1
  | .app function argument => decodeTime names function + decodeTime names argument + function.size + 1

theorem decodeTime_le (names : List String) (expression : Preterm) :
    decodeTime names expression ≤ expression.size * (names.length + expression.size + 2) := by
  induction expression with
  | var _ => simp only [decodeTime, Preterm.size]; nlinarith
  | term index => have := Cost.lookupTime_le names index; simp only [decodeTime, Preterm.size]; nlinarith
  | app function argument ihFunction ihArgument =>
      simp only [decodeTime, Preterm.size]
      nlinarith [Preterm.one_le_size function, Preterm.one_le_size argument]

mutual

/-- Time of `decompile`. -/
def decompileTime (presentation : Presentation) (witness : ProofWitness) : Nat :=
  match witness with
  | .hyp _ => 1
  | .theoremApp index arguments children =>
      Cost.lookupTime presentation.rules index +
        (arguments.map (decodeTime presentation.syntaxSignature.names)).sum + arguments.length +
          decompileChildrenTime presentation children + 1
  | .conversion _ child => decompileTime presentation child + 1
termination_by structural witness

def decompileChildrenTime (presentation : Presentation) (children : List ProofWitness) : Nat :=
  match children with
  | [] => 1
  | child :: children => decompileTime presentation child + 1 + decompileChildrenTime presentation children
termination_by structural children

end

/-- The per-node charge of decompiling a witness of size at most `budget`. -/
def decompileCharge (presentation : Presentation) (budget : Nat) : Nat :=
  presentation.rules.length + presentation.syntaxSignature.names.length + budget + 6

theorem sum_decodeTime_le (names : List String) (arguments : List Preterm) {budget : Nat}
    (small : sizes arguments ≤ budget) :
    (arguments.map (decodeTime names)).sum ≤ sizes arguments * (names.length + budget + 2) := by
  induction arguments with
  | nil => simp [sizes]
  | cons argument arguments ih =>
      simp only [List.map_cons, List.sum_cons, sizes_cons] at small ⊢
      have head := decodeTime_le names argument
      have widened := Nat.mul_le_mul_left argument.size
        (show names.length + argument.size + 2 ≤ names.length + budget + 2 by omega)
      have tail := ih (by omega)
      nlinarith

mutual

theorem decompileTime_le (presentation : Presentation) {budget : Nat} (witness : ProofWitness)
    (small : Cost.proofSize witness ≤ budget) :
    decompileTime presentation witness + 1 ≤ Cost.proofSize witness * decompileCharge presentation budget := by
  match witness with
  | .hyp _ => simp only [decompileTime, Cost.proofSize, decompileCharge]; omega
  | .theoremApp index arguments children =>
      simp only [Cost.proofSize] at small
      have lookup := Cost.lookupTime_le presentation.rules index
      have decoding := sum_decodeTime_le presentation.syntaxSignature.names arguments (budget := budget)
        (by omega)
      have argumentsLength := Cost.length_le_sizes arguments
      have list := decompileChildrenTime_le presentation (budget := budget) children (by omega)
      have charge : presentation.syntaxSignature.names.length + budget + 2 + 1 ≤
          decompileCharge presentation budget := by unfold decompileCharge; omega
      have widened := Nat.mul_le_mul_left (sizes arguments) charge
      simp only [decompileTime, Cost.proofSize]
      have rules : presentation.rules.length + 4 ≤ decompileCharge presentation budget := by
        unfold decompileCharge; omega
      have expand : sizes arguments * (presentation.syntaxSignature.names.length + budget + 2 + 1) =
          sizes arguments * (presentation.syntaxSignature.names.length + budget + 2) + sizes arguments := by
        ring
      have expandCharge : (sizes arguments + Cost.proofSizes children + 1) * decompileCharge presentation budget =
          sizes arguments * decompileCharge presentation budget +
            Cost.proofSizes children * decompileCharge presentation budget +
              decompileCharge presentation budget := by ring
      omega
  | .conversion _ child =>
      simp only [Cost.proofSize] at small
      have inner := decompileTime_le presentation (budget := budget) child (by omega)
      have positive : 1 ≤ decompileCharge presentation budget := by unfold decompileCharge; omega
      simp only [decompileTime, Cost.proofSize]
      nlinarith
termination_by structural witness

theorem decompileChildrenTime_le (presentation : Presentation) {budget : Nat}
    (children : List ProofWitness) (small : Cost.proofSizes children ≤ budget) :
    decompileChildrenTime presentation children ≤
      Cost.proofSizes children * decompileCharge presentation budget + 1 := by
  match children with
  | [] => simp [decompileChildrenTime, Cost.proofSizes]
  | child :: children =>
      simp only [Cost.proofSizes] at small
      have head := decompileTime_le presentation (budget := budget) child (by omega)
      have tail := decompileChildrenTime_le presentation (budget := budget) children (by omega)
      simp only [decompileChildrenTime, Cost.proofSizes]
      nlinarith
termination_by structural children

end

/-! ## The p-equivalence -/

/-- **A presentation without equations p-simulates MM0.** The decompiled tree is no
larger than the witness, and decompiling takes time polynomial in the witness. -/
def decompileSimulation (presentation : Presentation)
    (equationFree : presentation.syntaxSignature.language.equations = []) :
    PSimulation (sourceChecker presentation) (targetChecker presentation) where
  translate _ witness := (decompile presentation witness).getD (.premise 0)
  preserves claim witness accepted := by
    have checked : ProofWitness.Checks presentation.theory.termSignature
        presentation.theory.definitionSignature presentation.theory.theoremSignature claim.context
        claim.targetHypotheses witness claim.expression :=
      (ProofWitness.check_iff _ _ _ _ _ _ _).mp (by simpa [targetChecker] using accepted)
    obtain ⟨tree, decompiled, sourceChecked⟩ :=
      decompile_accepted equationFree claim.contexts claim.localScope claim.encoded checked
    have proved := (SortedFirstOrderRules.proof?_eq_some_iff _ _ _ _ _ _).mpr sourceChecked
    simp [sourceChecker, decompiled, proved]
  sizeBound := ⟨X + 1, fun input => by
    simp only [sourceChecker, targetChecker, SizedChecker.inputSize, eval_add, eval_X, eval_one]
    cases decompiled : decompile presentation input.2 with
    | none => simp [rawSize]
    | some tree =>
        have := decompile_size input.2 decompiled
        simp only [Option.getD_some]
        omega⟩
  translationTime _ witness := decompileTime presentation witness
  timeBound := by
    refine ⟨(X + 1) * (X + C (presentation.rules.length + presentation.syntaxSignature.names.length + 6)),
      fun input => ?_⟩
    have bound := decompileTime_le presentation (budget := Cost.proofSize input.2) input.2 le_rfl
    simp only [targetChecker, SizedChecker.inputSize, eval_mul, eval_add, eval_X, eval_one, eval_C]
    unfold decompileCharge at bound
    have widened : Cost.proofSize input.2 *
        (presentation.rules.length + presentation.syntaxSignature.names.length + Cost.proofSize input.2 + 6) ≤
        (EncodedSequent.size input.1 + Cost.proofSize input.2 + 1) *
          (EncodedSequent.size input.1 + Cost.proofSize input.2 +
            (presentation.rules.length + presentation.syntaxSignature.names.length + 6)) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega

/-- **MM0 and a presentation without equations p-simulate each other.** -/
def pEquivalent (presentation : Presentation)
    (equationFree : presentation.syntaxSignature.language.equations = []) :
    PSimulation (targetChecker presentation) (sourceChecker presentation) ×
      PSimulation (sourceChecker presentation) (targetChecker presentation) :=
  (compileSimulation presentation, decompileSimulation presentation equationFree)

/-! ## Controls -/

/-- A hypothesis reads back as the premise at the same position. -/
example (presentation : Presentation) : decompile presentation (.hyp 4) = some (.premise 4) := by
  simp [decompile]

/-- A theorem application at a position with no rule does not read back. -/
example (presentation : Presentation) :
    decompile presentation (.theoremApp presentation.rules.length [] []) = none := by
  simp [decompile]

/-- Removing conversion steps keeps theorem applications and drops conversions. -/
example (witness : ProofWitness) (step : ConvWitness) :
    strip (.conversion step witness) = strip witness := by
  simp [strip]

end Mettapedia.Languages.MM0.Translation.CertificateEquivalence
