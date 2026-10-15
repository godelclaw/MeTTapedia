import Mettapedia.GSLT.LanguageDef.ProofSystems
import Mettapedia.Languages.MM0.Kernel.ProofComplexity
import Mettapedia.Languages.MM0.Translation.FirstOrderCertificates
import Mettapedia.Languages.MM0.Translation.FirstOrderPropositionalMeaning

/-!
# MM0 p-simulates the tree checkers of first-order presentations

A first-order presentation has its own certificate checker: `SortedFirstOrderRules.proof?`
reads a raw proof tree and computes the pattern it proves. `compile?` turns such a tree
into an MM0 proof witness node for node, and `checkCompiled_iff` says the MM0 kernel
accepts the compiled witness exactly when the presentation accepts the tree. For a
presentation with equations these are its trees without conversion steps. Its
certificates with conversion steps compile too (`checksModulo_iff_compiled`), and
that translation is not timed here.

This module adds the bounds that make the translation a p-simulation in the sense of
Cook and Reckhow. The compiled witness has at most twice the size of the tree
(`compile_size`), and the translation's time function is linear in the tree with a
factor fixed by the presentation (`compileTime_le`). So the MM0 checker p-simulates the
presentation's checker on every sequent the two sides both render
(`compileSimulation`).

For the Hilbert systems of intuitionistic and classical propositional logic, presented
rule for rule as Foundation's, this is MM0 p-simulating Cook and Reckhow's Frege
systems in tree form (`fregeSimulation`).

Sizes count nodes, and a name lookup is charged per entry, comparing names as atoms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.CertificateSimulation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.GSLT.LanguageDef.ProofSystems
open Kernel FirstOrderSyntax FirstOrderTyping FirstOrderRules FirstOrderCertificates
open Polynomial

/-! ## Sizes of patterns and raw proofs -/

mutual

/-- The number of nodes of a first-order pattern; other forms count as one node. -/
def patternSize (pattern : Pattern) : Nat :=
  match pattern with
  | .apply _ arguments => patternSizes arguments + 1
  | _ => 1
termination_by structural pattern

def patternSizes (patterns : List Pattern) : Nat :=
  match patterns with
  | [] => 0
  | pattern :: patterns => patternSize pattern + patternSizes patterns
termination_by structural patterns

end

mutual

/-- The size of a raw proof tree: its nodes and the patterns of its arguments. -/
def rawSize (proof : RawOpenProof) : Nat :=
  match proof with
  | .premise _ => 1
  | .node invocation children => patternSizes invocation.arguments + rawSizes children + 1
termination_by structural proof

def rawSizes (proofs : List RawOpenProof) : Nat :=
  match proofs with
  | [] => 0
  | proof :: proofs => rawSize proof + rawSizes proofs
termination_by structural proofs

end

/-! ## The compiled witness is at most twice the tree -/

mutual

theorem encode_size {names : List String} {pattern : Pattern} {expression : Preterm}
    (encoded : encode names pattern = some expression) :
    expression.size + 1 ≤ 2 * patternSize pattern := by
  cases pattern with
  | bvar index =>
      simp only [encode, Option.some.injEq] at encoded
      subst expression
      simp [Preterm.size, patternSize]
  | apply name arguments =>
      cases found : index? names name with
      | none => simp [encode, found] at encoded
      | some index =>
          cases result : encodeList names arguments with
          | none => simp [encode, found, result] at encoded
          | some expressions =>
              have same : Preterm.applyArgs (.term index) expressions = expression := by
                simpa [encode, found, result] using encoded
              subst expression
              have list := encodeList_size result
              rw [Cost.size_applyArgs]
              simp only [Preterm.size, patternSize]
              omega
  | _ => simp [encode] at encoded
termination_by sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

theorem encodeList_size {names : List String} {patterns : List Pattern} {expressions : List Preterm}
    (encoded : encodeList names patterns = some expressions) :
    sizes expressions + expressions.length ≤ 2 * patternSizes patterns := by
  cases patterns with
  | nil =>
      simp only [encodeList, Option.some.injEq] at encoded
      subst expressions
      simp [sizes, patternSizes]
  | cons pattern patterns =>
      cases first : encode names pattern with
      | none => simp [encodeList, first] at encoded
      | some head =>
          cases rest : encodeList names patterns with
          | none => simp [encodeList, first, rest] at encoded
          | some tail =>
              have same : head :: tail = expressions := by simpa [encodeList, first, rest] using encoded
              subst expressions
              have headSize := encode_size first
              have tailSize := encodeList_size rest
              simp only [sizes_cons, List.length_cons, patternSizes]
              omega
termination_by sizeOf patterns
decreasing_by all_goals sizeOf_pattern_dec

end

mutual

theorem compile_size {presentation : Presentation} (proof : RawOpenProof) {witness : ProofWitness}
    (compiled : compile? presentation proof = some witness) :
    Cost.proofSize witness ≤ 2 * rawSize proof := by
  match proof with
  | .premise index =>
      simp only [compile?, Option.some.injEq] at compiled
      subst compiled
      simp [Cost.proofSize, rawSize]
  | .node invocation children =>
      simp only [compile?, Option.bind_eq_bind] at compiled
      cases found : index? (presentation.rules.map fun rule => rule.row.id) invocation.ruleId.value with
      | none => simp [found] at compiled
      | some ruleIndex =>
          cases arguments : encodeList presentation.syntaxSignature.names invocation.arguments with
          | none => simp [found, arguments] at compiled
          | some encoded =>
              cases compiledChildren : compileChildren? presentation children with
              | none => simp [found, arguments, compiledChildren] at compiled
              | some witnesses =>
                  simp only [found, arguments, compiledChildren, Option.bind_some, Option.pure_def,
                    Option.some.injEq] at compiled
                  subst compiled
                  have argumentsSize := encodeList_size arguments
                  have childrenSize := compileChildren_size children compiledChildren
                  simp only [Cost.proofSize, rawSize]
                  omega
termination_by structural proof

theorem compileChildren_size {presentation : Presentation} (proofs : List RawOpenProof)
    {witnesses : List ProofWitness} (compiled : compileChildren? presentation proofs = some witnesses) :
    Cost.proofSizes witnesses ≤ 2 * rawSizes proofs := by
  match proofs with
  | [] =>
      simp only [compileChildren?, Option.some.injEq] at compiled
      subst compiled
      simp [Cost.proofSizes, rawSizes]
  | proof :: proofs =>
      simp only [compileChildren?, Option.bind_eq_bind] at compiled
      cases first : compile? presentation proof with
      | none => simp [first] at compiled
      | some witness =>
          cases rest : compileChildren? presentation proofs with
          | none => simp [first, rest] at compiled
          | some remaining =>
              simp only [first, rest, Option.bind_some, Option.pure_def, Option.some.injEq] at compiled
              subst compiled
              have headSize := compile_size proof first
              have tailSize := compileChildren_size proofs rest
              simp only [Cost.proofSizes, rawSizes]
              omega
termination_by structural proofs

end

/-! ## The translation runs in linear time -/

/-- Time of a name lookup: a membership test and an index search, each walking the
names once. -/
def nameTime (names : List String) : Nat := 2 * names.length + 2

mutual

/-- Time of `encode`. -/
def encodeTime (names : List String) (pattern : Pattern) : Nat :=
  match pattern with
  | .apply _ arguments => nameTime names + encodeListTime names arguments + arguments.length + 1
  | _ => 1
termination_by structural pattern

/-- Time of `encodeList`. -/
def encodeListTime (names : List String) (patterns : List Pattern) : Nat :=
  match patterns with
  | [] => 1
  | pattern :: patterns => encodeTime names pattern + 1 + encodeListTime names patterns
termination_by structural patterns

end

mutual

theorem encodeTime_le (names : List String) (pattern : Pattern) :
    encodeTime names pattern + 2 ≤ (2 * names.length + 6) * patternSize pattern := by
  match pattern with
  | .apply _ arguments =>
      have list := encodeListTime_le names arguments
      simp only [encodeTime, patternSize, nameTime]
      nlinarith
  | .bvar _ => simp only [encodeTime, patternSize]; omega
  | .fvar _ => simp only [encodeTime, patternSize]; omega
  | .lambda _ _ => simp only [encodeTime, patternSize]; omega
  | .multiLambda _ _ _ => simp only [encodeTime, patternSize]; omega
  | .subst _ _ => simp only [encodeTime, patternSize]; omega
  | .collection _ _ _ => simp only [encodeTime, patternSize]; omega
termination_by structural pattern

theorem encodeListTime_le (names : List String) (patterns : List Pattern) :
    encodeListTime names patterns + patterns.length ≤
      (2 * names.length + 6) * patternSizes patterns + 1 := by
  match patterns with
  | [] => simp [encodeListTime, patternSizes]
  | pattern :: patterns =>
      have head := encodeTime_le names pattern
      have tail := encodeListTime_le names patterns
      simp only [encodeListTime, patternSizes, List.length_cons]
      nlinarith
termination_by structural patterns

end

mutual

/-- Time of `compile?`. -/
def compileTime (presentation : Presentation) (proof : RawOpenProof) : Nat :=
  match proof with
  | .premise _ => 1
  | .node invocation children =>
      nameTime (presentation.rules.map fun rule => rule.row.id) +
        encodeListTime presentation.syntaxSignature.names invocation.arguments +
          compileChildrenTime presentation children + 1
termination_by structural proof

/-- Time of `compileChildren?`. -/
def compileChildrenTime (presentation : Presentation) (proofs : List RawOpenProof) : Nat :=
  match proofs with
  | [] => 1
  | proof :: proofs => compileTime presentation proof + 1 + compileChildrenTime presentation proofs
termination_by structural proofs

end

/-- The factor of the translation's linear time, fixed by the presentation. -/
def compileFactor (presentation : Presentation) : Nat :=
  2 * presentation.rules.length + 2 * presentation.syntaxSignature.names.length + 10

mutual

theorem compileTime_le (presentation : Presentation) (proof : RawOpenProof) :
    compileTime presentation proof + 2 ≤ compileFactor presentation * rawSize proof := by
  match proof with
  | .premise _ => simp only [compileTime, rawSize, compileFactor]; omega
  | .node invocation children =>
      have arguments := encodeListTime_le presentation.syntaxSignature.names invocation.arguments
      have list := compileChildrenTime_le presentation children
      have factor : 2 * presentation.syntaxSignature.names.length + 6 ≤ compileFactor presentation := by
        unfold compileFactor; omega
      have widened := Nat.mul_le_mul_right (patternSizes invocation.arguments) factor
      simp only [compileTime, rawSize, nameTime, List.length_map]
      have rules : 2 * presentation.rules.length + 7 ≤ compileFactor presentation := by
        unfold compileFactor; omega
      nlinarith
termination_by structural proof

theorem compileChildrenTime_le (presentation : Presentation) (proofs : List RawOpenProof) :
    compileChildrenTime presentation proofs + proofs.length ≤
      compileFactor presentation * rawSizes proofs + 1 := by
  match proofs with
  | [] => simp [compileChildrenTime, rawSizes]
  | proof :: proofs =>
      have head := compileTime_le presentation proof
      have tail := compileChildrenTime_le presentation proofs
      simp only [compileChildrenTime, rawSizes, List.length_cons]
      nlinarith
termination_by structural proofs

end

/-! ## The p-simulation -/

/-- A sequent of a presentation together with its MM0 rendering. -/
structure EncodedSequent (presentation : Presentation) where
  bound : List TypeExpr
  hypotheses : List Pattern
  pattern : Pattern
  context : Context
  targetHypotheses : List Preterm
  expression : Preterm
  contexts : ContextEncodes presentation.syntaxSignature.sorts bound context
  localScope : List.Forall₂ (Encodes presentation.syntaxSignature.names) hypotheses targetHypotheses
  encoded : Encodes presentation.syntaxSignature.names pattern expression

/-- The size of a sequent, measured on the presentation's side. -/
def EncodedSequent.size {presentation : Presentation} (claim : EncodedSequent presentation) : Nat :=
  patternSizes claim.hypotheses + patternSize claim.pattern + claim.bound.length

/-- The presentation's checker of proof trees. -/
def sourceChecker (presentation : Presentation) :
    SizedChecker (EncodedSequent presentation) RawOpenProof where
  check claim proof := decide (SortedFirstOrderRules.proof? presentation.syntaxSignature.language
    presentation.rules claim.bound claim.hypotheses proof = some claim.pattern)
  claimSize := EncodedSequent.size
  certificateSize := rawSize

/-- The MM0 kernel checking the rendering of the same sequent. -/
def targetChecker (presentation : Presentation) :
    SizedChecker (EncodedSequent presentation) ProofWitness where
  check claim witness := ProofWitness.check presentation.theory.termSignature
    presentation.theory.definitionSignature presentation.theory.theoremSignature claim.context
    claim.targetHypotheses witness claim.expression
  claimSize := EncodedSequent.size
  certificateSize := Cost.proofSize

/-- **MM0 p-simulates every first-order presentation's tree checker.** The compiled witness
is at most twice the size of the tree, and the translation runs in linear time. -/
def compileSimulation (presentation : Presentation) :
    PSimulation (targetChecker presentation) (sourceChecker presentation) where
  translate _ proof := (compile? presentation proof).getD (.hyp 0)
  preserves claim proof accepted := by
    have proved : SortedFirstOrderRules.proof? presentation.syntaxSignature.language presentation.rules
        claim.bound claim.hypotheses proof = some claim.pattern := by
      simpa [sourceChecker] using accepted
    have checked := (checkCompiled_iff claim.contexts claim.localScope claim.encoded).mpr proved
    unfold checkCompiled at checked
    cases compiled : compile? presentation proof with
    | none => simp [compiled] at checked
    | some witness => simpa [targetChecker, compiled] using checked
  sizeBound := ⟨2 * X + 1, fun input => by
    simp only [targetChecker, sourceChecker, SizedChecker.inputSize, eval_add, eval_mul, eval_X,
      eval_one, eval_ofNat]
    cases compiled : compile? presentation input.2 with
    | none => simp [Cost.proofSize]
    | some witness =>
        have := compile_size input.2 compiled
        simp only [Option.getD_some]
        omega⟩
  translationTime _ proof := compileTime presentation proof
  timeBound := ⟨C (compileFactor presentation) * X, fun input => by
    have := compileTime_le presentation input.2
    simp only [sourceChecker, SizedChecker.inputSize, eval_mul, eval_C, eval_X]
    nlinarith⟩

/-- **MM0 p-simulates Frege systems.** The Hilbert systems of intuitionistic and classical
propositional logic, presented rule for rule as Foundation's
(`PropositionalHilbertPresentations.derives_iff_hilbert`), are Cook and Reckhow's Frege
systems in tree form. -/
def fregeSimulation (classical : Bool) :
    PSimulation (targetChecker (FirstOrderPropositionalMeaning.presentation classical))
      (sourceChecker (FirstOrderPropositionalMeaning.presentation classical)) :=
  compileSimulation (FirstOrderPropositionalMeaning.presentation classical)

/-! ## Controls -/

example : rawSize (.premise 0) = 1 := rfl

example (presentation : Presentation) : compileTime presentation (.premise 3) = 1 := rfl

/-- A premise compiles to a hypothesis of the same size. -/
example (presentation : Presentation) : compile? presentation (.premise 2) = some (.hyp 2) := by
  simp [compile?]

/-- A certificate naming a rule the presentation lacks does not compile. -/
theorem compile_unknownRule (presentation : Presentation) {name : String} {arguments : List Pattern}
    {children : List RawOpenProof}
    (unknown : name ∉ presentation.rules.map fun rule => rule.row.id) :
    compile? presentation (.node ⟨⟨name⟩, arguments⟩ children) = none := by
  simp only [compile?, Option.bind_eq_bind, index?]
  simp [unknown]

end Mettapedia.Languages.MM0.Translation.CertificateSimulation
