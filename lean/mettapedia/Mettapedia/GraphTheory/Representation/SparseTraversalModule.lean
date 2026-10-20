import Mettapedia.Algebra.SparseLinearMap
import Mettapedia.GraphTheory.Representation.EdgeListToMatrixModule

/-!
# An authored module for weighted sparse traversal

The two operational rules consume a weighted input reference and finish the
row. Arithmetic is represented by an expression tree with an independent
semiring interpretation; no result is supplied to a rewrite as a premise.
The generic executor's exact successor list agrees with the typed machine
on every canonical state, including terminal states.

The established canonical text/UTF-8 codec carries the complete module.
This adds no alternative parser or external byte-format claim.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.Representation.SparseTraversalModule

open Mettapedia.Algebra
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation
open Mettapedia.GSLT.LanguageDef

/-- Weighted references retain coefficient and input names separately. -/
def quoted : QuotedTheory := moduleTheory! Theory SparseTraversal() {
  Types { Name; Scalar; Entry; Entries; State; }
  Terms {
    NameZero . |- : Name;
    NameSucc . key:Name |- : Name;
    Zero . |- : Scalar;
    Parameter . key:Name |- : Scalar;
    Add . left:Scalar, right:Scalar |- : Scalar;
    Multiply . left:Scalar, right:Scalar |- : Scalar;
    Weighted . weight:Name, input:Name |- : Entry;
    Nil . |- : Entries;
    Cons . entry:Entry, rest:Entries |- : Entries;
    Active . remaining:Entries, accumulator:Scalar |- : State;
    Done . result:Scalar |- : State;
  }
  Rewrites {
    Consume : (Active (Cons (Weighted Weight Input) Rest) Accumulator) ~>
      (Active Rest (Add Accumulator (Multiply (Parameter Weight) (Parameter Input))));
    Finish : (Active (Nil) Accumulator) ~> (Done Accumulator);
  }
  Exports { Name; Scalar; Entry; Entries; State; }
}

def language : LanguageDef := quoted.toLanguageDef

def consumeRule : RewriteRule :=
  RewriteRule.mk (bindings := none) "Consume" [] []
    (.apply "Active" [.apply "Cons"
      [.apply "Weighted" [.fvar "Weight", .fvar "Input"], .fvar "Rest"], .fvar "Accumulator"])
    (.apply "Active" [.fvar "Rest", .apply "Add" [.fvar "Accumulator",
      .apply "Multiply" [.apply "Parameter" [.fvar "Weight"], .apply "Parameter" [.fvar "Input"]]]])

def finishRule : RewriteRule :=
  RewriteRule.mk (bindings := none) "Finish" [] []
    (.apply "Active" [.apply "Nil" [], .fvar "Accumulator"])
    (.apply "Done" [.fvar "Accumulator"])

theorem language_rewrites : language.rewrites = [consumeRule, finishRule] := rfl

theorem language_validates : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  all_goals try decide +kernel
  intro rule member
  rw [language_rewrites] at member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl
  all_goals
    simp +decide [LanguageDef.validateRewrite, language, quoted, consumeRule, finishRule,
      LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames, LanguageDef.typeNames]

theorem quoted_admitted : (admit? quoted).isSome = true := by
  apply (admit_isSome_iff quoted).mpr
  constructor
  · change language.validate.isEmpty = true
    rw [language_validates]
    rfl
  · decide

inductive Expr where
  | zero
  | parameter (key : Nat)
  | add (first second : Expr)
  | multiply (first second : Expr)
deriving DecidableEq, Repr

def Expr.eval {R : Type*} [Zero R] [Add R] [Mul R] (environment : Nat → R) : Expr → R
  | .zero => 0
  | .parameter key => environment key
  | .add first second => first.eval environment + second.eval environment
  | .multiply first second => first.eval environment * second.eval environment

def Expr.nodes : Expr → Nat
  | .zero => 1
  | .parameter _ => 1
  | .add first second | .multiply first second => 1 + first.nodes + second.nodes

abbrev Entry := Nat × Nat

def update (accumulator : Expr) (entry : Entry) : Expr :=
  .add accumulator (.multiply (.parameter entry.1) (.parameter entry.2))

/-- The symbolic source retains four new expression nodes per occurrence.
An arithmetic-only endpoint observer does not require retaining this tree. -/
theorem constructed_nodes (entries : List Entry) (initial : Expr) :
    (entries.foldl update initial).nodes = initial.nodes + 4 * entries.length := by
  induction entries generalizing initial with
  | nil => simp
  | cons entry rest ih =>
      rw [List.foldl_cons, ih]
      simp only [update, Expr.nodes, List.length_cons]
      omega

abbrev State := Mettapedia.GSLT.Dynamics.OrderedListFold.State Entry Expr

def step? : State → Option State :=
  Mettapedia.GSLT.Dynamics.OrderedListFold.step? update

def namePattern : Nat → Pattern
  | 0 => .apply "NameZero" []
  | n + 1 => .apply "NameSucc" [namePattern n]

def exprPattern : Expr → Pattern
  | .zero => .apply "Zero" []
  | .parameter key => .apply "Parameter" [namePattern key]
  | .add first second => .apply "Add" [exprPattern first, exprPattern second]
  | .multiply first second => .apply "Multiply" [exprPattern first, exprPattern second]

def entryPattern (entry : Entry) : Pattern :=
  .apply "Weighted" [namePattern entry.1, namePattern entry.2]

def entriesPattern : List Entry → Pattern
  | [] => .apply "Nil" []
  | entry :: rest => .apply "Cons" [entryPattern entry, entriesPattern rest]

def statePattern : State → Pattern
  | .active entries accumulator => .apply "Active" [entriesPattern entries, exprPattern accumulator]
  | .done result => .apply "Done" [exprPattern result]

def rootSuccessors (source : Pattern) : List Pattern :=
  rewriteAt (engineBasePremises RelationEnv.empty) language 1 source

theorem rootSuccessors_cons (entry : Entry) (rest : List Entry) (accumulator : Expr) :
    rootSuccessors (statePattern (.active (entry :: rest) accumulator)) =
      [statePattern (.active rest (update accumulator entry))] := by
  simp [OSLF.MeTTaIL.Reflection.ReflectionProfile.empty,
    matchingPresentationForRule?, substitutionPresentationForRule?, reflectiveRuleForRule?,
    rootSuccessors, rewriteAt, language_rewrites, consumeRule, finishRule,
    statePattern, entriesPattern, entryPattern, exprPattern, update, applyRuleUsing,
    matchPatternForRule, matchPatternForRuleUsing, applyBindingsForRule,
    applyBindingsForRuleUsing, Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings,
    premisesUsing,
    Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
    Mettapedia.OSLF.MeTTaIL.Match.matchArgs,
    Mettapedia.OSLF.MeTTaIL.Match.mergeBindings,
    Mettapedia.OSLF.MeTTaIL.Match.applyBindings]

theorem rootSuccessors_nil (accumulator : Expr) :
    rootSuccessors (statePattern (.active [] accumulator)) = [statePattern (.done accumulator)] := by
  simp [OSLF.MeTTaIL.Reflection.ReflectionProfile.empty,
    matchingPresentationForRule?, substitutionPresentationForRule?, reflectiveRuleForRule?,
    rootSuccessors, rewriteAt, language_rewrites, consumeRule, finishRule,
    statePattern, entriesPattern,  applyRuleUsing,
    matchPatternForRule, matchPatternForRuleUsing, applyBindingsForRule,
    applyBindingsForRuleUsing, Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings,
    premisesUsing,
    Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
    Mettapedia.OSLF.MeTTaIL.Match.matchArgs,
    Mettapedia.OSLF.MeTTaIL.Match.mergeBindings,
    Mettapedia.OSLF.MeTTaIL.Match.applyBindings]

theorem rootSuccessors_done (result : Expr) :
    rootSuccessors (statePattern (.done result)) = [] := by
  simp [OSLF.MeTTaIL.Reflection.ReflectionProfile.empty,
    matchingPresentationForRule?,  reflectiveRuleForRule?,
    rootSuccessors, rewriteAt, language_rewrites, consumeRule, finishRule,
    statePattern,   applyRuleUsing,
    matchPatternForRule, matchPatternForRuleUsing, applyBindingsForRule,
    applyBindingsForRuleUsing, 
    
    Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
    
    
    Mettapedia.OSLF.MeTTaIL.Match.matchPattern]

theorem rootSuccessors_state (source : State) :
    rootSuccessors (statePattern source) = (step? source).toList.map statePattern := by
  cases source with
  | active entries accumulator =>
      cases entries with
      | nil => exact rootSuccessors_nil accumulator
      | cons entry rest => exact rootSuccessors_cons entry rest accumulator
  | done result => exact rootSuccessors_done result

/-- The canonical result-list equality gives preservation and no extra root
outcomes, rather than preservation alone. -/
theorem root_step_iff (source : State) (target : Pattern) :
    target ∈ rootSuccessors (statePattern source) ↔
      ∃ next, step? source = some next ∧ target = statePattern next := by
  rw [rootSuccessors_state]
  cases transition : step? source <;> simp

/-- The selected root execution is an actual reduction of the authored
language, not a second rewrite table defined by its evaluator. -/
theorem language_step {source target : State} (transition : step? source = some target) :
    langReduces language (statePattern source) (statePattern target) := by
  apply (langReducesUsing_iff_execUsing RelationEnv.empty language _ _).2
  refine ⟨1, ?_⟩
  change statePattern target ∈ rootSuccessors (statePattern source)
  exact (root_step_iff source _).2 ⟨target, transition, rfl⟩

def constructionPath : (entries : List Entry) → (initial : Expr) →
    (langGSLT language).RewritePath (statePattern (.active entries initial))
      (statePattern (.done (entries.foldl update initial)))
  | [], initial =>
      .cons (langReduces_to_semantic _ (language_step (source := .active [] initial) rfl)) (.nil _)
  | entry :: rest, initial =>
      .cons (langReduces_to_semantic _
        (language_step (source := .active (entry :: rest) initial) rfl))
        (constructionPath rest (update initial entry))

theorem constructionPath_length (entries : List Entry) (initial : Expr) :
    (constructionPath entries initial).length = entries.length + 1 := by
  induction entries generalizing initial with
  | nil => rfl
  | cons entry rest ih =>
      change 1 + (constructionPath rest (update initial entry)).length = rest.length + 2
      rw [ih]
      omega

def interpretedEntries {R : Type*} (environment : Nat → R)
    (entries : List Entry) : List (Nat × R) :=
  entries.map (fun entry => (entry.2, environment entry.1))

theorem completed_expression_eval {R : Type*} [Zero R] [Add R] [Mul R] (environment : Nat → R)
    (entries : List Entry) (initial : Expr) :
    (entries.foldl update initial).eval environment =
      SparseLinearMap.rowRun (interpretedEntries environment entries) environment
        (initial.eval environment) := by
  induction entries generalizing initial with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.foldl_cons, interpretedEntries, List.map_cons,
        SparseLinearMap.rowRun]
      exact ih (update initial entry)

/-- Empty-initialized authored traversal is a row of the general sparse
operator, with coefficients and input values supplied by the environment. -/
theorem completed_expression_sparse {R : Type*} [Zero R] [Add R] [Mul R] (environment : Nat → R)
    (entries : List Entry) :
    (entries.foldl update .zero).eval environment =
      SparseLinearMap.apply (fun _ : Unit => interpretedEntries environment entries) environment () :=
  completed_expression_eval environment entries .zero

def schema : String := "weighted-sparse-traversal/1"

def envelope : ModuleFormat.Module ModuleFormat.upstreamLimits :=
  ⟨⟨"SparseTraversal", [], [⟨"TraversalLanguage",
    ModuleFormat.Portable.specification schema ModuleFormat.Portable.exportsCodec quoted⟩]⟩,
    by decide⟩

def moduleText : String := ModuleFormat.renderText ModuleFormat.upstreamLimits envelope

def moduleBytes : ByteArray := ModuleFormat.Text.renderBytes
  (ModuleFormat.Value.Wire.encode (ModuleFormat.encodeRaw envelope.val))

theorem moduleBytes_eq_utf8 : moduleBytes = moduleText.toUTF8 := rfl

theorem read_moduleText :
    ModuleFormat.readText? ModuleFormat.upstreamLimits moduleText = some envelope :=
  ModuleFormat.readText_renderText _ _

theorem read_moduleBytes :
    (ModuleFormat.Text.readBytes? moduleBytes).bind (fun term =>
      (ModuleFormat.Value.Wire.decode? term).bind
        (ModuleFormat.decode? ModuleFormat.upstreamLimits)) = some envelope := by
  simp [moduleBytes]

theorem read_export :
    (ModuleFormat.readText? ModuleFormat.upstreamLimits moduleText).bind (fun parsed =>
      parsed.val.exports.head?.bind (fun entry =>
        ModuleFormat.Portable.admitSpecification? schema ModuleFormat.Portable.exportsCodec entry.spec)) =
      some quoted := by
  rw [read_moduleText]
  exact ModuleFormat.Portable.specification_roundtrip _ _ _

theorem read_successors (source : State) :
    ((ModuleFormat.readText? ModuleFormat.upstreamLimits moduleText).bind (fun parsed =>
      parsed.val.exports.head?.bind (fun entry =>
        ModuleFormat.Portable.admitSpecification? schema ModuleFormat.Portable.exportsCodec entry.spec))).map
        (fun theory => rewriteAt (engineBasePremises RelationEnv.empty) theory.toLanguageDef 1
          (statePattern source)) = some ((step? source).toList.map statePattern) := by
  rw [read_export]
  exact congrArg some (rootSuccessors_state source)

theorem wrong_schema_refused :
    ModuleFormat.Portable.readTheory? "other/1" ModuleFormat.Portable.exportsCodec
      (ModuleFormat.Portable.renderTheory schema ModuleFormat.Portable.exportsCodec quoted) = none :=
  ModuleFormat.Portable.readTheory_renderTheory_otherSchema _ _ _ _ _ (by decide)

namespace Controls

def references : List Entry := [(0, 1), (0, 1)]
def environment : Nat → Nat := fun key => if key = 0 then 2 else 3

theorem duplicate_references_retain_two_occurrences :
    (constructionPath references .zero).length = 3 ∧
      (references.foldl update .zero).eval environment = 12 := by
  constructor
  · exact constructionPath_length _ _
  · decide

/-- Removing Consume keeps the signature but prevents a nonempty row from
advancing. The generic executor observes the missing behavior. -/
def withoutConsume : LanguageDef := { language with «rewrites» := [finishRule] }

theorem missing_consume_stalls :
    rewriteAt (engineBasePremises RelationEnv.empty) withoutConsume 1
      (statePattern (.active references .zero)) = [] := by
  simp [withoutConsume, references, finishRule, statePattern, entriesPattern,
    rewriteAt, applyRuleUsing, matchPatternForRule, matchPatternForRuleUsing,
    OSLF.MeTTaIL.Reflection.ReflectionProfile.empty,
    matchingPresentationForRule?, reflectiveRuleForRule?,
    Mettapedia.OSLF.MeTTaIL.Match.matchPattern, Mettapedia.OSLF.MeTTaIL.Match.matchArgs]

end Controls

end Mettapedia.GraphTheory.Representation.SparseTraversalModule
