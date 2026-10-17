import Mettapedia.GraphTheory.Representation.EdgeListToMatrixLanguageDef
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable

/-!
# Module authoring for occurrence-wise matrix materialization

The independently authored closed theory below uses the established
`moduleTheory!` quotation. Its complete core is the existing graph language,
including parameter names, constructor rows and ordered rewrite occurrences.
The original empty concrete-notation rows are retained. No graph-term source
grammar is added here.

The upstream-looking quotation is Lean syntax. Actual character and UTF-8
transport uses the separate canonical `(module:document payload)` reader and
the existing portable presentation codec, not either historical `.module`
grammar. Reading recovers the same core before its existing executor is used.

Successor-list equality gives preservation and no additional root outcomes on
canonical typed states. Construction paths use the actual generated GSLT and
retain each input occurrence; independent matrix denotation agrees with the
extensional refinement. These results do not verify mutable matrix storage or
an external implementation of the module reader or executor.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.Representation.EdgeListToMatrixModule

open Mettapedia.GraphTheory.Representation
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation

open Mettapedia.GSLT.LanguageDef

/-- This declaration spells out the source theory independently of the
existing record-valued language definition. -/
def quoted : QuotedTheory := moduleTheory! Theory EdgeListToMatrix() {
  Types { Vertex; Edge; Edges; Matrix; State; }
  Terms {
    VertexZero . |- : Vertex;
    VertexSucc . vertex:Vertex |- : Vertex;
    EdgeValue . source:Vertex, target:Vertex |- : Edge;
    EdgesNil . |- : Edges;
    EdgesCons . edge:Edge, rest:Edges |- : Edges;
    MatrixEmpty . |- : Matrix;
    MatrixSetSymmetric . matrix:Matrix, source:Vertex, target:Vertex |- : Matrix;
    Active . remaining:Edges, matrix:Matrix |- : State;
    Done . matrix:Matrix |- : State;
  }
  Rewrites {
    Write : (Active (EdgesCons (EdgeValue Source Target) Rest) Matrix) ~>
      (Active Rest (MatrixSetSymmetric Matrix Source Target));
    Finish : (Active (EdgesNil) Matrix) ~> (Done Matrix);
  }
  Exports { Vertex; Edge; Edges; Matrix; State; }
}

/-- Equality concerns the whole presentation, rather than constructor labels
or agreement on one sample execution. -/
theorem quoted_core_eq : quoted.toLanguageDef = EdgeListToMatrixLanguageDef.language := by
  rfl

theorem quoted_validates : quoted.validate = [] := by
  rw [show quoted.validate = quoted.toLanguageDef.validate from rfl, quoted_core_eq]
  exact EdgeListToMatrixLanguageDef.language_validates

theorem quoted_admitted : (admit? quoted).isSome = true := by
  apply (admit_isSome_iff quoted).mpr
  constructor
  · rw [quoted_validates]
    rfl
  · decide

/-! ## Existing root execution and independent denotation -/

def rootSuccessors (source : Pattern) : List Pattern :=
  rewriteAt (engineBasePremises RelationEnv.empty) quoted.toLanguageDef 1 source

/-- Every canonical state has exactly the already specified successor list,
including the empty result for terminal states. -/
theorem rootSuccessors_state {n : Nat} (source : EdgeListToMatrixLanguageDef.State n) :
    rootSuccessors (EdgeListToMatrixLanguageDef.statePattern source) =
      (EdgeListToMatrixLanguageDef.step? source).toList.map EdgeListToMatrixLanguageDef.statePattern := by
  unfold rootSuccessors
  rw [quoted_core_eq]
  exact EdgeListToMatrixLanguageDef.rewriteOnce_state source

theorem quoted_step_semantic_square {n : Nat} {source target : EdgeListToMatrixLanguageDef.State n}
    (step : EdgeListToMatrixLanguageDef.step? source = some target) :
    langReduces quoted.toLanguageDef (EdgeListToMatrixLanguageDef.statePattern source) (EdgeListToMatrixLanguageDef.statePattern target) ∧
      EdgeListToMatrixGSLT.step? source.denote = some target.denote := by
  rw [quoted_core_eq]
  exact EdgeListToMatrixLanguageDef.language_step_semantic_square step

/-- Construct a path of actual authored reductions, one per edge occurrence
and one finalization. The existing typed builder supplies its endpoint. -/
def constructionPath {n : Nat} :
    (remaining : List (EdgeList.Edge n)) → (matrix : EdgeListToMatrixLanguageDef.MatrixExpr n) →
    (langGSLT quoted.toLanguageDef).RewritePath
      (EdgeListToMatrixLanguageDef.statePattern (.active remaining matrix))
      (EdgeListToMatrixLanguageDef.statePattern (.done (EdgeListToMatrixLanguageDef.buildExpr matrix remaining)))
  | [], matrix =>
      .cons (langReduces_to_semantic _
        (quoted_step_semantic_square (source := .active [] matrix) rfl).1) (.nil _)
  | edge :: rest, matrix =>
      .cons (langReduces_to_semantic _
        (quoted_step_semantic_square (source := .active (edge :: rest) matrix) rfl).1)
        (constructionPath rest (.setSymmetric matrix edge))

theorem constructionPath_length {n : Nat} (remaining : List (EdgeList.Edge n))
    (matrix : EdgeListToMatrixLanguageDef.MatrixExpr n) :
    (constructionPath remaining matrix).length = remaining.length + 1 := by
  induction remaining generalizing matrix with
  | nil => rfl
  | cons edge rest inductionHypothesis =>
      change 1 + (constructionPath rest (.setSymmetric matrix edge)).length =
        rest.length + 2
      rw [inductionHypothesis]
      omega

/-- The actual construction path's terminal expression has the exact matrix
specified by the extensional graph-representation transformation. -/
theorem construction_output {n : Nat} (graph : EdgeList.Rep n) :
    (constructionPath graph.entries .empty).length = graph.entries.length + 1 ∧
      (EdgeListToMatrixLanguageDef.buildExpr .empty graph.entries).denote =
        Transformations.toMatrix (EdgeList.presentation n) graph :=
  ⟨constructionPath_length _ _, EdgeListToMatrixLanguageDef.complete_denotes_refinement graph⟩

/-! ## Canonical source text and bytes reuse the existing reader -/

def schema : String := "edge-list-matrix/1"

def sourceText : String :=
  ModuleFormat.Portable.renderTheory schema ModuleFormat.Portable.exportsCodec quoted

def sourceBytes : ByteArray :=
  ModuleFormat.Text.renderBytes
    (ModuleFormat.Portable.theoryTerm schema ModuleFormat.Portable.exportsCodec quoted)

theorem read_sourceText :
    ModuleFormat.Portable.readTheory? schema ModuleFormat.Portable.exportsCodec sourceText =
      some quoted :=
  ModuleFormat.Portable.readTheory_renderTheory _ _ _

theorem read_sourceBytes :
    (ModuleFormat.Text.readBytes? sourceBytes).bind
      (ModuleFormat.Portable.theory? schema ModuleFormat.Portable.exportsCodec) = some quoted := by
  rw [sourceBytes, ModuleFormat.Text.readBytes_renderBytes]
  change ModuleFormat.Portable.theory? schema ModuleFormat.Portable.exportsCodec
    (ModuleFormat.Portable.theoryTerm schema ModuleFormat.Portable.exportsCodec quoted) = some quoted
  exact ModuleFormat.Portable.theory_roundtrip _ _ _

/-- The reader recovers the operational presentation before any execution is
performed; it does not introduce a second rewrite table. -/
theorem read_sourceText_core :
    (ModuleFormat.Portable.readTheory? schema ModuleFormat.Portable.exportsCodec sourceText).map
      (·.toLanguageDef) = some EdgeListToMatrixLanguageDef.language := by
  rw [read_sourceText]
  exact congrArg some quoted_core_eq

theorem read_sourceText_successors {n : Nat} (source : EdgeListToMatrixLanguageDef.State n) :
    (ModuleFormat.Portable.readTheory? schema ModuleFormat.Portable.exportsCodec sourceText).map
      (fun theory => rewriteAt (engineBasePremises RelationEnv.empty)
        theory.toLanguageDef 1 (EdgeListToMatrixLanguageDef.statePattern source)) =
      some ((EdgeListToMatrixLanguageDef.step? source).toList.map EdgeListToMatrixLanguageDef.statePattern) := by
  rw [read_sourceText]
  exact congrArg some (rootSuccessors_state source)

/-- The same theory is an export of the existing public module envelope.
Envelope admission checks its schema; the export decoder below separately
checks the portable language payload. -/
def moduleEnvelope : ModuleFormat.Module ModuleFormat.upstreamLimits :=
  ⟨⟨"EdgeListToMatrix", [], [⟨"GraphLanguage",
    ModuleFormat.Portable.specification schema ModuleFormat.Portable.exportsCodec quoted⟩]⟩,
    by decide⟩

def moduleText : String := ModuleFormat.renderText ModuleFormat.upstreamLimits moduleEnvelope

def moduleBytes : ByteArray :=
  ModuleFormat.Text.renderBytes (ModuleFormat.Value.Wire.encode
    (ModuleFormat.encodeRaw moduleEnvelope.val))

theorem moduleBytes_eq_utf8 : moduleBytes = moduleText.toUTF8 := rfl

theorem read_moduleText :
    ModuleFormat.readText? ModuleFormat.upstreamLimits moduleText = some moduleEnvelope :=
  ModuleFormat.readText_renderText _ _

theorem read_moduleBytes :
    (ModuleFormat.Text.readBytes? moduleBytes).bind (fun term =>
      (ModuleFormat.Value.Wire.decode? term).bind (ModuleFormat.decode? ModuleFormat.upstreamLimits)) =
      some moduleEnvelope := by
  simp [moduleBytes]

/-- Actual character reading recovers both the admitted envelope and the
complete theory stored in its declared export position. -/
theorem read_moduleText_export :
    (ModuleFormat.readText? ModuleFormat.upstreamLimits moduleText).bind (fun parsed =>
      parsed.val.exports.head?.bind (fun entry =>
        ModuleFormat.Portable.admitSpecification? schema ModuleFormat.Portable.exportsCodec entry.spec)) =
      some quoted := by
  rw [read_moduleText]
  change ModuleFormat.Portable.admitSpecification? schema ModuleFormat.Portable.exportsCodec
    (ModuleFormat.Portable.specification schema ModuleFormat.Portable.exportsCodec quoted) = some quoted
  exact ModuleFormat.Portable.specification_roundtrip _ _ _

theorem read_moduleText_successors {n : Nat} (source : EdgeListToMatrixLanguageDef.State n) :
    ((ModuleFormat.readText? ModuleFormat.upstreamLimits moduleText).bind (fun parsed =>
      parsed.val.exports.head?.bind (fun entry =>
        ModuleFormat.Portable.admitSpecification? schema ModuleFormat.Portable.exportsCodec entry.spec))).map
      (fun theory => rewriteAt (engineBasePremises RelationEnv.empty)
        theory.toLanguageDef 1 (EdgeListToMatrixLanguageDef.statePattern source)) =
      some ((EdgeListToMatrixLanguageDef.step? source).toList.map EdgeListToMatrixLanguageDef.statePattern) := by
  rw [read_moduleText_export]
  exact congrArg some (rootSuccessors_state source)

theorem wrong_schema_refused :
    ModuleFormat.Portable.readTheory? "different/1" ModuleFormat.Portable.exportsCodec sourceText =
      none :=
  ModuleFormat.Portable.readTheory_renderTheory_otherSchema _ _ _ _ _ (by decide)

/- Executable refusal control at the existing character-reader boundary. -/
#guard (ModuleFormat.Portable.readTheory? schema ModuleFormat.Portable.exportsCodec "!(run)").isNone

/-! ## Occurrence-preserving positive and missing-rule negative controls -/

namespace Controls

open EdgeList.Canary

def edge : EdgeList.Edge 3 := ⟨v0, v1⟩
def initial : EdgeListToMatrixLanguageDef.State 3 := .active [edge, edge] .empty
def afterFirst : EdgeListToMatrixLanguageDef.State 3 := .active [edge] (.setSymmetric .empty edge)
def afterSecond : EdgeListToMatrixLanguageDef.State 3 :=
  .active [] (.setSymmetric (.setSymmetric .empty edge) edge)

theorem duplicate_occurrences_have_two_writes :
    rootSuccessors (EdgeListToMatrixLanguageDef.statePattern initial) = [EdgeListToMatrixLanguageDef.statePattern afterFirst] ∧
      rootSuccessors (EdgeListToMatrixLanguageDef.statePattern afterFirst) = [EdgeListToMatrixLanguageDef.statePattern afterSecond] ∧
      (constructionPath [edge, edge] .empty).length = 3 := by
  constructor
  · exact rootSuccessors_state initial
  constructor
  · exact rootSuccessors_state afterFirst
  · exact constructionPath_length _ _

/-- Repeated occurrences remain distinct in the construction despite identical
extensional matrix output after the second insertion. -/
theorem repeated_write_same_denotation :
    (EdgeListToMatrixLanguageDef.MatrixExpr.setSymmetric (.setSymmetric .empty edge) edge).denote =
      (EdgeListToMatrixLanguageDef.MatrixExpr.setSymmetric .empty edge).denote := by
  apply EdgeListToMatrixGSLT.matrix_ext
  funext source target
  simp [EdgeListToMatrixLanguageDef.MatrixExpr.denote, EdgeListToMatrixGSLT.insertOccurrence,
    AdjacencyMatrix.empty]

/-- Preserve the complete signature and finalization rule but remove Write. -/
def withoutWrite : LanguageDef :=
  { quoted.toLanguageDef with «rewrites» := [EdgeListToMatrixLanguageDef.finishRule] }

theorem missing_write_stalls :
    rewriteAt (engineBasePremises RelationEnv.empty) withoutWrite 1
      (EdgeListToMatrixLanguageDef.statePattern initial) = [] := by
  simp [OSLF.MeTTaIL.Reflection.ReflectionProfile.empty,
    matchingPresentationForRule?, reflectiveRuleForRule?,
    withoutWrite, quoted_core_eq, rewriteAt, EdgeListToMatrixLanguageDef.finishRule,
    initial, EdgeListToMatrixLanguageDef.statePattern,
    EdgeListToMatrixLanguageDef.edgesPattern, EdgeListToMatrixLanguageDef.edgePattern,
    EdgeListToMatrixLanguageDef.matrixPattern, applyRuleUsing,
    matchPatternForRule, matchPatternForRuleUsing,
    Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
    Mettapedia.OSLF.MeTTaIL.Match.matchArgs]

theorem same_signature_different_execution :
    withoutWrite.types = quoted.types ∧ withoutWrite.terms = quoted.terms ∧
      rewriteAt (engineBasePremises RelationEnv.empty) withoutWrite 1
          (EdgeListToMatrixLanguageDef.statePattern initial) ≠ rootSuccessors (EdgeListToMatrixLanguageDef.statePattern initial) := by
  refine ⟨rfl, rfl, ?_⟩
  rw [missing_write_stalls, duplicate_occurrences_have_two_writes.1]
  simp

end Controls

end Mettapedia.GraphTheory.Representation.EdgeListToMatrixModule
