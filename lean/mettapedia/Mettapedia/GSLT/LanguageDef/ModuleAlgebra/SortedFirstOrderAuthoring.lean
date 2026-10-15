import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation
import Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat

/-!
# Typed inference declarations over the shared module quotation

The `inferenceTheory!` quotation reuses every `moduleTheory!` core block.
`Judgments` names provable sorts; `Inferences` adds ordered premises and
explicitly typed formals. These are independent compositional layers over
the same `LanguageDef`, rather than another language syntax carrier.

Nullary names are resolved after assembling the full syntax, with rule
formals protected from resolution. Quotation and layer assembly do not
assert semantic admission. The typed first-order checker supplies that
separate boundary. This extension is a Lean authoring interface; it does
not extend the upstream Rust byte parser for `.module` files.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SortedFirstOrderAuthoring

open Lean
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open SortedFirstOrderRules UpstreamTheoryQuotation

def ruleCodec : ExactDeclarationCodec Rule Rule where
  encode := id
  decode := id
  decode_encode := fun _ => rfl
  encode_decode := fun _ => rfl

def inferenceLayer : CompositionalLayer LanguageDef :=
  exportLayer.product ((CompositionalLayer.ofCodec LanguageDef exportCodec).product
    (CompositionalLayer.ofCodec LanguageDef ruleCodec))

abbrev QuotedInferenceTheory := ExtendedLanguageDef inferenceLayer

def attach (syntaxTheory : QuotedTheory) (judgments : List String) (rules : List Rule) :
    QuotedInferenceTheory where
  toLanguageDef := syntaxTheory.toLanguageDef
  extension := (syntaxTheory.extension, (judgments, rules))

def core (source : QuotedInferenceTheory) : QuotedTheory :=
  ofCore source.toLanguageDef source.extension.1

def judgmentSorts (source : QuotedInferenceTheory) : List String := source.extension.2.1

def resolveRule (language : LanguageDef) (rule : Rule) : Rule :=
  { rule with row := { rule.row with
      premises := rule.row.premises.map (fun pattern =>
        pattern.resolveNullary language.nullaryLabels rule.row.vars)
      conclusion := rule.row.conclusion.resolveNullary language.nullaryLabels rule.row.vars } }

def rules (source : QuotedInferenceTheory) : List Rule :=
  source.extension.2.2.map (resolveRule source.toLanguageDef)

def assemble (displayName : String) (sources : List QuotedInferenceTheory) : QuotedInferenceTheory :=
  attach (UpstreamTheoryQuotation.assemble displayName (sources.map core))
    (sources.flatMap judgmentSorts) (sources.flatMap (fun source => source.extension.2.2))

private def renderList (values : List String) : String :=
  values.foldr (fun first rest => "(LCons " ++ first ++ " " ++ rest ++ ")") "LNil"

/-- Typed rows retain the existing inference-schema wire and its Pattern codec. -/
def renderRule? (rule : Rule) : Option String := do
  let declaredTypes ← rule.variableTypes.mapM CanonicalWire.renderTypeExpr?
  let row := InferenceCettaWire.CettaTerm.render
    (InferenceCettaWire.encodeRule rule.row.toSchema)
  pure ("(SortedRuleV1 " ++ row ++ " " ++ renderList declaredTypes ++ ")")

/-- The canonical core wire and independent authoring layers remain separate.
No reduced constructor inventory replaces the complete LanguageDef payload. -/
def render? (source : QuotedInferenceTheory) : Option String := do
  let language ← CanonicalWire.renderLanguage? source.toLanguageDef
  let inferenceRows ← (rules source).mapM renderRule?
  pure ("(GSLTInferenceTheoryWireV1\n  " ++ language ++ "  " ++
    renderList (source.extension.1.map reprStr) ++ "\n  " ++
    renderList ((judgmentSorts source).map reprStr) ++ "\n  " ++
    renderList inferenceRows ++ ")")

theorem assembled_core (displayName : String) (sources : List QuotedInferenceTheory) :
    (assemble displayName sources).toLanguageDef =
      (UpstreamTheoryQuotation.assemble displayName (sources.map core)).toLanguageDef := rfl

/-- Formals and premises retain authored order through layer composition. -/
theorem assembled_rules (displayName : String) (sources : List QuotedInferenceTheory) :
    rules (assemble displayName sources) =
      (sources.flatMap (fun source => source.extension.2.2)).map
        (resolveRule (assemble displayName sources).toLanguageDef) := rfl

declare_syntax_cat moduleInferenceDecl
declare_syntax_cat inferenceTheoryBlock

scoped syntax ident "(" langDefTypeBinding,* ")" ":"
  "[" langDefPattern,* "]" "=>" langDefPattern ";" : moduleInferenceDecl
scoped syntax moduleCoreBlock : inferenceTheoryBlock
scoped syntax "Judgments" "{" (ident ";")* "}" : inferenceTheoryBlock
scoped syntax "Inferences" "{" moduleInferenceDecl* "}" : inferenceTheoryBlock

def ofTypedFormals (label : String) (formals : List (String × TypeExpr))
    (premises : List Pattern) (conclusion : Pattern) : Rule where
  row := { id := label, vars := formals.map Prod.fst, premises := premises, conclusion := conclusion }
  variableTypes := formals.map Prod.snd

private def expandInference : TSyntax `moduleInferenceDecl → MacroM (TSyntax `term)
  | `(moduleInferenceDecl| $label:ident ($formals:langDefTypeBinding,*) :
      [$premises:langDefPattern,*] => $conclusion:langDefPattern ;) => do
      let ruleName : TSyntax `term := ⟨Syntax.mkStrLit label.getId.toString⟩
      let formalBindings ← formals.getElems.mapM expandTypeBinding
      let premises' ← premises.getElems.mapM expandPattern
      let conclusion' ← expandPattern conclusion
      `(ofTypedFormals $ruleName [$formalBindings,*] [$premises',*] $conclusion')
  | other => Macro.throwErrorAt other "unsupported typed inference declaration"

scoped macro "inferenceTheory!" "Theory" theoryName:ident "(" ")"
    "{" blocks:inferenceTheoryBlock* "}" : term => do
  let mut coreBlocks : Array (TSyntax `moduleCoreBlock) := #[]
  let mut judgments : Array (TSyntax `term) := #[]
  let mut ruleRows : Array (TSyntax `term) := #[]
  for block in blocks do
    match block with
    | `(inferenceTheoryBlock| $coreBlock:moduleCoreBlock) => coreBlocks := coreBlocks.push coreBlock
    | `(inferenceTheoryBlock| Judgments { $[$names:ident ;]* }) =>
        judgments := judgments ++ names.map (fun sortName => ⟨Syntax.mkStrLit sortName.getId.toString⟩)
    | `(inferenceTheoryBlock| Inferences { $rows:moduleInferenceDecl* }) =>
        ruleRows := ruleRows ++ (← rows.mapM expandInference)
    | other => Macro.throwErrorAt other "unsupported typed theory block"
  `(attach (moduleTheory! Theory $theoryName:ident () { $coreBlocks:moduleCoreBlock* })
    [$judgments,*] [$ruleRows,*])

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SortedFirstOrderAuthoring
