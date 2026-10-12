import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NativeAuthoring
import Mettapedia.GSLT.LanguageDef.ExtendedLanguageDef

/-!
# Native quotations of upstream theory-builder blocks

`moduleTheory! Theory T() { ... }` quotes the supported closed-theory fragment
of the frozen upstream module surface into the existing native authoring DSL.
The `Types`, `Terms`, `Equations`, and `Rewrites` blocks retain the complete core
rows. Simple `Exports` declarations are an independent compositional layer over
that same core; they are not silently treated as sort declarations.

Source: F1R3FLY-io/mettail-rust, commit
`8c1bb3b0ef3890406e375c2c5387dc9a3cdf0439`,
`mettail-elab/examples/modules/UnivAlg.module` and `Rholang.module`.

This is a Lean syntax quotation, not a verified byte parser for `.module`.
Imports, parameterized theory expressions, replacements, renamed exports,
generative application, and ordered-builder admission remain separate source
boundaries. Unsupported syntax has no fallback elaboration.

`englishTheory!` is a sentence-style quotation of the same declarations. It
borrows the controlled-English authoring approach of Adam Dingle's Natural Lean
(`https://github.com/medovina/natural_lean`), without using its implementation or
proof automation. Constructor parameters, notation atoms, patterns, and guards
reuse the existing native DSL categories. Equations declare the presentation;
they do not assert that Lean has proved an equation about an external model.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation

open Lean
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

/-- Visibility declarations are authored independently from the core. -/
def exportCodec : ExactDeclarationCodec String String where
  encode := id
  decode := id
  decode_encode := fun _ => rfl
  encode_decode := fun _ => rfl

def exportLayer : CompositionalLayer LanguageDef :=
  CompositionalLayer.ofCodec LanguageDef exportCodec

abbrev QuotedTheory := ExtendedLanguageDef exportLayer

def ofCore (language : LanguageDef) (exports : List String) : QuotedTheory where
  toLanguageDef := language
  extension := exports

def exportedNames (theory : QuotedTheory) : List String := theory.extension

/-- Simple exported names must name actual declared sorts. -/
def exportsValid (theory : QuotedTheory) : Bool :=
  theory.extension.all (fun exported => theory.typeNames.contains exported)

def admit? (theory : QuotedTheory) : Option QuotedTheory :=
  if theory.validate.isEmpty && exportsValid theory then some theory else none

theorem admit_isSome_iff (theory : QuotedTheory) :
    (admit? theory).isSome = true ↔ theory.validate.isEmpty = true ∧ exportsValid theory = true := by
  simp [admit?, Bool.and_eq_true]

/-- Independent fragments are assembled once; this is not the shared-origin
join of complete inherited theories. Export order is retained. -/
def assemble (langName : String) (fragments : List QuotedTheory) : QuotedTheory :=
  ofCore (NativeAuthoring.assemble langName (fragments.map (·.toLanguageDef)))
    (fragments.flatMap exportedNames)

theorem assemble_core (langName : String) (fragments : List QuotedTheory) :
    (assemble langName fragments).toLanguageDef =
      NativeAuthoring.assemble langName (fragments.map (·.toLanguageDef)) := rfl

theorem assemble_exports (langName : String) (fragments : List QuotedTheory) :
    (assemble langName fragments).extension = fragments.flatMap exportedNames := rfl

def changeNotation (tokens : String ≃ String) (theory : QuotedTheory) : QuotedTheory :=
  ofCore (Parsing.GrammarPresentationTransport.mapLanguage tokens theory.toLanguageDef)
    theory.extension

@[simp] theorem changeNotation_core (tokens : String ≃ String) (theory : QuotedTheory) :
    (changeNotation tokens theory).toLanguageDef =
      Parsing.GrammarPresentationTransport.mapLanguage tokens theory.toLanguageDef := rfl

@[simp] theorem changeNotation_exports (tokens : String ≃ String) (theory : QuotedTheory) :
    exportedNames (changeNotation tokens theory) = exportedNames theory := rfl

theorem changeNotation_assemble (tokens : String ≃ String) (langName : String)
    (fragments : List QuotedTheory) :
    changeNotation tokens (assemble langName fragments) =
      assemble langName (fragments.map (changeNotation tokens)) := by
  change ofCore
      (Parsing.GrammarPresentationTransport.mapLanguage tokens
        (NativeAuthoring.assemble langName (fragments.map (·.toLanguageDef))))
      (fragments.flatMap exportedNames) =
    ofCore
      (NativeAuthoring.assemble langName
        ((fragments.map (changeNotation tokens)).map (·.toLanguageDef)))
      ((fragments.map (changeNotation tokens)).flatMap exportedNames)
  apply congrArg₂ ofCore
  · rw [NativeAuthoring.mapLanguage_assemble]
    congr 1
    simp only [List.map_map, Function.comp_def, changeNotation_core]
  · simp only [List.flatMap_map, changeNotation_exports]

theorem export_quote_exact (theory : QuotedTheory) :
    exportLayer.elaborate theory.toLanguageDef theory.authoredSource = some theory.extension :=
  theory.elaborate_authoredSource

/-! ## Quotation syntax, reusing all existing term and binding macros -/

declare_syntax_cat moduleCoreBlock
declare_syntax_cat moduleEquationDecl
declare_syntax_cat moduleRewriteDecl

scoped syntax langDefPattern "==" langDefPattern ";" : moduleEquationDecl
scoped syntax "if" langDefPremise "then" langDefPattern "==" langDefPattern ";" : moduleEquationDecl
scoped syntax ident ":" langDefPattern "~>" langDefPattern ";" : moduleRewriteDecl
scoped syntax ident ":" "if" langDefPremise "then" langDefPattern "~>" langDefPattern ";" : moduleRewriteDecl

scoped syntax "Types" "{" (langDefTypeDecl ";")* "}" : moduleCoreBlock
scoped syntax "Exports" "{" (ident ";")* "}" : moduleCoreBlock
scoped syntax "Terms" "{" langDefTermDecl* "}" : moduleCoreBlock
scoped syntax "Equations" "{" moduleEquationDecl* "}" : moduleCoreBlock
scoped syntax "Rewrites" "{" moduleRewriteDecl* "}" : moduleCoreBlock

private def equationSyntax (label : TSyntax `ident) : TSyntax `moduleEquationDecl →
    MacroM (TSyntax `langDefEquationDecl)
  | `(moduleEquationDecl| $left:langDefPattern == $right:langDefPattern ;) =>
      `(langDefEquationDecl| $label:ident . |- $left:langDefPattern = $right:langDefPattern ;)
  | `(moduleEquationDecl| if $premise:langDefPremise then $left:langDefPattern == $right:langDefPattern ;) =>
      `(langDefEquationDecl| $label:ident . | $premise:langDefPremise |- $left:langDefPattern = $right:langDefPattern ;)
  | other => Macro.throwErrorAt other "unsupported upstream equation quotation"

private def rewriteSyntax : TSyntax `moduleRewriteDecl → MacroM (TSyntax `langDefRewriteDecl)
  | `(moduleRewriteDecl| $label:ident : $left:langDefPattern ~> $right:langDefPattern ;) =>
      `(langDefRewriteDecl| $label:ident . |- $left:langDefPattern ~> $right:langDefPattern ;)
  | `(moduleRewriteDecl| $label:ident : if $premise:langDefPremise then $left:langDefPattern ~> $right:langDefPattern ;) =>
      `(langDefRewriteDecl| $label:ident . | $premise:langDefPremise |- $left:langDefPattern ~> $right:langDefPattern ;)
  | other => Macro.throwErrorAt other "unsupported upstream rewrite quotation"

scoped macro "moduleTheory!" "Theory" theoryName:ident "(" ")" "{" blocks:moduleCoreBlock* "}" : term => do
  let mut typeRows : Array (TSyntax `langDefTypeDecl) := #[]
  let mut termRows : Array (TSyntax `langDefTermDecl) := #[]
  let mut equationRows : Array (TSyntax `langDefEquationDecl) := #[]
  let mut rewriteRows : Array (TSyntax `langDefRewriteDecl) := #[]
  let mut exportRows : Array (TSyntax `term) := #[]
  for block in blocks do
    match block with
    | `(moduleCoreBlock| Types { $[$declarations:langDefTypeDecl ;]* }) =>
        typeRows := typeRows ++ declarations
    | `(moduleCoreBlock| Exports { $[$names:ident ;]* }) =>
        exportRows := exportRows ++ names.map (fun identifier => ⟨Syntax.mkStrLit identifier.getId.toString⟩)
    | `(moduleCoreBlock| Terms { $declarations:langDefTermDecl* }) =>
        termRows := termRows ++ declarations
    | `(moduleCoreBlock| Equations { $declarations:moduleEquationDecl* }) =>
        for declaration in declarations do
          let label : TSyntax `ident := ⟨mkIdent <| Name.mkSimple
            s!"{theoryName.getId}:equation:{equationRows.size}"⟩
          equationRows := equationRows.push (← equationSyntax label declaration)
    | `(moduleCoreBlock| Rewrites { $declarations:moduleRewriteDecl* }) =>
        rewriteRows := rewriteRows ++ (← declarations.mapM rewriteSyntax)
    | other => Macro.throwErrorAt other "unsupported upstream theory-builder quotation"
  let displayName : TSyntax `term := ⟨Syntax.mkStrLit theoryName.getId.toString⟩
  `(ofCore (languageDef! {
      name : $displayName
      types { $typeRows:langDefTypeDecl* }
      terms { $termRows:langDefTermDecl* }
      equations { $equationRows:langDefEquationDecl* }
      rewrites { $rewriteRows:langDefRewriteDecl* }
    }) [$exportRows,*])

/-! ## Sentence-style quotations into the same upstream declaration builder

Sentence boundaries and parameter scope are explicit. No quantifier or binding
scope is inferred from prose. The generated module blocks pass through the
single `moduleTheory!` elaborator, including its equation labels and independent
export layer. English keywords are enabled only by opening `EnglishAuthoring`.
-/

namespace EnglishAuthoring

declare_syntax_cat englishModuleSentence

scoped syntax "Declare" "the" "sort" langDefTypeDecl "." : englishModuleSentence
scoped syntax "Export" "the" "sort" ident "." : englishModuleSentence
scoped syntax "Declare" ident "returning" ident "with" "notation"
  langDefSyntaxAtom* "." : englishModuleSentence
scoped syntax "Declare" ident "taking" langDefTermParam,+ "returning" ident
  "with" "notation" langDefSyntaxAtom* "." : englishModuleSentence
scoped syntax "Assert" "that" langDefPattern "equals" langDefPattern "." : englishModuleSentence
scoped syntax "Assert" "that" "if" langDefPremise "then"
  langDefPattern "equals" langDefPattern "." : englishModuleSentence
scoped syntax "Rewrite" ident ":" langDefPattern "to" langDefPattern "." : englishModuleSentence
scoped syntax "Rewrite" ident ":" "if" langDefPremise "then"
  langDefPattern "to" langDefPattern "." : englishModuleSentence

private def englishSentenceBlock : TSyntax `englishModuleSentence → MacroM (TSyntax `moduleCoreBlock)
  | `(englishModuleSentence| Declare the sort $sortName:langDefTypeDecl .) =>
      `(moduleCoreBlock| Types { $sortName:langDefTypeDecl ; })
  | `(englishModuleSentence| Export the sort $sortName:ident .) =>
      `(moduleCoreBlock| Exports { $sortName:ident ; })
  | `(englishModuleSentence| Declare $label:ident returning $sortName:ident
        with notation $atoms:langDefSyntaxAtom* .) =>
      `(moduleCoreBlock| Terms { $label:ident . |- $atoms:langDefSyntaxAtom* : $sortName:ident ; })
  | `(englishModuleSentence| Declare $label:ident taking $parameters:langDefTermParam,*
        returning $sortName:ident with notation $atoms:langDefSyntaxAtom* .) =>
      `(moduleCoreBlock| Terms {
        $label:ident . $parameters:langDefTermParam,* |- $atoms:langDefSyntaxAtom* : $sortName:ident ; })
  | `(englishModuleSentence| Assert that $left:langDefPattern equals $right:langDefPattern .) =>
      `(moduleCoreBlock| Equations { $left:langDefPattern == $right:langDefPattern ; })
  | `(englishModuleSentence| Assert that if $premise:langDefPremise then
        $left:langDefPattern equals $right:langDefPattern .) =>
      `(moduleCoreBlock| Equations {
        if $premise:langDefPremise then $left:langDefPattern == $right:langDefPattern ; })
  | `(englishModuleSentence| Rewrite $label:ident : $left:langDefPattern to $right:langDefPattern .) =>
      `(moduleCoreBlock| Rewrites { $label:ident : $left:langDefPattern ~> $right:langDefPattern ; })
  | `(englishModuleSentence| Rewrite $label:ident : if $premise:langDefPremise then
        $left:langDefPattern to $right:langDefPattern .) =>
      `(moduleCoreBlock| Rewrites {
        $label:ident : if $premise:langDefPremise then $left:langDefPattern ~> $right:langDefPattern ; })
  | other => Macro.throwErrorAt other "unsupported English theory quotation"

scoped macro "englishTheory!" "Theory" theoryName:ident "{"
    sentences:englishModuleSentence* "}" : term => do
  let blocks ← sentences.mapM englishSentenceBlock
  `(moduleTheory! Theory $theoryName:ident () { $blocks:moduleCoreBlock* })

end EnglishAuthoring

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation
