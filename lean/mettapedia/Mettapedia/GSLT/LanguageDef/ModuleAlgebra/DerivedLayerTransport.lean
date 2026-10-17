import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.ProductCategoryElaboration
import Mettapedia.GSLT.LanguageDef.ExtensionAlongMorphisms
import Mettapedia.GSLT.LanguageDef.MapLanguageDef
import Mettapedia.GSLT.LanguageDef.StructuralRenamingSemantics

/-!
# Executable derived fields under change of core

The existing tuple and named-substitution layers use the same transport
interface as other coGSLT layers. Transport changes their actual sort and
constructor references, not only their decoration's base. Compilation commutes
with that action. No injectivity is needed for this algebraic square; admission,
freshness and conservativity have additional hypotheses and are not inferred
from transport alone.

The combined artifact contains an extended core and compiled substitution
patterns. Its observation is explicitly the old top-level rewrite result list
and the ordered results of executing the substitutions. Tuple typing is the
separate bidirectional theorem in ProductCategoryElaboration. This observation
does not assert contextual, modulo-equations, native-C or parser adequacy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.DerivedLayerTransport

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.ExtensionAlongMorphisms
open Mettapedia.GSLT.LanguageDef.StructuralRenamingSemantics


def mapTuple (symbols : LanguageDefSymbolMap) (declaration : ProductCategoryElaboration.Declaration) :
    ProductCategoryElaboration.Declaration :=
  ⟨symbols.sort declaration.sort, symbols.constructor declaration.constructor,
    declaration.components.map symbols.sort⟩

def mapNamed (symbols : LanguageDefSymbolMap) (declaration : NamedSubstitutionElaboration.Declaration) :
    NamedSubstitutionElaboration.Declaration :=
  ⟨declaration.target, mapPattern symbols declaration.body,
    mapPattern symbols declaration.replacement⟩

@[simp] theorem mapTuple_id (declaration : ProductCategoryElaboration.Declaration) :
    mapTuple LanguageDefSymbolMap.id declaration = declaration := by
  cases declaration
  simp [mapTuple, LanguageDefSymbolMap.id]

@[simp] theorem mapTuple_comp (first second : LanguageDefSymbolMap)
    (declaration : ProductCategoryElaboration.Declaration) :
    mapTuple (first.comp second) declaration = mapTuple second (mapTuple first declaration) := by
  cases declaration
  simp [mapTuple, LanguageDefSymbolMap.comp, List.map_map]

@[simp] theorem mapNamed_id (declaration : NamedSubstitutionElaboration.Declaration) :
    mapNamed LanguageDefSymbolMap.id declaration = declaration := by
  cases declaration
  simp [mapNamed]

@[simp] theorem mapNamed_comp (first second : LanguageDefSymbolMap)
    (declaration : NamedSubstitutionElaboration.Declaration) :
    mapNamed (first.comp second) declaration = mapNamed second (mapNamed first declaration) := by
  cases declaration
  simp [mapNamed]

def tupleTransport : CompositionalTransport
    (ProductCategoryElaboration.tupleLayer.reindex ValidatedLanguageDef.language) where
  map morphism declarations := declarations.map (mapTuple morphism.symbols)
  map_id _ declarations := by
    change List ProductCategoryElaboration.Declaration at declarations
    change declarations.map (mapTuple LanguageDefSymbolMap.id) = declarations
    calc
      _ = declarations.map _root_.id := List.map_congr_left fun declaration _ => mapTuple_id declaration
      _ = declarations := List.map_id declarations
  map_comp earlier later declarations := by
    change List ProductCategoryElaboration.Declaration at declarations
    change declarations.map (mapTuple (earlier.symbols.comp later.symbols)) = _
    simp [List.map_map, Function.comp_def]
  map_empty _ := rfl
  map_merge _ first second := by
    change List ProductCategoryElaboration.Declaration at first second
    change some (_ ++ _) = some ((first ++ second).map _)
    rw [List.map_append]

def namedTransport : CompositionalTransport
    (NamedSubstitutionElaboration.namedLayer.reindex ValidatedLanguageDef.language) where
  map morphism declarations := declarations.map (mapNamed morphism.symbols)
  map_id _ declarations := by
    change List NamedSubstitutionElaboration.Declaration at declarations
    change declarations.map (mapNamed LanguageDefSymbolMap.id) = declarations
    calc
      _ = declarations.map _root_.id := List.map_congr_left fun declaration _ => mapNamed_id declaration
      _ = declarations := List.map_id declarations
  map_comp earlier later declarations := by
    change List NamedSubstitutionElaboration.Declaration at declarations
    change declarations.map (mapNamed (earlier.symbols.comp later.symbols)) = _
    simp [List.map_map, Function.comp_def]
  map_empty _ := rfl
  map_merge _ first second := by
    change List NamedSubstitutionElaboration.Declaration at first second
    change some (_ ++ _) = some ((first ++ second).map _)
    rw [List.map_append]

/-- The same product transport used by other authored extension languages. -/
def combinedTransport := tupleTransport.product namedTransport

theorem map_parameters (symbols : LanguageDefSymbolMap) (index : Nat)
    (components : List String) :
    (ProductCategoryElaboration.parametersFrom index components).map (mapTermParam symbols) =
      ProductCategoryElaboration.parametersFrom index (components.map symbols.sort) := by
  induction components generalizing index with
  | nil => rfl
  | cons component rest ih =>
      simp [ProductCategoryElaboration.parametersFrom, mapTermParam, mapTypeExpr, ih]

private theorem parameter_names (symbols : LanguageDefSymbolMap) (index : Nat)
    (components : List String) :
    (ProductCategoryElaboration.parametersFrom index (components.map symbols.sort)).map TermParam.bodyName =
      (ProductCategoryElaboration.parametersFrom index components).map TermParam.bodyName := by
  induction components generalizing index with
  | nil => rfl
  | cons component rest ih => simp [ProductCategoryElaboration.parametersFrom, TermParam.bodyName, ih]

theorem map_tupleRule (symbols : LanguageDefSymbolMap) (declaration : ProductCategoryElaboration.Declaration) :
    mapGrammarRule symbols (ProductCategoryElaboration.tupleRule declaration) =
      ProductCategoryElaboration.tupleRule (mapTuple symbols declaration) := by
  have names := congrArg (List.map SyntaxItem.nonTerminal)
    (parameter_names symbols 0 declaration.components)
  simp only [List.map_map] at names
  simp only [mapGrammarRule, ProductCategoryElaboration.tupleRule, mapTuple, map_parameters]
  congr 1
  exact names.symm

theorem map_tuple_compile (symbols : LanguageDefSymbolMap) (core : LanguageDef)
    (declaration : ProductCategoryElaboration.Declaration) :
    mapLanguageDef symbols (ProductCategoryElaboration.compile core declaration) =
      ProductCategoryElaboration.compile (mapLanguageDef symbols core) (mapTuple symbols declaration) := by
  simp [mapLanguageDef, ProductCategoryElaboration.compile, List.map_append, mapTypeDecl,
    TypeDecl.plain, mapTuple, map_tupleRule]

theorem map_closeFVar (symbols : LanguageDefSymbolMap) (depth : Nat)
    (name : String) (body : Pattern) :
    mapPattern symbols (closeFVar depth name body) =
      closeFVar depth name (mapPattern symbols body) := by
  induction body using Pattern.inductionOn generalizing depth with
  | hbvar index => simp [closeFVar, mapPattern]
  | hfvar varName => simp only [closeFVar, mapPattern]; split <;> rfl
  | happly constructor arguments ih =>
      simp only [closeFVar, mapPattern, mapPatternList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun argument member => ih argument member depth
  | hlambda binder body ih => simp [closeFVar, mapPattern, ih]
  | hmultiLambda arity binders body ih => simp [closeFVar, mapPattern, ih]
  | hsubst body replacement ihBody ihReplacement =>
      simp [closeFVar, mapPattern, ihBody, ihReplacement]
  | hcollection kind elements rest ih =>
      simp only [closeFVar, mapPattern, mapPatternList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun element member => ih element member depth

theorem map_named_compile (symbols : LanguageDefSymbolMap) (declaration : NamedSubstitutionElaboration.Declaration) :
    mapPattern symbols (NamedSubstitutionElaboration.compileDeclaration declaration) =
      NamedSubstitutionElaboration.compileDeclaration (mapNamed symbols declaration) := by
  simp [NamedSubstitutionElaboration.compileDeclaration, NamedSubstitutionElaboration.abstractNamedAt, mapNamed, mapPattern,
    map_closeFVar, mapPattern_liftBVars]

theorem map_named_observation (symbols : LanguageDefSymbolMap)
    (declaration : NamedSubstitutionElaboration.Declaration) :
    mapPattern symbols (NamedSubstitutionElaboration.observeDeclaration declaration) =
      NamedSubstitutionElaboration.observeDeclaration (mapNamed symbols declaration) := by
  rw [← NamedSubstitutionElaboration.compileDeclaration_adequate, ← NamedSubstitutionElaboration.compileDeclaration_adequate]
  change mapPattern symbols (instantiateBVar _ _) = instantiateBVar _ _
  rw [mapPattern_instantiateBVar]
  simp [NamedSubstitutionElaboration.abstractNamedAt, mapNamed, map_closeFVar, mapPattern_liftBVars]

def compileTuples (core : LanguageDef) (declarations : List ProductCategoryElaboration.Declaration) : LanguageDef :=
  declarations.foldl ProductCategoryElaboration.compile core

theorem compileTuples_rewrites (core : LanguageDef) (declarations : List ProductCategoryElaboration.Declaration) :
    (compileTuples core declarations).rewrites = core.rewrites := by
  induction declarations generalizing core with
  | nil => rfl
  | cons declaration rest ih => exact ih (ProductCategoryElaboration.compile core declaration)

theorem compileTuples_old_steps (core : LanguageDef) (declarations : List ProductCategoryElaboration.Declaration)
    (term : Pattern) :
    rewriteStep (compileTuples core declarations) term = rewriteStep core term := by
  simp only [rewriteStep, compileTuples_rewrites]

theorem map_compileTuples (symbols : LanguageDefSymbolMap) (core : LanguageDef)
    (declarations : List ProductCategoryElaboration.Declaration) :
    mapLanguageDef symbols (compileTuples core declarations) =
      compileTuples (mapLanguageDef symbols core) (declarations.map (mapTuple symbols)) := by
  induction declarations generalizing core with
  | nil => rfl
  | cons declaration rest ih =>
      simpa [compileTuples, map_tuple_compile] using ih (ProductCategoryElaboration.compile core declaration)

def tupleRealization : Mettapedia.GSLT.Realization
    (fun _ : LanguageDef => List ProductCategoryElaboration.Declaration)
    (fun _ => LanguageDef) (fun _ => Pattern → List Pattern) where
  compile := compileTuples
  observeSource core _ := rewriteStep core
  observeArtifact _ artifact := rewriteStep artifact
  adequate := by
    intro core declarations
    funext term
    exact compileTuples_old_steps core declarations term

/-- The existing coGSLT product derives the combined executable realization.
Its artifact genuinely adds tuple declarations and compiles substitutions. -/
def realization := ProductCategoryElaboration.tupleLayer.productRealization
  NamedSubstitutionElaboration.namedLayer tupleRealization NamedSubstitutionElaboration.realization

theorem compilation_transport (symbols : LanguageDefSymbolMap) (core : LanguageDef)
    (tuples : List ProductCategoryElaboration.Declaration) (named : List NamedSubstitutionElaboration.Declaration) :
    realization.compile (mapLanguageDef symbols core)
        (tuples.map (mapTuple symbols), named.map (mapNamed symbols)) =
      (mapLanguageDef symbols (realization.compile core (tuples, named)).1,
       (realization.compile core (tuples, named)).2.map (mapPattern symbols)) := by
  change (compileTuples (mapLanguageDef symbols core) (tuples.map (mapTuple symbols)),
    (named.map (mapNamed symbols)).map NamedSubstitutionElaboration.compileDeclaration) =
      (mapLanguageDef symbols (compileTuples core tuples),
       (named.map NamedSubstitutionElaboration.compileDeclaration).map (mapPattern symbols))
  simp only [← map_compileTuples, List.map_map]
  congr 1
  exact List.map_congr_left fun declaration _ => (map_named_compile symbols declaration).symm

theorem old_may_iff (core : LanguageDef) (tuples : List ProductCategoryElaboration.Declaration)
    (term : Pattern) (property : Pattern → Prop) :
    (∃ result ∈ rewriteStep (compileTuples core tuples) term, property result) ↔
      ∃ result ∈ rewriteStep core term, property result := by
  rw [compileTuples_old_steps]

theorem old_must_iff (core : LanguageDef) (tuples : List ProductCategoryElaboration.Declaration)
    (term : Pattern) (property : Pattern → Prop) :
    (∀ result ∈ rewriteStep (compileTuples core tuples) term, property result) ↔
      ∀ result ∈ rewriteStep core term, property result := by
  rw [compileTuples_old_steps]

namespace Controls

private def renamed : LanguageDefSymbolMap :=
  { LanguageDefSymbolMap.id with
    sort := (fun name => "Target:" ++ name)
    constructor := (fun name => "Target:" ++ name) }

theorem transport_changes_references :
    (mapTuple renamed ⟨"Pair", "PairOf", ["Nat", "Nat"]⟩).components =
      ["Target:Nat", "Target:Nat"] ∧
    NamedSubstitutionElaboration.observeDeclaration (mapNamed renamed
      ⟨"x", .lambda none (.apply "K" [.fvar "x", .bvar 0]), .bvar 0⟩) =
      .lambda none (.apply "Target:K" [.bvar 1, .bvar 0]) := by
  constructor
  · rfl
  · simp [NamedSubstitutionElaboration.observeDeclaration, mapNamed, mapPattern, mapPatternList,
      NamedSubstitutionElaboration.substituteNamedAt, liftBVars, renamed]

theorem tuple_artifact_adds_a_constructor (core : LanguageDef) :
    (compileTuples core [⟨"Pair", "PairOf", ["Nat", "Nat"]⟩]).terms.length =
      core.terms.length + 1 := by
  simp [compileTuples, ProductCategoryElaboration.compile]

/-- A noninjective sort map may destroy freshness: the transport square is
not a certificate of admission or conservativity of arbitrary interpretations. -/
theorem transport_does_not_imply_freshness :
    "Pair" ≠ "Nat" ∧
    ({ LanguageDefSymbolMap.id with sort := fun _ => "Collapsed" } :
      LanguageDefSymbolMap).sort "Pair" =
      ({ LanguageDefSymbolMap.id with sort := fun _ => "Collapsed" } :
        LanguageDefSymbolMap).sort "Nat" := by decide

end Controls

#print axioms tupleTransport
#print axioms namedTransport
#print axioms map_tuple_compile
#print axioms map_named_observation
#print axioms realization
#print axioms compilation_transport
#print axioms old_must_iff

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.DerivedLayerTransport
