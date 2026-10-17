import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation

/-!
# Named substitution as an authored language-definition layer

The declaration names a free variable to replace. Its independent source action
walks the existing pattern syntax, lifting a replacement under each binder.
Compilation instead weakens the original body, closes the named variable into
the new bound level, and emits the existing `Pattern.subst` constructor.
Executing that constructor is proved equal to the source action for every
pattern, including open patterns, nested substitutions and multi-binders.

Declarations remain exact authored data in a compositional coGSLT layer over the
unchanged LanguageDef. Compilation is a separate, observation-preserving
realization: it is not the identity of declarations. This layer can compose
with the existing export layer without adding primitive LanguageDef fields.

This is the resolved-pattern boundary. Resolving a source dotted path, tracking
the target binder of a captured schema variable, and validating its sort against
an assembled language are separate admission obligations. No byte-parser or
native-runtime correspondence is inferred from the result here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NamedSubstitutionElaboration

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition

/-- Independent name-directed source action. An inserted replacement retains
its ambient bound-variable references when crossing inner binders. -/
def substituteNamedAt (depth : Nat) (name : String) (replacement : Pattern) :
    Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar varName =>
      if varName == name then liftBVars 0 depth replacement else .fvar varName
  | .apply constructor arguments =>
      .apply constructor (arguments.map (substituteNamedAt depth name replacement))
  | .lambda binder body =>
      .lambda binder (substituteNamedAt (depth + 1) name replacement body)
  | .multiLambda arity binders body =>
      .multiLambda arity binders
        (substituteNamedAt (depth + arity) name replacement body)
  | .subst body nestedReplacement =>
      .subst (substituteNamedAt (depth + 1) name replacement body)
        (substituteNamedAt depth name replacement nestedReplacement)
  | .collection kind elements rest =>
      .collection kind (elements.map (substituteNamedAt depth name replacement)) rest
termination_by body => sizeOf body
decreasing_by all_goals sizeOf_pattern_dec

/-- Introduce one bound level without capturing an existing ambient index. -/
def abstractNamedAt (depth : Nat) (name : String) (body : Pattern) : Pattern :=
  closeFVar depth name (liftBVars depth 1 body)

/-- The name-directed operation reduces to the core's binder-eliminating
substitution. No closure hypothesis hides the open-term case. -/
theorem instantiate_abstract_named (depth : Nat) (name : String)
    (replacement body : Pattern) :
    instantiateBVarAt depth replacement (abstractNamedAt depth name body) =
      substituteNamedAt depth name replacement body := by
  induction body using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      by_cases inner : index < depth
      · simp [abstractNamedAt, liftBVars, closeFVar, instantiateBVarAt,
          substituteNamedAt, inner, Nat.not_le.mpr inner]
      · have outer : depth ≤ index := Nat.le_of_not_gt inner
        have notInner : ¬index + 1 < depth := by omega
        have notLevel : index + 1 ≠ depth := by omega
        simp [abstractNamedAt, liftBVars, closeFVar, instantiateBVarAt,
          substituteNamedAt, outer, notInner, notLevel]
  | hfvar varName =>
      by_cases same : varName = name
      · simp [abstractNamedAt, liftBVars, closeFVar, instantiateBVarAt,
          substituteNamedAt, same]
      · simp [abstractNamedAt, liftBVars, closeFVar, instantiateBVarAt,
          substituteNamedAt, same]
  | happly constructor arguments ih =>
      simp only [abstractNamedAt, liftBVars, liftBVarsList_eq_map, closeFVar,
        instantiateBVarAt, substituteNamedAt, List.map_map]
      congr 1
      apply List.map_congr_left
      intro argument member
      exact ih argument member depth
  | hlambda binder body ih =>
      simp only [abstractNamedAt, liftBVars, closeFVar, instantiateBVarAt,
        substituteNamedAt]
      exact congrArg (Pattern.lambda binder) (ih (depth + 1))
  | hmultiLambda arity binders body ih =>
      simp only [abstractNamedAt, liftBVars, closeFVar, instantiateBVarAt,
        substituteNamedAt]
      exact congrArg (Pattern.multiLambda arity binders) (ih (depth + arity))
  | hsubst body nestedReplacement ihBody ihReplacement =>
      simp only [abstractNamedAt, liftBVars, closeFVar, instantiateBVarAt,
        substituteNamedAt]
      exact congrArg₂ Pattern.subst (ihBody (depth + 1)) (ihReplacement depth)
  | hcollection kind elements rest ih =>
      simp only [abstractNamedAt, liftBVars, liftBVarsList_eq_map, closeFVar,
        instantiateBVarAt, substituteNamedAt, List.map_map]
      congr 1
      apply List.map_congr_left
      intro element member
      exact ih element member depth

private theorem scopedList_mem {depth : Nat} {patterns : List Pattern}
    {pattern : Pattern} (hscoped : Pattern.isWellScopedListAt depth patterns = true)
    (member : pattern ∈ patterns) : pattern.isWellScopedAt depth = true := by
  induction patterns with
  | nil => cases member
  | cons head tail ih =>
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at hscoped
      rcases List.mem_cons.mp member with same | tailMember
      · simpa only [same] using hscoped.1
      · exact ih hscoped.2 tailMember

private theorem scopedList_map {depth : Nat} {patterns : List Pattern}
    {action : Pattern → Pattern}
    (hscoped : ∀ pattern ∈ patterns, (action pattern).isWellScopedAt depth = true) :
    Pattern.isWellScopedListAt depth (patterns.map action) = true := by
  induction patterns with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, Pattern.isWellScopedListAt, Bool.and_eq_true]
      exact ⟨hscoped head (List.mem_cons.mpr (Or.inl rfl)),
        ih (fun pattern member => hscoped pattern (List.mem_cons.mpr (Or.inr member)))⟩

/-- Closing the named variable after introducing its level preserves scope. -/
theorem close_named_scoped {ambient depth : Nat} (name : String) (body : Pattern)
    (hscoped : body.isWellScopedAt (ambient + depth + 1) = true) :
    (closeFVar depth name body).isWellScopedAt (ambient + depth + 1) = true := by
  induction body using Pattern.inductionOn generalizing depth with
  | hbvar index => simpa only [closeFVar] using hscoped
  | hfvar varName =>
      simp only [closeFVar]
      split
      · simp only [Pattern.isWellScopedAt]
        exact decide_eq_true (by omega)
      · rfl
  | happly constructor arguments ih =>
      simp only [closeFVar, Pattern.isWellScopedAt] at hscoped ⊢
      exact scopedList_map fun argument member => ih argument member
        (scopedList_mem hscoped member)
  | hlambda binder body ih =>
      simp only [closeFVar, Pattern.isWellScopedAt] at hscoped ⊢
      exact ih (by simpa only [Nat.add_assoc] using hscoped)
  | hmultiLambda arity binders body ih =>
      simp only [closeFVar, Pattern.isWellScopedAt] at hscoped ⊢
      have result := ih (depth := depth + arity)
        (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hscoped)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result
  | hsubst body nestedReplacement ihBody ihReplacement =>
      simp only [closeFVar, Pattern.isWellScopedAt, Bool.and_eq_true] at hscoped ⊢
      exact ⟨ihBody (by simpa only [Nat.add_assoc] using hscoped.1),
        ihReplacement hscoped.2⟩
  | hcollection kind elements rest ih =>
      simp only [closeFVar, Pattern.isWellScopedAt] at hscoped ⊢
      exact scopedList_map fun element member => ih element member
        (scopedList_mem hscoped member)

theorem abstract_named_scoped {ambient depth : Nat} (name : String) (body : Pattern)
    (hscoped : body.isWellScopedAt (ambient + depth) = true) :
    (abstractNamedAt depth name body).isWellScopedAt (ambient + depth + 1) = true :=
  close_named_scoped name _ (liftBVars_isWellScopedAt hscoped)

/-- The independent named action preserves arbitrary ambient contexts. -/
theorem substitute_named_scoped {ambient depth : Nat} (name : String)
    (replacement body : Pattern)
    (bodyScoped : body.isWellScopedAt (ambient + depth) = true)
    (replacementScoped : replacement.isWellScopedAt ambient = true) :
    (substituteNamedAt depth name replacement body).isWellScopedAt
      (ambient + depth) = true := by
  rw [← instantiate_abstract_named depth name replacement body]
  exact instantiateBVarAt_isWellScopedAt
    (abstract_named_scoped name body bodyScoped) replacementScoped

/-- Authored declarations retain the name and both original operands. -/
structure Declaration where
  target : String
  body : Pattern
  replacement : Pattern
deriving Repr, DecidableEq

/-- The structural syntax is a triple, not the compiled core pattern. -/
abbrev DeclarationSyntax := String × Pattern × Pattern

def codec : ExactDeclarationCodec DeclarationSyntax Declaration where
  encode := fun declaration =>
    (declaration.target, declaration.body, declaration.replacement)
  decode := fun source => ⟨source.1, source.2.1, source.2.2⟩
  decode_encode := by intro declaration; cases declaration; rfl
  encode_decode := by rintro ⟨target, body, replacement⟩; rfl

/-- The existing authored-document construction supplies the equations,
empty document, concatenation and exact quotation laws. -/
def namedLayer : CompositionalLayer LanguageDef :=
  CompositionalLayer.ofCodec LanguageDef codec

/-- Compile a declaration into the existing explicit-substitution syntax. -/
def compileDeclaration (declaration : Declaration) : Pattern :=
  .subst (abstractNamedAt 0 declaration.target declaration.body)
    declaration.replacement

/-- The independent source observation. -/
def observeDeclaration (declaration : Declaration) : Pattern :=
  substituteNamedAt 0 declaration.target declaration.replacement declaration.body

/-- Execute the compiled outer substitution without inventing host actions. -/
def observeCore : Pattern → Pattern
  | .subst body replacement => instantiateBVar replacement body
  | pattern => pattern

theorem compileDeclaration_adequate (declaration : Declaration) :
    observeCore (compileDeclaration declaration) = observeDeclaration declaration :=
  instantiate_abstract_named 0 declaration.target declaration.replacement
    declaration.body

theorem compileDeclaration_scoped {ambient : Nat} (declaration : Declaration)
    (bodyScoped : declaration.body.isWellScopedAt ambient = true)
    (replacementScoped : declaration.replacement.isWellScopedAt ambient = true) :
    (compileDeclaration declaration).isWellScopedAt ambient = true := by
  change ((abstractNamedAt 0 declaration.target declaration.body).isWellScopedAt
    (ambient + 1) && declaration.replacement.isWellScopedAt ambient) = true
  rw [Bool.and_eq_true]
  constructor
  · simpa only [Nat.add_zero] using
      abstract_named_scoped (ambient := ambient) (depth := 0)
        declaration.target declaration.body
        (by simpa only [Nat.add_zero] using bodyScoped)
  · exact replacementScoped

/-- Compilation retains declaration order and multiplicity. -/
def realization : GSLT.Realization
    (fun _ : LanguageDef => List Declaration)
    (fun _ => List Pattern) (fun _ => List Pattern) where
  compile := fun _ declarations => declarations.map compileDeclaration
  observeSource := fun _ declarations => declarations.map observeDeclaration
  observeArtifact := fun _ patterns => patterns.map observeCore
  adequate := by
    intro _ declarations
    simp only [List.map_map]
    apply List.map_congr_left
    intro declaration _
    exact compileDeclaration_adequate declaration

/-- Visibility is retained as authored data; it does not execute a rewrite. -/
def exportRealization : GSLT.Realization
    (fun _ : LanguageDef => List String)
    (fun _ => List String) (fun _ => List String) :=
  GSLT.Realization.identity (fun _ exports => exports)

/-- Both field meanings compose through the existing certified product. -/
def combinedRealization :=
  namedLayer.productRealization UpstreamTheoryQuotation.exportLayer
    realization exportRealization

theorem combined_realization_adequate (core : LanguageDef)
    (declarations : List Declaration) (exports : List String) :
    combinedRealization.observeArtifact core
        (combinedRealization.compile core (declarations, exports)) =
      (declarations.map observeDeclaration, exports) :=
  combinedRealization.adequate core (declarations, exports)

/-- Compose the independently authored substitution and visibility fields
over exactly the same core, using the established product construction. -/
def withExports (core : LanguageDef) (declarations : List Declaration)
    (exports : List String) :
    ExtendedLanguageDef (namedLayer.product UpstreamTheoryQuotation.exportLayer) :=
  ExtendedLanguageDef.ofProduct core namedLayer UpstreamTheoryQuotation.exportLayer
    declarations exports

theorem withExports_core (core : LanguageDef) (declarations : List Declaration)
    (exports : List String) :
    (withExports core declarations exports).toLanguageDef = core := rfl

theorem withExports_quote (core : LanguageDef) (declarations : List Declaration)
    (exports : List String) :
    (namedLayer.product UpstreamTheoryQuotation.exportLayer).elaborate core
        (withExports core declarations exports).authoredSource =
      some (declarations, exports) :=
  (withExports core declarations exports).elaborate_authoredSource

/-! ## Scope and representation controls -/

namespace Controls

/-- An open replacement remains ambient beneath an inner binder. -/
theorem open_replacement_under_binder :
    observeCore (compileDeclaration
      ⟨"x", .lambda none (.apply "Pair" [.bvar 0, .fvar "x"]), .bvar 0⟩) =
      .lambda none (.apply "Pair" [.bvar 0, .bvar 1]) := by
  rw [compileDeclaration_adequate]
  simp [observeDeclaration, substituteNamedAt, liftBVars]

/-- A name in display metadata does not capture a free replacement name. -/
theorem display_name_does_not_capture :
    observeCore (compileDeclaration
      ⟨"x", .lambda (some "y") (.fvar "x"), .fvar "y"⟩) =
      .lambda (some "y") (.fvar "y") := by
  rw [compileDeclaration_adequate]
  simp [observeDeclaration, substituteNamedAt, liftBVars]

/-- Both variables of a multi-binder stay fixed; the ambient replacement
crosses both levels. -/
theorem multi_binder_preserves_ambient_reference :
    observeCore (compileDeclaration
      ⟨"x", .multiLambda 2 [] (.apply "Triple" [.bvar 1, .bvar 0, .fvar "x"]),
        .bvar 0⟩) =
      .multiLambda 2 [] (.apply "Triple" [.bvar 1, .bvar 0, .bvar 2]) := by
  rw [compileDeclaration_adequate]
  simp [observeDeclaration, substituteNamedAt, liftBVars]

/-- The body of an already explicit substitution has one additional local
level, while its replacement remains in the outer context. -/
theorem nested_substitution_retains_both_contexts :
    observeCore (compileDeclaration
      ⟨"x", .subst (.apply "Pair" [.bvar 0, .fvar "x"]) (.fvar "x"),
        .bvar 0⟩) =
      .subst (.apply "Pair" [.bvar 0, .bvar 1]) (.bvar 0) := by
  rw [compileDeclaration_adequate]
  simp [observeDeclaration, substituteNamedAt, liftBVars]

/-- Omitting weakening captures an ambient variable even if the target
name never occurs. This is a negative control on the tempting short encoding. -/
theorem closing_without_weakening_is_wrong :
    instantiateBVar (.fvar "replacement") (closeFVar 0 "x" (.bvar 0)) ≠
      substituteNamedAt 0 "x" (.fvar "replacement") (.bvar 0) := by
  simp [instantiateBVar, instantiateBVarAt, closeFVar, liftBVars,
    substituteNamedAt]

/-- Compilation need not retain authoring identity: two different unused
target names yield the same artifact but remain different declarations. -/
theorem compilation_does_not_determine_declaration :
    ∃ first second : Declaration, first ≠ second ∧
      compileDeclaration first = compileDeclaration second := by
  refine ⟨⟨"x", .apply "K" [], .apply "V" []⟩,
    ⟨"y", .apply "K" [], .apply "V" []⟩, ?_, ?_⟩
  · intro equal
    have names := congrArg Declaration.target equal
    exact (by decide : "x" ≠ "y") names
  · simp [compileDeclaration, abstractNamedAt, liftBVars, liftBVarsList,
      closeFVar]

end Controls

#print axioms instantiate_abstract_named
#print axioms compileDeclaration_adequate
#print axioms substitute_named_scoped
#print axioms compileDeclaration_scoped
#print axioms realization
#print axioms combined_realization_adequate
#print axioms withExports_quote
#print axioms Controls.closing_without_weakening_is_wrong

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NamedSubstitutionElaboration
