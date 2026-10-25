import Mettapedia.GSLT.LanguageDef.BindingCollectionEquationFamily
import Mettapedia.OSLF.Syntax.BindingEqualityCertificates

/-!
# Intrinsic provenance of the derived collection equations

Each generator is one of the seven authored collection operations on typed
inputs, at any finite arity and ordered context. Its raw boundary receipt is
obtained from the existing producer. This distinguishes generated intrinsic
equations from the stronger family admitting every alternative elaboration
of equal erased endpoints.

All intended operations remain available. No equation is obtained by guessing
the declaration or the type of an erased collection.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.CollectionEquationGenerators

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open CollectionEquationFamily

/-- The actual bare collection row and its exact self-sorted parameter. -/
structure Row (language : LanguageDef) (kind : CollType) where
  rule : GrammarRule
  member : rule ∈ language.terms
  parameter : String
  shape : rule.bareParams = [.simple parameter (.collection kind (.base rule.category))]

/-- Reconstruct the source carrier row from checked finite inventory data. -/
def Row.ofRule? (language : LanguageDef) (kind : CollType) (rule : GrammarRule)
    (parameter : String) : Option (Row language kind) :=
  if member : rule ∈ language.terms then
    if shape : rule.bareParams = [.simple parameter (.collection kind (.base rule.category))] then
      some ⟨rule, member, parameter, shape⟩
    else none
  else none

theorem Row.ofRule?_complete {language : LanguageDef} {kind : CollType} (row : Row language kind) :
    Row.ofRule? language kind row.rule row.parameter = some row := by
  cases row with
  | mk rule member parameter shape => simp only [ofRule?, member, shape, dite_true]

theorem Row.ofRule?_exact (language : LanguageDef) (kind : CollType) (rule : GrammarRule)
    (parameter : String) :
    (∃ row, Row.ofRule? language kind rule parameter = some row) ↔
      rule ∈ language.terms ∧ rule.bareParams = [.simple parameter (.collection kind (.base rule.category))] := by
  simp only [ofRule?]
  split
  · split
    · exact ⟨fun _ => ⟨by assumption, by assumption⟩, fun _ => ⟨_, rfl⟩⟩
    · simp_all
  · simp_all

abbrev Values {language : LanguageDef} {kind : CollType} (row : Row language kind)
    (Γ : List TypeExpr) := List (Term (signatureOf language) Γ (.base row.rule.category))

/-- Only the existing typed producer operations generate this intrinsic
presentation. Arbitrary contexts, counts and typed child terms are retained. -/
inductive Generator (language : LanguageDef) : Type where
  | bagPermutation (row : Row language .hashBag) {Γ : List TypeExpr}
      (first second : Values row Γ) (permutation : first.Perm second)
  | setPermutation (row : Row language .hashSet) {Γ : List TypeExpr}
      (first second : Values row Γ) (permutation : first.Perm second)
  | setDeduplication (row : Row language .hashSet) {Γ : List TypeExpr}
      (value : Term (signatureOf language) Γ (.base row.rule.category)) (rest : Values row Γ)
  | flattening {kind : CollType} (row : Row language kind) (algebra : CollectionAlgebra)
      (declaration : AlgebraRule language row.rule kind algebra) (enabled : algebra.flatten = true)
      {Γ : List TypeExpr} (pre inner post : Values row Γ)
  | singletonCollapse {kind : CollType} (row : Row language kind) (algebra : CollectionAlgebra)
      (declaration : AlgebraRule language row.rule kind algebra) (enabled : algebra.flatten = true)
      {Γ : List TypeExpr} (value : Term (signatureOf language) Γ (.base row.rule.category))
  | unitElimination {kind : CollType} (row : Row language kind) (algebra : CollectionAlgebra)
      (declaration : AlgebraRule language row.rule kind algebra)
      (unit : String) (selected : algebra.unit = some unit)
      {Γ : List TypeExpr} (pre post : Values row Γ)
  | emptyUnit {kind : CollType} (row : Row language kind) (algebra : CollectionAlgebra)
      (declaration : AlgebraRule language row.rule kind algebra)
      (unit : String) (selected : algebra.unit = some unit) (Γ : List TypeExpr)

/-- Permutation is checked on the actual full intrinsic terms, including
complete declaring rows; equal raw erasures are not substituted for it. -/
def Generator.bagPermutation? {language : LanguageDef} (row : Row language .hashBag)
    {Γ : List TypeExpr} (first second : Values row Γ) : Option (Generator language) :=
  if permutation : first.Perm second then some (.bagPermutation row first second permutation) else none

def Generator.setPermutation? {language : LanguageDef} (row : Row language .hashSet)
    {Γ : List TypeExpr} (first second : Values row Γ) : Option (Generator language) :=
  if permutation : first.Perm second then some (.setPermutation row first second permutation) else none

theorem Generator.bagPermutation?_exact {language : LanguageDef} (row : Row language .hashBag)
    {Γ : List TypeExpr} (first second : Values row Γ) :
    (∃ generator, Generator.bagPermutation? row first second = some generator) ↔ first.Perm second := by
  unfold bagPermutation?
  split <;> simp_all

theorem Generator.setPermutation?_exact {language : LanguageDef} (row : Row language .hashSet)
    {Γ : List TypeExpr} (first second : Values row Γ) :
    (∃ generator, Generator.setPermutation? row first second = some generator) ↔ first.Perm second := by
  unfold setPermutation?
  split <;> simp_all

/-- Algebraic source producers reconstruct every declaring-row and enabled-law
premise before producing an original generator. -/
def Generator.flattening? {language : LanguageDef} {kind : CollType}
    (row : Row language kind) (algebra : CollectionAlgebra)
    {Γ : List TypeExpr} (pre inner post : Values row Γ) : Option (Generator language) := do
  let declaration ← checkedAlgebra? language row.rule kind algebra row.parameter
  if enabled : algebra.flatten = true then
    some (.flattening row algebra declaration.down enabled pre inner post)
  else none

def Generator.singletonCollapse? {language : LanguageDef} {kind : CollType}
    (row : Row language kind) (algebra : CollectionAlgebra)
    {Γ : List TypeExpr} (value : Term (signatureOf language) Γ (.base row.rule.category)) :
    Option (Generator language) := do
  let declaration ← checkedAlgebra? language row.rule kind algebra row.parameter
  if enabled : algebra.flatten = true then
    some (.singletonCollapse row algebra declaration.down enabled value)
  else none

def Generator.unitElimination? {language : LanguageDef} {kind : CollType}
    (row : Row language kind) (algebra : CollectionAlgebra) (unit : String)
    {Γ : List TypeExpr} (pre post : Values row Γ) : Option (Generator language) := do
  let declaration ← checkedAlgebra? language row.rule kind algebra row.parameter
  if selected : algebra.unit = some unit then
    some (.unitElimination row algebra declaration.down unit selected pre post)
  else none

def Generator.emptyUnit? {language : LanguageDef} {kind : CollType}
    (row : Row language kind) (algebra : CollectionAlgebra) (unit : String)
    (Γ : List TypeExpr) : Option (Generator language) := do
  let declaration ← checkedAlgebra? language row.rule kind algebra row.parameter
  if selected : algebra.unit = some unit then
    some (.emptyUnit row algebra declaration.down unit selected Γ)
  else none

theorem Generator.flattening?_complete {language : LanguageDef} {kind : CollType}
    (row : Row language kind) (algebra : CollectionAlgebra)
    (declaration : AlgebraRule language row.rule kind algebra) (enabled : algebra.flatten = true)
    {Γ : List TypeExpr} (pre inner post : Values row Γ) :
    Generator.flattening? row algebra pre inner post =
      some (.flattening row algebra declaration enabled pre inner post) := by
  obtain ⟨receipt, read⟩ := checkedAlgebra?_complete declaration
    ((GrammarRule.bareParams_cons_iff _ _ _).mp row.shape).2
  simp only [flattening?, read, enabled, dite_true]
  rfl

theorem Generator.singletonCollapse?_complete {language : LanguageDef} {kind : CollType}
    (row : Row language kind) (algebra : CollectionAlgebra)
    (declaration : AlgebraRule language row.rule kind algebra) (enabled : algebra.flatten = true)
    {Γ : List TypeExpr} (value : Term (signatureOf language) Γ (.base row.rule.category)) :
    Generator.singletonCollapse? row algebra value =
      some (.singletonCollapse row algebra declaration enabled value) := by
  obtain ⟨receipt, read⟩ := checkedAlgebra?_complete declaration
    ((GrammarRule.bareParams_cons_iff _ _ _).mp row.shape).2
  simp only [singletonCollapse?, read, enabled, dite_true]
  rfl

theorem Generator.unitElimination?_complete {language : LanguageDef} {kind : CollType}
    (row : Row language kind) (algebra : CollectionAlgebra)
    (declaration : AlgebraRule language row.rule kind algebra)
    (unit : String) (selected : algebra.unit = some unit)
    {Γ : List TypeExpr} (pre post : Values row Γ) :
    Generator.unitElimination? row algebra unit pre post =
      some (.unitElimination row algebra declaration unit selected pre post) := by
  obtain ⟨receipt, read⟩ := checkedAlgebra?_complete declaration
    ((GrammarRule.bareParams_cons_iff _ _ _).mp row.shape).2
  simp only [unitElimination?, read, selected, dite_true]
  rfl

theorem Generator.emptyUnit?_complete {language : LanguageDef} {kind : CollType}
    (row : Row language kind) (algebra : CollectionAlgebra)
    (declaration : AlgebraRule language row.rule kind algebra)
    (unit : String) (selected : algebra.unit = some unit) (Γ : List TypeExpr) :
    Generator.emptyUnit? row algebra unit Γ =
      some (.emptyUnit row algebra declaration unit selected Γ) := by
  obtain ⟨receipt, read⟩ := checkedAlgebra?_complete declaration
    ((GrammarRule.bareParams_cons_iff _ _ _).mp row.shape).2
  simp only [emptyUnit?, read, selected, dite_true]
  rfl

/-- The complete raw witness is produced from the supplied typed inputs,
rather than used to select arbitrary intrinsic endpoint elaborations. -/
noncomputable def Generator.declaration {language : LanguageDef} :
    Generator language → DeclaredAxiom language
  | .bagPermutation row first second permutation =>
      CollectionEquationFamily.bagPermutation row.rule row.member row.parameter row.shape
        first second permutation
  | .setPermutation row first second permutation =>
      CollectionEquationFamily.setPermutation row.rule row.member row.parameter row.shape
        first second permutation
  | .setDeduplication row value rest =>
      CollectionEquationFamily.setDeduplication row.rule row.member row.parameter row.shape value rest
  | .flattening row algebra declaration enabled pre inner post =>
      CollectionEquationFamily.flattening row.rule _ algebra declaration row.parameter row.shape
        enabled pre inner post
  | .singletonCollapse row algebra declaration enabled value =>
      CollectionEquationFamily.singletonCollapse row.rule _ algebra declaration row.parameter row.shape
        enabled value
  | .unitElimination row algebra declaration unit selected pre post =>
      CollectionEquationFamily.unitElimination row.rule _ algebra declaration row.parameter row.shape
        unit selected pre post
  | .emptyUnit row algebra declaration unit selected Γ =>
      CollectionEquationFamily.emptyUnit (Γ := Γ) row.rule _ algebra declaration row.parameter row.shape
        unit selected

/-- Unit-using generators retain one actual selected nullary declaration.
The other generators need no additional choice data. -/
def Generator.UnitSelection {language : LanguageDef} : Generator language → Type
  | .unitElimination row _ _ unit _ _ _ => SelectedUnit language row.rule.category unit
  | .emptyUnit row _ _ unit _ _ => SelectedUnit language row.rule.category unit
  | _ => Unit

/-- The seven original producers share their existing operations. Only the
unit branches now consume explicit, source-checked row selections. -/
def Generator.declarationWith {language : LanguageDef} :
    (generator : Generator language) → generator.UnitSelection → DeclaredAxiom language
  | .bagPermutation row first second permutation, _ =>
      CollectionEquationFamily.bagPermutation row.rule row.member row.parameter row.shape
        first second permutation
  | .setPermutation row first second permutation, _ =>
      CollectionEquationFamily.setPermutation row.rule row.member row.parameter row.shape
        first second permutation
  | .setDeduplication row value rest, _ =>
      CollectionEquationFamily.setDeduplication row.rule row.member row.parameter row.shape value rest
  | .flattening row algebra declaration enabled pre inner post, _ =>
      CollectionEquationFamily.flattening row.rule _ algebra declaration row.parameter row.shape
        enabled pre inner post
  | .singletonCollapse row algebra declaration enabled value, _ =>
      CollectionEquationFamily.singletonCollapse row.rule _ algebra declaration row.parameter row.shape
        enabled value
  | .unitElimination row algebra declaration unit selected pre post, chosen =>
      CollectionEquationFamily.unitEliminationWith row.rule _ algebra declaration row.parameter row.shape
        unit selected chosen pre post
  | .emptyUnit row algebra declaration unit selected Γ, chosen =>
      CollectionEquationFamily.emptyUnitWith (Γ := Γ) row.rule _ algebra declaration row.parameter row.shape
        unit selected chosen

/-- Search the original finite row inventory only when this generator uses a
unit. Every successful value retains the actual row and its formation data. -/
def Generator.selection? {language : LanguageDef} :
    (generator : Generator language) → Option generator.UnitSelection
  | .unitElimination row _ _ unit _ _ _ => SelectedUnit.find? language row.rule.category unit
  | .emptyUnit row _ _ unit _ _ => SelectedUnit.find? language row.rule.category unit
  | .bagPermutation _ _ _ _ => some ()
  | .setPermutation _ _ _ _ => some ()
  | .setDeduplication _ _ _ => some ()
  | .flattening _ _ _ _ _ _ _ => some ()
  | .singletonCollapse _ _ _ _ _ => some ()

theorem Generator.selection?_total {language : LanguageDef} (generator : Generator language) :
    ∃ selected, generator.selection? = some selected := by
  cases generator with
  | unitElimination row algebra declaration unit selected pre post =>
      obtain ⟨unitRow, member, labelled, sorted, empty⟩ := declaration.unitAuthored unit selected
      exact SelectedUnit.find?_complete ⟨unitRow, member, labelled, sorted, empty⟩
  | emptyUnit row algebra declaration unit selected Γ =>
      obtain ⟨unitRow, member, labelled, sorted, empty⟩ := declaration.unitAuthored unit selected
      exact SelectedUnit.find?_complete ⟨unitRow, member, labelled, sorted, empty⟩
  | _ => exact ⟨(), rfl⟩

/-- The actual finite computation returns its produced typed declaration. -/
def Generator.declaration? {language : LanguageDef} (generator : Generator language) :
    Option (DeclaredAxiom language) :=
  generator.selection?.map generator.declarationWith

theorem Generator.declaration?_total {language : LanguageDef} (generator : Generator language) :
    ∃ declaration, generator.declaration? = some declaration := by
  obtain ⟨selected, accepted⟩ := generator.selection?_total
  exact ⟨generator.declarationWith selected, by simp only [declaration?, accepted, Option.map_some]⟩

/-- Original non-effective selection is used only to prove existence of a
finite exact witness. No runtime search invokes it. -/
noncomputable def Generator.originalSelection {language : LanguageDef} :
    (generator : Generator language) → generator.UnitSelection
  | .unitElimination row algebra declaration unit selected _ _ =>
      originalUnit row.rule _ algebra declaration unit selected
  | .emptyUnit row algebra declaration unit selected _ =>
      originalUnit row.rule _ algebra declaration unit selected
  | .bagPermutation _ _ _ _ => ()
  | .setPermutation _ _ _ _ => ()
  | .setDeduplication _ _ _ => ()
  | .flattening _ _ _ _ _ _ _ => ()
  | .singletonCollapse _ _ _ _ _ => ()

theorem Generator.declarationWith_original {language : LanguageDef} (generator : Generator language) :
    generator.declarationWith generator.originalSelection = generator.declaration := by
  cases generator <;> rfl

/-- This local test concerns only the unit rows this particular generator
uses. Other constructor inventories are unrestricted. -/
def Generator.unitUnique? {language : LanguageDef} : Generator language → Bool
  | .unitElimination row _ _ unit _ _ _ => SelectedUnit.unique? language row.rule.category unit
  | .emptyUnit row _ _ unit _ _ => SelectedUnit.unique? language row.rule.category unit
  | _ => true

theorem Generator.declarationWith_eq_original {language : LanguageDef} (generator : Generator language)
    (unique : generator.unitUnique? = true) (selected : generator.UnitSelection) :
    generator.declarationWith selected = generator.declaration := by
  cases generator with
  | unitElimination row algebra declaration unit isUnit pre post =>
      have same := (SelectedUnit.same_row_iff selected
        (originalUnit row.rule _ algebra declaration unit isUnit)).mp
        (SelectedUnit.unique?_sound unique _ _)
      cases same
      rfl
  | emptyUnit row algebra declaration unit isUnit Γ =>
      have same := (SelectedUnit.same_row_iff selected
        (originalUnit row.rule _ algebra declaration unit isUnit)).mp
        (SelectedUnit.unique?_sound unique _ _)
      cases same
      rfl
  | _ => rfl

/-- A packet may provide its complete selected unit row. Checking that row
retains all original source choices even when finite first-match search and
the old mathematical choice select different metadata. -/
def Generator.selectionFromRow? {language : LanguageDef} :
    (generator : Generator language) → Option GrammarRule → Option generator.UnitSelection
  | .unitElimination row _ _ unit _ _ _, some chosen =>
      SelectedUnit.ofRow? language row.rule.category unit chosen
  | .emptyUnit row _ _ unit _ _, some chosen =>
      SelectedUnit.ofRow? language row.rule.category unit chosen
  | .bagPermutation _ _ _ _, none => some ()
  | .setPermutation _ _ _ _, none => some ()
  | .setDeduplication _ _ _, none => some ()
  | .flattening _ _ _ _ _ _ _, none => some ()
  | .singletonCollapse _ _ _ _ _, none => some ()
  | _, _ => none

def Generator.selectionRow {language : LanguageDef} :
    (generator : Generator language) → generator.UnitSelection → Option GrammarRule
  | .unitElimination _ _ _ _ _ _ _, selected => some selected.rule
  | .emptyUnit _ _ _ _ _ _, selected => some selected.rule
  | .bagPermutation _ _ _ _, _ => none
  | .setPermutation _ _ _ _, _ => none
  | .setDeduplication _ _ _, _ => none
  | .flattening _ _ _ _ _ _ _, _ => none
  | .singletonCollapse _ _ _ _ _, _ => none

theorem Generator.selectionFromRow?_complete {language : LanguageDef} (generator : Generator language)
    (selected : generator.UnitSelection) :
    generator.selectionFromRow? (generator.selectionRow selected) = some selected := by
  cases generator with
  | unitElimination => exact SelectedUnit.ofRow?_complete _
  | emptyUnit => exact SelectedUnit.ofRow?_complete _
  | _ => cases selected; rfl

def Generator.checkedDeclaration? {language : LanguageDef} (generator : Generator language)
    (selectedRow : Option GrammarRule) : Option (DeclaredAxiom language) :=
  (generator.selectionFromRow? selectedRow).map generator.declarationWith

/-- Every original intrinsic generator has an accepted finite selected-row
packet with exactly its original intrinsic endpoints. This coverage theorem
requires no uniqueness assumption on the source language. -/
theorem Generator.checkedDeclaration?_covers_original {language : LanguageDef}
    (generator : Generator language) :
    ∃ selectedRow, generator.checkedDeclaration? selectedRow = some generator.declaration := by
  refine ⟨generator.selectionRow generator.originalSelection, ?_⟩
  rw [checkedDeclaration?, generator.selectionFromRow?_complete, Option.map_some,
    generator.declarationWith_original]

/-- Selection does not change the source context, category, declaring row or
raw equation endpoints. Intrinsic full-row equality is a stronger property. -/
theorem Generator.declarationWith_context {language : LanguageDef} (generator : Generator language)
    (selected : generator.UnitSelection) :
    (generator.declarationWith selected).context = generator.declaration.context := by
  cases generator <;> rfl

theorem Generator.declarationWith_category {language : LanguageDef} (generator : Generator language)
    (selected : generator.UnitSelection) :
    (generator.declarationWith selected).category = generator.declaration.category := by
  cases generator <;> rfl

theorem Generator.declarationWith_source {language : LanguageDef} (generator : Generator language)
    (selected : generator.UnitSelection) :
    (generator.declarationWith selected).source = generator.declaration.source := by
  cases generator <;> rfl

theorem Generator.declarationWith_target {language : LanguageDef} (generator : Generator language)
    (selected : generator.UnitSelection) :
    (generator.declarationWith selected).target = generator.declaration.target := by
  cases generator <;> rfl

theorem Generator.declarationWith_declaringRule {language : LanguageDef} (generator : Generator language)
    (selected : generator.UnitSelection) :
    declaringRule (generator.declarationWith selected).witness = declaringRule generator.declaration.witness := by
  cases generator <;> rfl

theorem Generator.declarationWith_erases {language : LanguageDef} (generator : Generator language)
    (selected : generator.UnitSelection) :
    erase (generator.declarationWith selected).left = erase generator.declaration.left ∧
      erase (generator.declarationWith selected).right = erase generator.declaration.right := by
  exact ⟨(generator.declarationWith selected).leftErases.trans
      ((generator.declarationWith_source selected).trans generator.declaration.leftErases.symm),
    (generator.declarationWith selected).rightErases.trans
      ((generator.declarationWith_target selected).trans generator.declaration.rightErases.symm)⟩

/-- Every computed generator is admitted by the existing provenance-bearing
boundary family; it is not licensed by a generic List representation. -/
theorem Generator.declarationWith_boundary {language : LanguageDef} (generator : Generator language)
    (selected : generator.UnitSelection) :
    CollectionEquationFamily.family language (generator.declarationWith selected).toAxiom :=
  declared_admitted _

def family (language : LanguageDef) (equation : EqAxiom (signatureOf language) []) : Prop :=
  ∃ generator : Generator language, generator.declaration.toAxiom = equation

theorem generated_admitted {language : LanguageDef} (generator : Generator language) :
    family language generator.declaration.toAxiom := ⟨generator, rfl⟩

/-- Every generated intrinsic law has its already checked declaring-rule and
raw operational boundary evidence. The converse is not asserted. -/
theorem included_in_boundary_family {language : LanguageDef}
    {equation : EqAxiom (signatureOf language) []} (admitted : family language equation) :
    CollectionEquationFamily.family language equation := by
  obtain ⟨generator, rfl⟩ := admitted
  exact declared_admitted generator.declaration

/-- A finite source producer together with its explicit checked unit row.
This reuses the original seven-generator syntax. -/
abbrev SelectedGenerator (language : LanguageDef) :=
  (generator : Generator language) × generator.UnitSelection

def SelectedGenerator.declaration {language : LanguageDef} (selected : SelectedGenerator language) :
    DeclaredAxiom language := selected.1.declarationWith selected.2

/-- One actual root certificate uses a finite substitution vector for every
ordinary source variable. There are no contextual metavariables in these
collection laws and no provider callback in this evidence. -/
def SelectedGenerator.instanceCertificate {language : LanguageDef} (selected : SelectedGenerator language)
    {Γ : List TypeExpr}
    (environment : EqualityCertificates.Substitution (signatureOf language) selected.declaration.context Γ) :
    EqualityCertificates.Certificate (signatureOf language) [] [selected.declaration.toAxiom]
      Γ (.base selected.declaration.category) :=
  .axiom ⟨0, by simp⟩ (.nil (Θ := [])) .nil environment

theorem SelectedGenerator.instanceCertificate_checked {language : LanguageDef}
    (selected : SelectedGenerator language) {Γ : List TypeExpr}
    (environment : EqualityCertificates.Substitution (signatureOf language) selected.declaration.context Γ) :
    EqualityCertificates.check (selected.instanceCertificate environment)
      (bind environment.read selected.declaration.left)
      (bind environment.read selected.declaration.right) = true := by
  simp only [instanceCertificate, EqualityCertificates.check, EqualityCertificates.replay,
    List.get_eq_getElem, List.getElem_cons_zero, DeclaredAxiom.toAxiom,
    ContextualAssignment.instantiate_embed, and_self, decide_true]

/-- The constructive intrinsic family permits any checked unit-row selection.
The older choice-fixed family is included; equality of those intrinsic
families is not asserted for ambiguous unit metadata. -/
def selectedFamily (language : LanguageDef) (equation : EqAxiom (signatureOf language) []) : Prop :=
  ∃ selected : SelectedGenerator language, selected.declaration.toAxiom = equation

theorem original_in_selected {language : LanguageDef}
    {equation : EqAxiom (signatureOf language) []} (admitted : family language equation) :
    selectedFamily language equation := by
  obtain ⟨generator, same⟩ := admitted
  exact ⟨⟨generator, generator.originalSelection⟩,
    (congrArg DeclaredAxiom.toAxiom generator.declarationWith_original).trans same⟩

theorem selected_in_boundary {language : LanguageDef}
    {equation : EqAxiom (signatureOf language) []} (admitted : selectedFamily language equation) :
    CollectionEquationFamily.family language equation := by
  obtain ⟨selected, rfl⟩ := admitted
  exact declared_admitted _

/-- This finite environment is computed from the source producers and their
literal unit metadata; checking equality evidence never selects an axiom. -/
def equations {language : LanguageDef} (selected : List (SelectedGenerator language)) :
    List (EqAxiom (signatureOf language) []) :=
  selected.map (fun item => item.declaration.toAxiom)

theorem equations_supported {language : LanguageDef} (selected : List (SelectedGenerator language)) :
    BindingEquationFamilyCongruence.Supported (selectedFamily language) (equations selected) := by
  intro equation member
  obtain ⟨item, _, same⟩ := List.mem_map.mp member
  exact ⟨item, same⟩

/-- Every finite supported source fragment has finite producer data. This is
an evidence-existence result; it introduces no proof-to-runtime choice. -/
theorem supported_finite {language : LanguageDef}
    (fragment : List (EqAxiom (signatureOf language) []))
    (supported : BindingEquationFamilyCongruence.Supported (selectedFamily language) fragment) :
    ∃ selected : List (SelectedGenerator language), equations selected = fragment := by
  induction fragment with
  | nil => exact ⟨[], rfl⟩
  | cons equation rest ih =>
      obtain ⟨head, same⟩ := supported equation List.mem_cons_self
      obtain ⟨tail, exactTail⟩ := ih (fun later member => supported later (List.mem_cons_of_mem _ member))
      exact ⟨head :: tail, congrArg₂ List.cons same exactTail⟩

/-- Actual replay of the existing finite, sorted/scoped equality certificates
is exact for this generated finite environment. Operator comparison retains
full source declaration metadata and binding arities. -/
theorem finite_evidence_exact {language : LanguageDef} (selected : List (SelectedGenerator language))
    {Γ : List TypeExpr} {sort : TypeExpr}
    (left right : Term (signatureOf language) Γ sort) :
    EqClosure (equations selected) left right ↔
      ∃ certificate : EqualityCertificates.Certificate (signatureOf language) [] (equations selected) Γ sort,
        EqualityCertificates.check certificate left right = true :=
  EqualityCertificates.check_complete left right

/-- The independently generated contextual equation relation and accepted
finite evidence have the same scope. In particular, arbitrary original
binder contexts and explicit simultaneous substitutions are retained. -/
theorem selected_evidence_exact {language : LanguageDef}
    {Γ : List TypeExpr} {sort : TypeExpr} (left right : Term (signatureOf language) Γ sort) :
    BindingEquationFamilyCongruence.Related (selectedFamily language) left right ↔
      ∃ selected : List (SelectedGenerator language),
        ∃ certificate : EqualityCertificates.Certificate (signatureOf language) [] (equations selected) Γ sort,
          EqualityCertificates.check certificate left right = true := by
  constructor
  · rintro ⟨fragment, supported, derivation⟩
    obtain ⟨selected, rfl⟩ := supported_finite fragment supported
    obtain ⟨certificate, accepted⟩ := (finite_evidence_exact selected left right).mp derivation
    exact ⟨selected, certificate, accepted⟩
  · rintro ⟨selected, certificate, accepted⟩
    exact ⟨equations selected, equations_supported selected,
      EqualityCertificates.check_sound certificate left right accepted⟩

/-- Original intrinsic source proofs are covered without a global unit
uniqueness assumption. The constructive selected family remains explicit. -/
theorem original_evidence_coverage {language : LanguageDef}
    {Γ : List TypeExpr} {sort : TypeExpr} {left right : Term (signatureOf language) Γ sort}
    (derivation : BindingEquationFamilyCongruence.Related (family language) left right) :
    ∃ selected : List (SelectedGenerator language),
      ∃ certificate : EqualityCertificates.Certificate (signatureOf language) [] (equations selected) Γ sort,
        EqualityCertificates.check certificate left right = true := by
  obtain ⟨fragment, supported, proof⟩ := derivation
  exact (selected_evidence_exact left right).mp ⟨fragment,
    (fun equation member => original_in_selected (supported equation member)), proof⟩

/-- Every selected source producer is a root of the existing contextual
congruence, using its actual computed certificate. -/
theorem SelectedGenerator.related {language : LanguageDef} (selected : SelectedGenerator language) :
    BindingEquationFamilyCongruence.Related (selectedFamily language)
      selected.declaration.left selected.declaration.right := by
  let environment := EqualityCertificates.Substitution.quote (S := signatureOf language)
    selected.declaration.context (fun _ position => Term.var position)
  have accepted := selected.instanceCertificate_checked environment
  have proof := EqualityCertificates.check_sound (selected.instanceCertificate environment)
    (bind environment.read selected.declaration.left) (bind environment.read selected.declaration.right) accepted
  simp only [environment, EqualityCertificates.Substitution.read_quote, bind_id] at proof
  refine ⟨[selected.declaration.toAxiom], ?_, proof⟩
  intro equation member
  have same := List.mem_singleton.mp member
  exact ⟨selected, same.symm⟩

/-- At the declared algebraic observer, every checked unit-row selection
represents the same unit. The complete source metadata remains distinct in
raw intrinsic syntax; the equality is earned from two empty-unit laws. -/
theorem selectedUnits_related {language : LanguageDef} {kind : CollType}
    (row : Row language kind) (algebra : CollectionAlgebra)
    (declaration : AlgebraRule language row.rule kind algebra)
    (unit : String) (isUnit : algebra.unit = some unit)
    (first second : SelectedUnit language row.rule.category unit) {Γ : List TypeExpr} :
    BindingEquationFamilyCongruence.Related (selectedFamily language)
      (first.term (Γ := Γ)) second.term := by
  let generator : Generator language := .emptyUnit row algebra declaration unit isUnit Γ
  have left := SelectedGenerator.related (⟨generator, first⟩ : SelectedGenerator language)
  have right := SelectedGenerator.related (⟨generator, second⟩ : SelectedGenerator language)
  exact BindingEquationFamilyCongruence.Related.trans
    (BindingEquationFamilyCongruence.Related.symm left) right

/-- The comparison survives the original capture-avoiding simultaneous
substitution, including every declared binder prefix. -/
theorem selectedUnits_bind_related {language : LanguageDef} {kind : CollType}
    (row : Row language kind) (algebra : CollectionAlgebra)
    (declaration : AlgebraRule language row.rule kind algebra)
    (unit : String) (isUnit : algebra.unit = some unit)
    (first second : SelectedUnit language row.rule.category unit) {Γ Δ : List TypeExpr}
    (environment : Sub (signatureOf language) Γ Δ) :
    BindingEquationFamilyCongruence.Related (selectedFamily language)
      (bind environment first.term) (bind environment second.term) :=
  BindingEquationFamilyCongruence.Related.bind environment
    (selectedUnits_related row algebra declaration unit isUnit first second)

/-- Per-used-generator uniqueness is sufficient to stay inside the older
choice-fixed intrinsic family. No unrelated unit inventory is restricted. -/
theorem equations_original_supported {language : LanguageDef}
    (selected : List (SelectedGenerator language))
    (unique : ∀ item ∈ selected, item.1.unitUnique? = true) :
    BindingEquationFamilyCongruence.Supported (family language) (equations selected) := by
  intro equation member
  obtain ⟨item, inSelected, same⟩ := List.mem_map.mp member
  refine ⟨item.1, ?_⟩
  exact (congrArg DeclaredAxiom.toAxiom
    (item.1.declarationWith_eq_original (unique item inSelected) item.2)).symm.trans same

end Mettapedia.GSLT.LanguageDef.BindingSyntax.CollectionEquationGenerators
