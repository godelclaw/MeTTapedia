import Mettapedia.GSLT.LanguageDef.BindingSignature
import Mettapedia.GSLT.LanguageDef.EquationOccurrence
import Mettapedia.OSLF.Syntax.BindingEquationFamilyModel

/-!
# Collection equations from actual authored declaration witnesses

The equation family retains the declaring grammar row, its exact category,
and the existing proof-relevant derived-law witness. Its generators range
over every finite collection size and every intrinsic ambient context. Their
closure and full quotient-valued model use the checked equation-family core.
The family adds no signature monoid laws and carries no runtime authority.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.CollectionEquationFamily

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics

def declaringRule {language : LanguageDef} {left right : Pattern} :
    DerivedGeneratorWitness language left right → GrammarRule
  | .bagPerm rule _ _ _ _ _ => rule
  | .setPerm rule _ _ _ _ _ => rule
  | .setDedup rule _ _ _ _ => rule
  | .flatten rule _ _ _ _ _ _ _ _ => rule
  | .singleton rule _ _ _ _ _ _ => rule
  | .unitElim rule _ _ _ _ _ _ _ _ => rule
  | .emptyUnit rule _ _ _ _ _ _ => rule

/-- Sorted intrinsic endpoints and the exact authored derived-law occurrence.
The category equation prevents a differently coloured declaration from
supplying the law merely by choosing another existential raw typing context. -/
structure DeclaredAxiom (language : LanguageDef) where
  context : List TypeExpr
  category : String
  left : Term (signatureOf language) context (.base category)
  right : Term (signatureOf language) context (.base category)
  source : Pattern
  target : Pattern
  leftErases : erase left = source
  rightErases : erase right = target
  witness : DerivedGeneratorWitness language source target
  sameCategory : (declaringRule witness).category = category

def DeclaredAxiom.toAxiom {language : LanguageDef} (declaration : DeclaredAxiom language) :
    EqAxiom (signatureOf language) [] :=
  ⟨declaration.context, .base declaration.category, embed declaration.left, embed declaration.right⟩

def family (language : LanguageDef) (equation : EqAxiom (signatureOf language) []) : Prop :=
  ∃ declaration : DeclaredAxiom language, declaration.toAxiom = equation

theorem declared_admitted {language : LanguageDef} (declaration : DeclaredAxiom language) :
    family language declaration.toAxiom := ⟨declaration, rfl⟩

/-- The actual variadic row is used at the input list's exact finite size. -/
def homogeneousArguments {language : LanguageDef} {Γ : List TypeExpr} {sort : TypeExpr} :
    (values : List (Term (signatureOf language) Γ sort)) →
      Args (signatureOf language) (List.replicate values.length ([], sort)) Γ
  | [] => .nil
  | head :: tail => .cons head (homogeneousArguments tail)

theorem erase_homogeneousArguments {language : LanguageDef}
    {Γ : List TypeExpr} {sort : TypeExpr}
    (values : List (Term (signatureOf language) Γ sort)) :
    eraseArguments (homogeneousArguments values) = values.map erase := by
  induction values with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons (erase head)) ih

def node {language : LanguageDef} (rule : GrammarRule) (member : rule ∈ language.terms)
    (parameter : String) (kind : CollType)
    (shape : rule.params = [.simple parameter (.collection kind (.base rule.category))])
    {Γ : List TypeExpr} (values : List (Term (signatureOf language) Γ (.base rule.category))) :
    Term (signatureOf language) Γ (.base rule.category) :=
  .op (.collectionConstructor rule member parameter kind (.base rule.category) shape values.length)
    (homogeneousArguments values)

theorem erase_node {language : LanguageDef} (rule : GrammarRule)
    (member : rule ∈ language.terms) (parameter : String) (kind : CollType)
    (shape : rule.params = [.simple parameter (.collection kind (.base rule.category))])
    {Γ : List TypeExpr} (values : List (Term (signatureOf language) Γ (.base rule.category))) :
    erase (node rule member parameter kind shape values) =
      .collection kind (values.map erase) none := erase_homogeneousArguments values |>
        congrArg (fun elements => Pattern.collection kind elements none)

theorem sorted_node {language : LanguageDef} (rule : GrammarRule)
    (member : rule ∈ language.terms) (parameter : String) (kind : CollType)
    (shape : rule.params = [.simple parameter (.collection kind (.base rule.category))])
    {Γ : List TypeExpr} (values : List (Term (signatureOf language) Γ (.base rule.category))) :
    SortedAt language (.collection kind (values.map erase) none) rule.category := by
  refine ⟨FreeTypeContext.empty, Γ, ?_⟩
  rw [← erase_node rule member parameter kind shape values]
  exact erase_typed _

def bagPermutation {language : LanguageDef} (rule : GrammarRule)
    (member : rule ∈ language.terms) (parameter : String)
    (shape : rule.params = [.simple parameter (.collection .hashBag (.base rule.category))])
    {Γ : List TypeExpr} (first second : List (Term (signatureOf language) Γ (.base rule.category)))
    (permutation : first.Perm second) : DeclaredAxiom language where
  context := Γ
  category := rule.category
  left := node rule member parameter .hashBag shape first
  right := node rule member parameter .hashBag shape second
  source := .collection .hashBag (first.map erase) none
  target := .collection .hashBag (second.map erase) none
  leftErases := erase_node _ _ _ _ _ _
  rightErases := erase_node _ _ _ _ _ _
  witness := .bagPerm rule _ _ ⟨member, ⟨parameter, _, shape⟩⟩
    (sorted_node rule member parameter .hashBag shape first) (permutation.map erase)
  sameCategory := rfl

def setPermutation {language : LanguageDef} (rule : GrammarRule)
    (member : rule ∈ language.terms) (parameter : String)
    (shape : rule.params = [.simple parameter (.collection .hashSet (.base rule.category))])
    {Γ : List TypeExpr} (first second : List (Term (signatureOf language) Γ (.base rule.category)))
    (permutation : first.Perm second) : DeclaredAxiom language where
  context := Γ
  category := rule.category
  left := node rule member parameter .hashSet shape first
  right := node rule member parameter .hashSet shape second
  source := .collection .hashSet (first.map erase) none
  target := .collection .hashSet (second.map erase) none
  leftErases := erase_node _ _ _ _ _ _
  rightErases := erase_node _ _ _ _ _ _
  witness := .setPerm rule _ _ ⟨member, ⟨parameter, _, shape⟩⟩
    (sorted_node rule member parameter .hashSet shape first) (permutation.map erase)
  sameCategory := rfl

def setDeduplication {language : LanguageDef} (rule : GrammarRule)
    (member : rule ∈ language.terms) (parameter : String)
    (shape : rule.params = [.simple parameter (.collection .hashSet (.base rule.category))])
    {Γ : List TypeExpr} (value : Term (signatureOf language) Γ (.base rule.category))
    (rest : List (Term (signatureOf language) Γ (.base rule.category))) : DeclaredAxiom language where
  context := Γ
  category := rule.category
  left := node rule member parameter .hashSet shape (value :: value :: rest)
  right := node rule member parameter .hashSet shape (value :: rest)
  source := .collection .hashSet (erase value :: erase value :: rest.map erase) none
  target := .collection .hashSet (erase value :: rest.map erase) none
  leftErases := by rw [erase_node]; rfl
  rightErases := by rw [erase_node]; rfl
  witness := .setDedup rule _ _ ⟨member, ⟨parameter, _, shape⟩⟩
    (by simpa only [List.map_cons] using
      sorted_node rule member parameter .hashSet shape (value :: value :: rest))
  sameCategory := rfl

def flattening {language : LanguageDef} (rule : GrammarRule) (kind : CollType)
    (algebra : CollectionAlgebra) (declaration : AlgebraRule language rule kind algebra)
    (parameter : String)
    (shape : rule.params = [.simple parameter (.collection kind (.base rule.category))])
    (enabled : algebra.flatten = true) {Γ : List TypeExpr}
    (pre inner post : List (Term (signatureOf language) Γ (.base rule.category))) :
    DeclaredAxiom language where
  context := Γ
  category := rule.category
  left := node rule declaration.authored parameter kind shape
    (pre ++ node rule declaration.authored parameter kind shape inner :: post)
  right := node rule declaration.authored parameter kind shape (pre ++ inner ++ post)
  source := .collection kind
    (pre.map erase ++ .collection kind (inner.map erase) none :: post.map erase) none
  target := .collection kind (pre.map erase ++ inner.map erase ++ post.map erase) none
  leftErases := by simp only [erase_node, List.map_append, List.map_cons]
  rightErases := by simp only [erase_node, List.map_append]
  witness := .flatten rule kind algebra _ _ _ declaration enabled
    (by simpa only [List.map_append, List.map_cons, erase_node] using
      (sorted_node rule declaration.authored parameter kind shape
        (pre ++ node rule declaration.authored parameter kind shape inner :: post)))
  sameCategory := rfl

def singletonCollapse {language : LanguageDef} (rule : GrammarRule) (kind : CollType)
    (algebra : CollectionAlgebra) (declaration : AlgebraRule language rule kind algebra)
    (parameter : String)
    (shape : rule.params = [.simple parameter (.collection kind (.base rule.category))])
    (enabled : algebra.flatten = true) {Γ : List TypeExpr}
    (value : Term (signatureOf language) Γ (.base rule.category)) : DeclaredAxiom language where
  context := Γ
  category := rule.category
  left := node rule declaration.authored parameter kind shape [value]
  right := value
  source := .collection kind [erase value] none
  target := erase value
  leftErases := by rw [erase_node]; rfl
  rightErases := rfl
  witness := .singleton rule kind algebra _ declaration enabled
    (by simpa only [List.map_cons, List.map_nil] using
      sorted_node rule declaration.authored parameter kind shape [value])
  sameCategory := rfl

/-- The declared unit constructor is rebuilt from its actual nullary row. -/
def nullary {language : LanguageDef} (rule : GrammarRule) (member : rule ∈ language.terms)
    (empty : rule.params = []) {Γ : List TypeExpr} :
    Term (signatureOf language) Γ (.base rule.category) :=
  .op (.constructor rule member
    (by simp only [UsesBareCollection, empty]; simp)
    (by rw [empty]; exact ParameterScopes.nil)) .nil

theorem eraseConstructorArguments_empty {language : LanguageDef} {Γ : List TypeExpr}
    {parameters : List TermParam} (scopes : ParameterScopes parameters []) :
    eraseConstructorArguments (language := language) (bound := Γ) scopes .nil = [] := by
  cases scopes
  rfl

theorem erase_nullary {language : LanguageDef} (rule : GrammarRule)
    (member : rule ∈ language.terms) (empty : rule.params = []) {Γ : List TypeExpr} :
    erase (nullary (Γ := Γ) rule member empty) = .apply rule.label [] := by
  unfold nullary
  simp only [erase]
  congr 1
  exact eraseConstructorArguments_empty _

theorem erase_type_cast {language : LanguageDef} {Γ : List TypeExpr}
    {first second : TypeExpr} (same : first = second)
    (value : Term (signatureOf language) Γ first) :
    erase (same ▸ value) = erase value := by
  subst second
  rfl

/-- The complete declaring row of a constructor occurrence remains observable
at the intrinsic boundary, including metadata ignored by raw erasure. -/
def constructorRow? {language : LanguageDef} : {Γ : List TypeExpr} → {sort : TypeExpr} →
    Term (signatureOf language) Γ sort → Option GrammarRule
  | _, _, .var _ => none
  | _, _, .op operator _ => match operator with
      | .constructor rule _ _ _ => some rule
      | _ => none

/-- A concrete authored unit selection retains the complete grammar row.
Two rows with the same erased label need not have equal metadata. -/
structure SelectedUnit (language : LanguageDef) (category unit : String) where
  rule : GrammarRule
  authored : rule ∈ language.terms
  labelled : rule.label = unit
  sorted : rule.category = category
  nullary : rule.params = []

namespace SelectedUnit

variable {language : LanguageDef} {category unit : String}

def rowMatches (category unit : String) (rule : GrammarRule) : Bool :=
  decide (rule.label = unit ∧ rule.category = category ∧ rule.params = [])

/-- A packet may select any complete authored nullary row, rather than only
the first row selected by finite search. All original metadata is checked. -/
def ofRow? (language : LanguageDef) (category unit : String) (rule : GrammarRule) :
    Option (SelectedUnit language category unit) :=
  if member : rule ∈ language.terms then
    if fields : rule.label = unit ∧ rule.category = category ∧ rule.params = [] then
      some ⟨rule, member, fields.1, fields.2.1, fields.2.2⟩
    else none
  else none

theorem ofRow?_complete (selected : SelectedUnit language category unit) :
    ofRow? language category unit selected.rule = some selected := by
  simp only [ofRow?, selected.authored, selected.labelled, selected.sorted, selected.nullary,
    and_self, dite_true]

private def ofFiltered {rule : GrammarRule}
    (member : rule ∈ language.terms.filter (rowMatches category unit)) :
    SelectedUnit language category unit :=
  let admitted := List.mem_filter.mp member
  let fields : rule.label = unit ∧ rule.category = category ∧ rule.params = [] :=
    of_decide_eq_true admitted.2
  ⟨rule, admitted.1, fields.1, fields.2.1, fields.2.2⟩

/-- Search the original finite inventory and reconstruct every required
source premise. No untrusted row or opaque choice function is invoked. -/
def find? (language : LanguageDef) (category unit : String) : Option (SelectedUnit language category unit) :=
  match found : language.terms.find? (rowMatches category unit) with
  | none => none
  | some rule =>
      let fields : rule.label = unit ∧ rule.category = category ∧ rule.params = [] :=
        of_decide_eq_true (show rowMatches category unit rule = true from List.find?_some found)
      some ⟨rule, List.mem_of_find?_eq_some found, fields.1, fields.2.1, fields.2.2⟩

theorem find?_complete (selected : SelectedUnit language category unit) :
    ∃ actual, find? language category unit = some actual := by
  unfold find?
  split
  · rename_i absent
    have rejected := (List.find?_eq_none.mp absent) selected.rule selected.authored
    have accepted : rowMatches category unit selected.rule = true := by
      simp only [rowMatches, selected.labelled, selected.sorted, selected.nullary, and_self, decide_true]
    exact (rejected accepted).elim
  · exact ⟨_, rfl⟩

theorem find?_exact (language : LanguageDef) (category unit : String) :
    (∃ actual, find? language category unit = some actual) ↔ Nonempty (SelectedUnit language category unit) :=
  ⟨fun ⟨actual, _⟩ => ⟨actual⟩, fun ⟨selected⟩ => find?_complete selected⟩

def term (selected : SelectedUnit language category unit) {Γ : List TypeExpr} :
    Term (signatureOf language) Γ (.base category) :=
  congrArg TypeExpr.base selected.sorted ▸ CollectionEquationFamily.nullary selected.rule selected.authored selected.nullary

@[simp] theorem erase_term (selected : SelectedUnit language category unit) {Γ : List TypeExpr} :
    erase (selected.term (Γ := Γ)) = .apply unit [] := by
  rw [term, erase_type_cast, erase_nullary, selected.labelled]

theorem term_selection_independent (first second : SelectedUnit language category unit) {Γ : List TypeExpr} :
    erase (first.term (Γ := Γ)) = erase (second.term (Γ := Γ)) := by
  rw [erase_term, erase_term]

/-- The selected unit has no variables; actual source renaming retains the
whole selected constructor metadata, not only its raw erased label. -/
theorem term_rename (selected : SelectedUnit language category unit) {Γ Δ : List TypeExpr}
    (action : Ren (signatureOf language) Γ Δ) :
    Mettapedia.OSLF.Binding.rename action selected.term = selected.term := by
  rcases selected with ⟨rule, member, labelled, sorted, empty⟩
  cases sorted
  simp only [term, CollectionEquationFamily.nullary, Mettapedia.OSLF.Binding.rename, Mettapedia.OSLF.Binding.renameArgs]

theorem term_bind (selected : SelectedUnit language category unit) {Γ Δ : List TypeExpr}
    (action : Sub (signatureOf language) Γ Δ) :
    Mettapedia.OSLF.Binding.bind action selected.term = selected.term := by
  rcases selected with ⟨rule, member, labelled, sorted, empty⟩
  cases sorted
  simp only [term, CollectionEquationFamily.nullary, Mettapedia.OSLF.Binding.bind, Mettapedia.OSLF.Binding.bindArgs]

/-- A local executable condition tests complete source rows. Equal labels,
categories and arities alone do not establish this condition. -/
def unique? (language : LanguageDef) (category unit : String) : Bool :=
  match language.terms.filter (rowMatches category unit) with
  | [] => true
  | first :: rest => rest.all (fun later => decide (later = first))

private theorem unique_members {rows : List GrammarRule}
    (same : (match rows with | [] => true | first :: rest => rest.all (fun later => decide (later = first))) = true)
    {first second : GrammarRule} (left : first ∈ rows) (right : second ∈ rows) : first = second := by
  cases rows with
  | nil => cases left
  | cons head tail =>
      have each : ∀ row ∈ tail, row = head := by simpa only [List.all_eq_true, decide_eq_true_eq] using same
      have l : first = head := (List.mem_cons.mp left).elim id (each first)
      have r : second = head := (List.mem_cons.mp right).elim id (each second)
      exact l.trans r.symm

theorem unique?_sound (unique : unique? language category unit = true)
    (first second : SelectedUnit language category unit) : first.rule = second.rule := by
  apply unique_members unique
  · exact List.mem_filter.mpr ⟨first.authored, by
      simp only [rowMatches, first.labelled, first.sorted, first.nullary, and_self, decide_true]⟩
  · exact List.mem_filter.mpr ⟨second.authored, by
      simp only [rowMatches, second.labelled, second.sorted, second.nullary, and_self, decide_true]⟩

theorem unique?_complete
    (unique : ∀ first second : SelectedUnit language category unit, first.rule = second.rule) :
    unique? language category unit = true := by
  unfold unique?
  generalize rowsEqual : language.terms.filter (rowMatches category unit) = rows
  cases rows with
  | nil => rfl
  | cons first rest =>
      simp only [List.all_eq_true, decide_eq_true_eq]
      intro second member
      have firstMember : first ∈ language.terms.filter (rowMatches category unit) := by
        rw [rowsEqual]
        exact List.mem_cons_self
      have secondMember : second ∈ language.terms.filter (rowMatches category unit) := by
        rw [rowsEqual]
        exact List.mem_cons_of_mem _ member
      exact unique (ofFiltered secondMember) (ofFiltered firstMember)

theorem unique?_exact (language : LanguageDef) (category unit : String) :
    unique? language category unit = true ↔
      ∀ first second : SelectedUnit language category unit, first.rule = second.rule :=
  ⟨fun accepted first second => unique?_sound accepted first second, unique?_complete⟩

theorem same_row_iff (first second : SelectedUnit language category unit) :
    first.rule = second.rule ↔ first = second := by
  constructor
  · intro same
    cases first
    cases second
    cases same
    rfl
  · exact congrArg SelectedUnit.rule

theorem term_equal_of_same_row (first second : SelectedUnit language category unit)
    (same : first.rule = second.rule) {Γ : List TypeExpr} : first.term (Γ := Γ) = second.term := by
  cases first with
  | mk firstRule firstMember firstLabel firstCategory firstEmpty =>
      cases second with
      | mk secondRule secondMember secondLabel secondCategory secondEmpty =>
          cases same
          rfl

@[simp] theorem constructorRow?_term (selected : SelectedUnit language category unit)
    {Γ : List TypeExpr} : constructorRow? (selected.term (Γ := Γ)) = some selected.rule := by
  rcases selected with ⟨rule, member, labelled, sorted, empty⟩
  cases sorted
  rfl

theorem term_same_row_iff (first second : SelectedUnit language category unit) {Γ : List TypeExpr} :
    first.term (Γ := Γ) = second.term ↔ first.rule = second.rule := by
  constructor
  · intro same
    have observed := congrArg constructorRow? same
    simpa only [constructorRow?_term, Option.some.injEq] using observed
  · intro same
    exact term_equal_of_same_row first second same (Γ := Γ)

theorem term_equal_of_unique (unique : unique? language category unit = true)
    (first second : SelectedUnit language category unit) {Γ : List TypeExpr} : first.term (Γ := Γ) = second.term :=
  term_equal_of_same_row first second (unique?_sound unique first second)

end SelectedUnit

/-- Validate an actual collection-algebra row and its authored unit inventory.
The parameter name is submitted data and is checked against the literal row. -/
def checkedAlgebra? (language : LanguageDef) (rule : GrammarRule) (kind : CollType)
    (algebra : CollectionAlgebra) (parameter : String) :
    Option (PLift (AlgebraRule language rule kind algebra)) :=
  if member : rule ∈ language.terms then
    if declared : rule.algebra? = some algebra then
      if shape : rule.params = [.simple parameter (.collection kind (.base rule.category))] then
        match unitRead : algebra.unit with
        | none => some ⟨⟨member, declared, ⟨parameter, shape⟩, by
            intro unit impossible
            rw [unitRead] at impossible
            cases impossible⟩⟩
        | some unit =>
            match SelectedUnit.find? language rule.category unit with
            | none => none
            | some selected => some ⟨⟨member, declared, ⟨parameter, shape⟩, by
                intro supplied isUnit
                rw [unitRead] at isUnit
                have same := Option.some.inj isUnit
                cases same
                exact ⟨selected.rule, selected.authored, selected.labelled,
                  selected.sorted, selected.nullary⟩⟩⟩
      else none
    else none
  else none

theorem checkedAlgebra?_complete {language : LanguageDef} {rule : GrammarRule} {kind : CollType}
    {algebra : CollectionAlgebra} {parameter : String}
    (declaration : AlgebraRule language rule kind algebra)
    (shape : rule.params = [.simple parameter (.collection kind (.base rule.category))]) :
    ∃ receipt, checkedAlgebra? language rule kind algebra parameter = some receipt := by
  unfold checkedAlgebra?
  simp only [declaration.authored, declaration.declared, shape, dite_true]
  split
  · exact ⟨_, rfl⟩
  · rename_i unit read
    obtain ⟨unitRule, member, labelled, sorted, empty⟩ := declaration.unitAuthored unit read
    obtain ⟨selected, found⟩ := SelectedUnit.find?_complete
      (⟨unitRule, member, labelled, sorted, empty⟩ : SelectedUnit language rule.category unit)
    simp only [found]
    exact ⟨⟨declaration⟩, True.intro⟩

theorem checkedAlgebra?_exact (language : LanguageDef) (rule : GrammarRule) (kind : CollType)
    (algebra : CollectionAlgebra) (parameter : String) :
    (∃ receipt, checkedAlgebra? language rule kind algebra parameter = some receipt) ↔
      rule.params = [.simple parameter (.collection kind (.base rule.category))] ∧
        AlgebraRule language rule kind algebra := by
  constructor
  · rintro ⟨receipt, accepted⟩
    refine ⟨?_, receipt.down⟩
    unfold checkedAlgebra? at accepted
    split at accepted
    · split at accepted
      · split at accepted
        · assumption
        · cases accepted
      · cases accepted
    · cases accepted
  · rintro ⟨shape, declaration⟩
    exact checkedAlgebra?_complete declaration shape

/-- The old mathematical choice is exposed only for comparison. Execution
uses SelectedUnit.find? or an explicitly checked selected source row. -/
noncomputable def originalUnit {language : LanguageDef} (rule : GrammarRule) (kind : CollType)
    (algebra : CollectionAlgebra) (declaration : AlgebraRule language rule kind algebra)
    (unit : String) (isUnit : algebra.unit = some unit) : SelectedUnit language rule.category unit :=
  let found := declaration.unitAuthored unit isUnit
  let unitRule := Classical.choose found
  let data := Classical.choose_spec found
  ⟨unitRule, data.1, data.2.1, data.2.2.1, data.2.2.2⟩

noncomputable def declaredUnit {language : LanguageDef} (rule : GrammarRule) (kind : CollType)
    (algebra : CollectionAlgebra) (declaration : AlgebraRule language rule kind algebra)
    (unit : String) (isUnit : algebra.unit = some unit) {Γ : List TypeExpr} :
    Term (signatureOf language) Γ (.base rule.category) :=
  let found := declaration.unitAuthored unit isUnit
  let unitRule := Classical.choose found
  let data := Classical.choose_spec found
  congrArg TypeExpr.base data.2.2.1 ▸ nullary unitRule data.1 data.2.2.2

theorem erase_declaredUnit {language : LanguageDef} (rule : GrammarRule) (kind : CollType)
    (algebra : CollectionAlgebra) (declaration : AlgebraRule language rule kind algebra)
    (unit : String) (isUnit : algebra.unit = some unit) {Γ : List TypeExpr} :
    erase (declaredUnit (Γ := Γ) rule kind algebra declaration unit isUnit) = .apply unit [] := by
  unfold declaredUnit
  rw [erase_type_cast, erase_nullary, (Classical.choose_spec
    (declaration.unitAuthored unit isUnit)).2.1]

theorem originalUnit_term {language : LanguageDef} (rule : GrammarRule) (kind : CollType)
    (algebra : CollectionAlgebra) (declaration : AlgebraRule language rule kind algebra)
    (unit : String) (isUnit : algebra.unit = some unit) {Γ : List TypeExpr} :
    (originalUnit rule kind algebra declaration unit isUnit).term (Γ := Γ) =
      declaredUnit rule kind algebra declaration unit isUnit := rfl

/-- Local full-row uniqueness is sufficient for exact intrinsic agreement.
No uniqueness assumption is required for the erased observer comparison. -/
theorem selectedUnit_eq_original_of_unique {language : LanguageDef} (rule : GrammarRule) (kind : CollType)
    (algebra : CollectionAlgebra) (declaration : AlgebraRule language rule kind algebra)
    (unit : String) (isUnit : algebra.unit = some unit)
    (unique : SelectedUnit.unique? language rule.category unit = true)
    (selected : SelectedUnit language rule.category unit) {Γ : List TypeExpr} :
    selected.term (Γ := Γ) = declaredUnit rule kind algebra declaration unit isUnit :=
  (SelectedUnit.term_equal_of_unique unique selected (originalUnit rule kind algebra declaration unit isUnit)).trans
    (originalUnit_term rule kind algebra declaration unit isUnit)

def unitEliminationWith {language : LanguageDef} (rule : GrammarRule) (kind : CollType)
    (algebra : CollectionAlgebra) (declaration : AlgebraRule language rule kind algebra)
    (parameter : String)
    (shape : rule.params = [.simple parameter (.collection kind (.base rule.category))])
    (unit : String) (isUnit : algebra.unit = some unit)
    (selected : SelectedUnit language rule.category unit) {Γ : List TypeExpr}
    (pre post : List (Term (signatureOf language) Γ (.base rule.category))) :
    DeclaredAxiom language where
  context := Γ
  category := rule.category
  left := node rule declaration.authored parameter kind shape
    (pre ++ selected.term :: post)
  right := node rule declaration.authored parameter kind shape (pre ++ post)
  source := .collection kind (pre.map erase ++ .apply unit [] :: post.map erase) none
  target := .collection kind (pre.map erase ++ post.map erase) none
  leftErases := by simp only [erase_node, List.map_append, List.map_cons, SelectedUnit.erase_term]
  rightErases := by simp only [erase_node, List.map_append]
  witness := .unitElim rule kind algebra unit _ _ declaration isUnit
    (by simpa only [List.map_append, List.map_cons, SelectedUnit.erase_term] using
      (sorted_node rule declaration.authored parameter kind shape
        (pre ++ selected.term :: post)))
  sameCategory := rfl

def emptyUnitWith {language : LanguageDef} (rule : GrammarRule) (kind : CollType)
    (algebra : CollectionAlgebra) (declaration : AlgebraRule language rule kind algebra)
    (parameter : String)
    (shape : rule.params = [.simple parameter (.collection kind (.base rule.category))])
    (unit : String) (isUnit : algebra.unit = some unit)
    (selected : SelectedUnit language rule.category unit) {Γ : List TypeExpr} :
    DeclaredAxiom language where
  context := Γ
  category := rule.category
  left := node rule declaration.authored parameter kind shape []
  right := selected.term
  source := .collection kind [] none
  target := .apply unit []
  leftErases := by rw [erase_node]; rfl
  rightErases := SelectedUnit.erase_term selected
  witness := .emptyUnit rule kind algebra unit declaration isUnit
    (sorted_node (Γ := Γ) rule declaration.authored parameter kind shape [])
  sameCategory := rfl

noncomputable def unitElimination {language : LanguageDef} (rule : GrammarRule) (kind : CollType)
    (algebra : CollectionAlgebra) (declaration : AlgebraRule language rule kind algebra)
    (parameter : String)
    (shape : rule.params = [.simple parameter (.collection kind (.base rule.category))])
    (unit : String) (isUnit : algebra.unit = some unit) {Γ : List TypeExpr}
    (pre post : List (Term (signatureOf language) Γ (.base rule.category))) :
    DeclaredAxiom language :=
  unitEliminationWith rule kind algebra declaration parameter shape unit isUnit
    (originalUnit rule kind algebra declaration unit isUnit) pre post

noncomputable def emptyUnit {language : LanguageDef} (rule : GrammarRule) (kind : CollType)
    (algebra : CollectionAlgebra) (declaration : AlgebraRule language rule kind algebra)
    (parameter : String)
    (shape : rule.params = [.simple parameter (.collection kind (.base rule.category))])
    (unit : String) (isUnit : algebra.unit = some unit) {Γ : List TypeExpr} :
    DeclaredAxiom language :=
  emptyUnitWith (Γ := Γ) rule kind algebra declaration parameter shape unit isUnit
    (originalUnit rule kind algebra declaration unit isUnit)

/-- Every declaring-rule-certified family axiom has its full contextual law
in the actual constructed binding quotient. -/
noncomputable abbrev algebra (language : LanguageDef) :=
  BindingEquationFamilyModel.algebra (family language)

theorem full_contextual_satisfaction (language : LanguageDef) :
    BindingEquationFamilyModel.Satisfies (algebra language) (family language) :=
  BindingEquationFamilyModel.algebra_satisfies (family language)


end Mettapedia.GSLT.LanguageDef.BindingSyntax.CollectionEquationFamily
