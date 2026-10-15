import Mettapedia.GSLT.LanguageDef.DefinitionalEquations

/-!
# Unfolding decides the equality that definitions generate

A list of definitions is acyclic, in authored order, when every definition
is well formed, the heads are distinct, and no body mentions its own head or
the head of a later definition. A language is presented by such a list when
its authored equations are exactly those definitions.

Full unfolding applies the last definition first. For a language presented
by an acyclic list, with no collection laws, two patterns are equal in the
language's equation theory exactly when their full unfoldings are the same
pattern. The equation theory is the one every language definition has; no
second notion of definitional equality is introduced.

The proof removes one definition at a time. Unfolding the last definition
maps the theory of the whole list into the theory of the earlier ones, and
the empty list generates syntactic equality.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DefinitionalEquations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.EquationSemantics

/-- Definitions in authored order, each depending only on earlier ones. -/
structure Acyclic (rows : List Row) : Prop where
  wellFormed : ∀ row ∈ rows, row.WellFormed
  distinctHeads : rows.Pairwise (fun earlier later => earlier.head ≠ later.head)
  ownHead : ∀ row ∈ rows, Avoids row.head row.body
  laterHeads : rows.Pairwise (fun earlier later => Avoids later.head earlier.body)

namespace Acyclic

theorem nil : Acyclic [] :=
  ⟨by simp, List.Pairwise.nil, by simp, List.Pairwise.nil⟩

/-- Dropping the last definition keeps the list acyclic. -/
theorem init {rows : List Row} {row : Row} (acyclic : Acyclic (rows ++ [row])) :
    Acyclic rows :=
  ⟨fun other member => acyclic.wellFormed other (List.mem_append_left _ member),
    (List.pairwise_append.mp acyclic.distinctHeads).1,
    fun other member => acyclic.ownHead other (List.mem_append_left _ member),
    (List.pairwise_append.mp acyclic.laterHeads).1⟩

/-- What the last definition contributes: it is well formed, its body does
not mention its head, and every earlier definition has a different head and
a body that does not mention it. -/
theorem last {rows : List Row} {row : Row} (acyclic : Acyclic (rows ++ [row])) :
    row.WellFormed ∧ Avoids row.head row.body ∧
      ∀ earlier ∈ rows, earlier.WellFormed ∧ earlier.head ≠ row.head ∧
        Avoids row.head earlier.body :=
  ⟨acyclic.wellFormed row (by simp), acyclic.ownHead row (by simp),
    fun earlier member =>
      ⟨acyclic.wellFormed earlier (List.mem_append_left _ member),
        (List.pairwise_append.mp acyclic.distinctHeads).2.2 earlier member row (by simp),
        (List.pairwise_append.mp acyclic.laterHeads).2.2 earlier member row (by simp)⟩⟩

/-- Dropping the first definition keeps the list acyclic. -/
theorem tail {rows : List Row} {row : Row} (acyclic : Acyclic (row :: rows)) : Acyclic rows :=
  ⟨fun other member => acyclic.wellFormed other (List.mem_cons_of_mem _ member),
    (List.pairwise_cons.mp acyclic.distinctHeads).2,
    fun other member => acyclic.ownHead other (List.mem_cons_of_mem _ member),
    (List.pairwise_cons.mp acyclic.laterHeads).2⟩

/-- What the first definition contributes: it is well formed, and its body
mentions neither its own head nor the head of any later definition. -/
theorem first {rows : List Row} {row : Row} (acyclic : Acyclic (row :: rows)) :
    row.WellFormed ∧ Avoids row.head row.body ∧ ∀ later ∈ rows, Avoids later.head row.body :=
  ⟨acyclic.wellFormed row (by simp), acyclic.ownHead row (by simp),
    (List.pairwise_cons.mp acyclic.laterHeads).1⟩

end Acyclic

/-- The language's authored equations are exactly these definitions. -/
structure Presents (language : LanguageDef) (rows : List Row) : Prop where
  defined : ∀ equation ∈ language.equations, ∃ row ∈ rows, Defines equation row
  authored : ∀ row ∈ rows, ∃ equation ∈ language.equations, Defines equation row

theorem forall₂_members {equations : List Equation} {rows : List Row}
    (pointwise : List.Forall₂ Defines equations rows) :
    (∀ equation ∈ equations, ∃ row ∈ rows, Defines equation row) ∧
      (∀ row ∈ rows, ∃ equation ∈ equations, Defines equation row) := by
  induction pointwise with
  | nil => exact ⟨by simp, by simp⟩
  | cons defines _ inductionHypothesis =>
    obtain ⟨forward, backward⟩ := inductionHypothesis
    constructor
    · intro equation member
      rcases List.mem_cons.mp member with rfl | inTail
      · exact ⟨_, by simp, defines⟩
      · obtain ⟨row, rowMember, rowDefines⟩ := forward equation inTail
        exact ⟨row, List.mem_cons_of_mem _ rowMember, rowDefines⟩
    · intro row member
      rcases List.mem_cons.mp member with rfl | inTail
      · exact ⟨_, by simp, defines⟩
      · obtain ⟨equation, equationMember, equationDefines⟩ := backward row inTail
        exact ⟨equation, List.mem_cons_of_mem _ equationMember, equationDefines⟩

/-- Equations that state the rows one each, in order, present them. -/
theorem presents_of_forall₂ {language : LanguageDef} {rows : List Row}
    (pointwise : List.Forall₂ Defines language.equations rows) : Presents language rows :=
  ⟨(forall₂_members pointwise).1, (forall₂_members pointwise).2⟩

/-- Full unfolding: the last definition first. -/
def expand (rows : List Row) (pattern : Pattern) : Pattern :=
  rows.foldr unfoldOne pattern

@[simp]
theorem expand_nil (pattern : Pattern) : expand [] pattern = pattern := rfl

theorem expand_cons (row : Row) (rows : List Row) (pattern : Pattern) :
    expand (row :: rows) pattern = unfoldOne row (expand rows pattern) := rfl

theorem expand_append_singleton (rows : List Row) (row : Row) (pattern : Pattern) :
    expand (rows ++ [row]) pattern = expand rows (unfoldOne row pattern) := by
  simp [expand, List.foldr_append]

/-- The language without the equations that state one definition. -/
def without (language : LanguageDef) (row : Row) : LanguageDef :=
  { language with
    equations := language.equations.filter (fun equation => decide (equation.left ≠ row.left)) }

theorem left_ne_of_head_ne {first second : Row} (differs : first.head ≠ second.head) :
    first.left ≠ second.left := by
  intro same
  simp only [Row.left, Pattern.apply.injEq] at same
  exact differs same.1

theorem Presents.without {language : LanguageDef} {rows : List Row} {row : Row}
    (presents : Presents language (rows ++ [row]))
    (differs : ∀ earlier ∈ rows, earlier.head ≠ row.head) :
    Presents (without language row) rows := by
  constructor
  · intro equation member
    obtain ⟨authored, kept⟩ := List.mem_filter.mp member
    obtain ⟨other, otherMember, defines⟩ := presents.defined equation authored
    rcases List.mem_append.mp otherMember with earlier | isRow
    · exact ⟨other, earlier, defines⟩
    · have same : other = row := by simpa using isRow
      subst same
      exact absurd defines.left (by simpa using kept)
  · intro earlier member
    obtain ⟨equation, authored, defines⟩ :=
      presents.authored earlier (List.mem_append_left _ member)
    refine ⟨equation, List.mem_filter.mpr ⟨authored, ?_⟩, defines⟩
    rw [decide_eq_true_iff, defines.left]
    exact left_ne_of_head_ne (differs earlier member)

section NormalForms

variable {base : BasePremiseEvaluator}

/-- Equal patterns have the same full unfolding. -/
theorem expand_eq_of_equationEquiv :
    ∀ rows : List Row, Acyclic rows → ∀ language : LanguageDef, Presents language rows →
      language.usesCollection .hashBag = false → language.usesCollection .hashSet = false →
      language.hasAlgebraDeclarations = false →
      ∀ {left right : Pattern}, EquationEquiv base language left right →
        expand rows left = expand rows right := by
  intro rows
  induction rows using List.reverseRecOn with
  | nil =>
    intro _ language presents noBags noSets noAlgebra left right equivalent
    have empty : language.equations = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro equation member
      obtain ⟨row, rowMember, -⟩ := presents.defined equation member
      cases rowMember
    have free : language.isEquationFree = true := by
      simp [LanguageDef.isEquationFree, empty, noBags, noSets, noAlgebra]
    exact (equationEquiv_iff_eq_of_no_generators free left right).mp equivalent
  | append_singleton rows row inductionHypothesis =>
    intro acyclic language presents noBags noSets noAlgebra left right equivalent
    obtain ⟨rowFormed, rowOwn, earlier⟩ := acyclic.last
    have classified : ∀ equation ∈ language.equations,
        Defines equation row ∨
          ∃ other : Row, Defines equation other ∧ other.WellFormed ∧ other.head ≠ row.head ∧
            Avoids row.head other.body ∧
            equation ∈ (without language row).equations := by
      intro equation authored
      obtain ⟨other, otherMember, defines⟩ := presents.defined equation authored
      rcases List.mem_append.mp otherMember with before | isRow
      · obtain ⟨otherFormed, differs, absent⟩ := earlier other before
        refine Or.inr ⟨other, defines, otherFormed, differs, absent,
          List.mem_filter.mpr ⟨authored, ?_⟩⟩
        rw [decide_eq_true_iff, defines.left]
        exact left_ne_of_head_ne differs
      · have same : other = row := by simpa using isRow
        subst same
        exact Or.inl defines
    have pass := equationEquiv_unfoldOne_pass (base := base) (smaller := without language row)
      (no_derivedInstance_of_no_derived_laws noBags noSets noAlgebra) rowFormed rowOwn
      classified equivalent
    rw [expand_append_singleton, expand_append_singleton]
    exact inductionHypothesis acyclic.init (without language row)
      (presents.without (fun other member => (earlier other member).2.1))
      noBags noSets noAlgebra pass

/-- Every pattern is equal to its full unfolding. -/
theorem equationEquiv_expand {language : LanguageDef} :
    ∀ rows : List Row,
      (∀ row ∈ rows, row.WellFormed ∧ ∃ equation ∈ language.equations, Defines equation row) →
      ∀ pattern : Pattern, EquationEquiv base language pattern (expand rows pattern)
  | [], _, pattern => Relation.EqvGen.refl pattern
  | row :: rows, every, pattern => by
      obtain ⟨formed, equation, authored, defines⟩ := every row (by simp)
      have inner := equationEquiv_expand rows
        (fun other member => every other (by simp [member])) pattern
      have outer := equationEquiv_unfoldOne (base := base) authored defines formed
        (expand rows pattern)
      exact Relation.EqvGen.trans _ _ _ inner outer

/-- **Normal forms.** In a language presented by an acyclic list of
definitions, with no collection laws, the equation theory is equality of
full unfoldings. -/
theorem equationEquiv_iff_expand_eq {language : LanguageDef} {rows : List Row}
    (acyclic : Acyclic rows) (presents : Presents language rows)
    (noBags : language.usesCollection .hashBag = false)
    (noSets : language.usesCollection .hashSet = false)
    (noAlgebra : language.hasAlgebraDeclarations = false) (left right : Pattern) :
    EquationEquiv base language left right ↔ expand rows left = expand rows right := by
  constructor
  · exact expand_eq_of_equationEquiv rows acyclic language presents noBags noSets noAlgebra
  · intro same
    have every : ∀ row ∈ rows,
        row.WellFormed ∧ ∃ equation ∈ language.equations, Defines equation row :=
      fun row member => ⟨acyclic.wellFormed row member, presents.authored row member⟩
    have toLeft := equationEquiv_expand (base := base) rows every left
    have toRight := equationEquiv_expand (base := base) rows every right
    rw [same] at toLeft
    exact Relation.EqvGen.trans _ _ _ toLeft (Relation.EqvGen.symm _ _ toRight)

/-- The equation theory of such a language is decidable. -/
noncomputable def decideEquationEquiv {language : LanguageDef} {rows : List Row}
    (acyclic : Acyclic rows) (presents : Presents language rows)
    (noBags : language.usesCollection .hashBag = false)
    (noSets : language.usesCollection .hashSet = false)
    (noAlgebra : language.hasAlgebraDeclarations = false) (left right : Pattern) :
    Decidable (EquationEquiv base language left right) :=
  decidable_of_iff _
    (equationEquiv_iff_expand_eq acyclic presents noBags noSets noAlgebra left right).symm

end NormalForms

/-! ## Unfolding commutes with instantiation

A rule or a definition is instantiated by substituting an argument vector
for its metavariables. Unfolding the instance is instantiating the unfolded
schema at the unfolded arguments. This is what lets a derivation be
transported along full unfolding, rule instance by rule instance. -/

section Instantiation

open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules

theorem applyBindings_cons_eq (name : String) (value : Pattern) (rest : Bindings) :
    applyBindings ((name, value) :: rest) (.fvar name) = value :=
  applyBindings_fvar_of_find (entry := (name, value)) (by simp)

theorem applyBindings_cons_ne {head name : String} (differs : head ≠ name) (value : Pattern)
    (rest : Bindings) :
    applyBindings ((head, value) :: rest) (.fvar name) = applyBindings rest (.fvar name) := by
  cases found : rest.find? (fun entry => entry.1 == name) with
  | none =>
    have whole : ((head, value) :: rest).find? (fun entry => entry.1 == name) = none := by
      simp [differs, found]
    rw [applyBindings_fvar_of_not_find whole, applyBindings_fvar_of_not_find found]
  | some entry =>
    have whole : ((head, value) :: rest).find? (fun entry => entry.1 == name) = some entry := by
      simp [differs, found]
    rw [applyBindings_fvar_of_find whole, applyBindings_fvar_of_find found]

/-- A bound metavariable takes one of the supplied values; an unbound one
stays as it is. -/
theorem applyBindings_zip_value (name : String) :
    ∀ (names : List String) (values : List Pattern),
      applyBindings (names.zip values) (.fvar name) = .fvar name ∨
        applyBindings (names.zip values) (.fvar name) ∈ values
  | [], _ => Or.inl (applyBindings_fvar_of_not_find (by simp))
  | _ :: _, [] => Or.inl (applyBindings_fvar_of_not_find (by simp))
  | head :: names, value :: values => by
      by_cases same : head = name
      · subst same
        rw [List.zip_cons_cons, applyBindings_cons_eq]
        exact Or.inr (by simp)
      · rw [List.zip_cons_cons, applyBindings_cons_ne same]
        rcases applyBindings_zip_value name names values with unbound | member
        · exact Or.inl unbound
        · exact Or.inr (List.mem_cons_of_mem _ member)

theorem applyBindings_zip_mem {name : String} :
    ∀ {names : List String} {values : List Pattern}, name ∈ names →
      names.length = values.length → applyBindings (names.zip values) (.fvar name) ∈ values
  | [], _, member, _ => by cases member
  | _ :: _, [], _, lengths => by simp at lengths
  | head :: names, value :: values, member, lengths => by
      by_cases same : head = name
      · subst same
        rw [List.zip_cons_cons, applyBindings_cons_eq]
        simp
      · rw [List.zip_cons_cons, applyBindings_cons_ne same]
        have inTail : name ∈ names := by
          rcases List.mem_cons.mp member with equal | inTail
          · exact absurd equal.symm same
          · exact inTail
        exact List.mem_cons_of_mem _ (applyBindings_zip_mem inTail (by simpa using lengths))

/-- Mapping the values commutes with looking a bound metavariable up. -/
theorem applyBindings_zip_mapValues (function : Pattern → Pattern) {name : String} :
    ∀ {names : List String} {values : List Pattern}, name ∈ names →
      names.length = values.length →
        applyBindings (names.zip (values.map function)) (.fvar name) =
          function (applyBindings (names.zip values) (.fvar name))
  | [], _, member, _ => by cases member
  | _ :: _, [], _, lengths => by simp at lengths
  | head :: names, value :: values, member, lengths => by
      by_cases same : head = name
      · subst same
        rw [List.map_cons, List.zip_cons_cons, List.zip_cons_cons, applyBindings_cons_eq,
          applyBindings_cons_eq]
      · have inTail : name ∈ names := by
          rcases List.mem_cons.mp member with equal | inTail
          · exact absurd equal.symm same
          · exact inTail
        rw [List.map_cons, List.zip_cons_cons, List.zip_cons_cons, applyBindings_cons_ne same,
          applyBindings_cons_ne same]
        exact applyBindings_zip_mapValues function inTail (by simpa using lengths)

/-- Substituting into an instance is instantiating at the substituted
arguments. -/
theorem applyBindings_comp_zip (outer : Bindings) {names : List String}
    {values : List Pattern} (lengths : names.length = values.length) :
    ∀ pattern : Pattern, Schema names pattern →
      applyBindings outer (applyBindings (names.zip values) pattern) =
        applyBindings (names.zip (values.map (applyBindings outer))) pattern
  | .fvar _, schema => by
      cases schema with
      | metavariable member =>
        exact (applyBindings_zip_mapValues (applyBindings outer) member lengths).symm
  | .apply constructor arguments, schema => by
      cases schema with
      | constructor schemas =>
        rw [applyBindings_apply, applyBindings_apply, applyBindings_apply, List.map_map]
        congr 1
        apply List.map_congr_left
        intro argument member
        exact applyBindings_comp_zip outer lengths argument (schemas.member member)
  | .bvar _, schema => by cases schema
  | .lambda _ _, schema => by cases schema
  | .multiLambda _ _ _, schema => by cases schema
  | .subst _ _, schema => by cases schema
  | .collection _ _ _, schema => by cases schema
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

/-- Unfolding an instance of any schema is instantiating the unfolded schema
at the unfolded values. -/
theorem unfoldOne_applyBindings_schema {row : Row} (formed : row.WellFormed)
    {names : List String} (bindings : Bindings) :
    ∀ pattern : Pattern, Schema names pattern →
      unfoldOne row (applyBindings bindings pattern) =
        applyBindings (mapValues (unfoldOne row) bindings) (unfoldOne row pattern)
  | .fvar name, _ => by
      rw [unfoldOne_fvar]
      exact (applyBindings_mapValues_fvar (unfoldOne row) (unfoldOne_fvar row) bindings name).symm
  | .apply constructor arguments, schema => by
      cases schema with
      | constructor schemas =>
        have pointwise : (arguments.map (applyBindings bindings)).map (unfoldOne row) =
            (arguments.map (unfoldOne row)).map
              (applyBindings (mapValues (unfoldOne row) bindings)) := by
          rw [List.map_map, List.map_map]
          apply List.map_congr_left
          intro argument member
          exact unfoldOne_applyBindings_schema formed bindings argument (schemas.member member)
        rw [applyBindings_apply, unfoldOne_apply, unfoldOne_apply, List.length_map]
        by_cases saturated : constructor = row.head ∧ arguments.length = row.formals.length
        · rw [if_pos saturated, if_pos saturated,
            applyBindings_comp_zip _ (by simp [saturated.2]) row.body formed.schema, pointwise]
        · rw [if_neg saturated, if_neg saturated, applyBindings_apply, pointwise]
  | .bvar _, schema => by cases schema
  | .lambda _ _, schema => by cases schema
  | .multiLambda _ _ _, schema => by cases schema
  | .subst _ _, schema => by cases schema
  | .collection _ _ _, schema => by cases schema
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

theorem schemas_of_forall {names : List String} :
    ∀ patterns : List Pattern, (∀ pattern ∈ patterns, Schema names pattern) →
      Schemas names patterns
  | [], _ => .nil
  | pattern :: patterns, every =>
      .cons (every pattern (by simp))
        (schemas_of_forall patterns (fun other member => every other (by simp [member])))

/-- An instance of a schema at schemas is a schema. -/
theorem schema_applyBindings_zip {formals names : List String} {values : List Pattern}
    (lengths : formals.length = values.length)
    (every : ∀ value ∈ values, Schema names value) :
    ∀ pattern : Pattern, Schema formals pattern →
      Schema names (applyBindings (formals.zip values) pattern)
  | .fvar _, schema => by
      cases schema with
      | metavariable member => exact every _ (applyBindings_zip_mem member lengths)
  | .apply constructor arguments, schema => by
      cases schema with
      | constructor schemas =>
        rw [applyBindings_apply]
        apply Schema.constructor
        apply schemas_of_forall
        exact List.forall_mem_map.mpr (fun argument member =>
          schema_applyBindings_zip lengths every argument (schemas.member member))
  | .bvar _, schema => by cases schema
  | .lambda _ _, schema => by cases schema
  | .multiLambda _ _ _, schema => by cases schema
  | .subst _ _, schema => by cases schema
  | .collection _ _ _, schema => by cases schema
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

/-- Unfolding a schema gives a schema over the same metavariables. -/
theorem schema_unfoldOne {row : Row} (formed : row.WellFormed) {names : List String} :
    ∀ pattern : Pattern, Schema names pattern → Schema names (unfoldOne row pattern)
  | .fvar _, schema => by
      rw [unfoldOne_fvar]
      exact schema
  | .apply constructor arguments, schema => by
      cases schema with
      | constructor schemas =>
        have every : ∀ value ∈ arguments.map (unfoldOne row), Schema names value :=
          List.forall_mem_map.mpr (fun argument member =>
            schema_unfoldOne formed argument (schemas.member member))
        rw [unfoldOne_apply]
        split
        · rename_i saturated
          exact schema_applyBindings_zip (by simp [saturated.2]) every row.body formed.schema
        · exact Schema.constructor (schemas_of_forall _ every)
  | .bvar _, schema => by cases schema
  | .lambda _ _, schema => by cases schema
  | .multiLambda _ _ _, schema => by cases schema
  | .subst _ _, schema => by cases schema
  | .collection _ _ _, schema => by cases schema
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

theorem schema_expand {names : List String} :
    ∀ rows : List Row, (∀ row ∈ rows, row.WellFormed) →
      ∀ pattern : Pattern, Schema names pattern → Schema names (expand rows pattern)
  | [], _, _, schema => schema
  | row :: rows, every, pattern, schema =>
      schema_unfoldOne (every row (by simp)) _
        (schema_expand rows (fun other member => every other (by simp [member])) pattern schema)

theorem mapValues_zip (function : Pattern → Pattern) (names : List String)
    (values : List Pattern) :
    mapValues function (names.zip values) = names.zip (values.map function) := by
  induction names generalizing values with
  | nil => simp [mapValues]
  | cons head names inductionHypothesis =>
    cases values with
    | nil => simp [mapValues]
    | cons value values =>
      simpa [mapValues] using inductionHypothesis values

/-- Full unfolding of an instance is the instance of the fully unfolded
schema at the fully unfolded values. -/
theorem expand_applyBindings_zip {names : List String} :
    ∀ rows : List Row, (∀ row ∈ rows, row.WellFormed) →
      ∀ (values : List Pattern) (pattern : Pattern), Schema names pattern →
        expand rows (applyBindings (names.zip values) pattern) =
          applyBindings (names.zip (values.map (expand rows))) (expand rows pattern)
  | [], _, values, pattern, _ => by
      have same : values.map (expand []) = values := by
        induction values with
        | nil => rfl
        | cons value values inductionHypothesis => simp [inductionHypothesis]
      rw [same]
      rfl
  | row :: rows, every, values, pattern, schema => by
      have rest : ∀ other ∈ rows, other.WellFormed :=
        fun other member => every other (by simp [member])
      rw [expand_cons, expand_applyBindings_zip rows rest values pattern schema,
        unfoldOne_applyBindings_schema (every row (by simp)) _ _
          (schema_expand rows rest pattern schema),
        mapValues_zip, List.map_map]
      rfl

end Instantiation

end Mettapedia.GSLT.LanguageDef.DefinitionalEquations
