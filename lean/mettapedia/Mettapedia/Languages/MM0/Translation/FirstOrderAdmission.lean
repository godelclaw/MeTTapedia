import Mettapedia.Languages.MM0.Translation.FirstOrderRules
import Mettapedia.Languages.MM0.Kernel.SpecificationChecking
import Mettapedia.Languages.MM0.Kernel.SymbolSupport
import Mettapedia.Languages.MM0.Kernel.DependencyFreeTerms

/-!
# Sequential admission of compiled first-order modules

The generated declarations are checked in this order: sorts, the primitive
constructors, the definitions in authored order, and the axioms. Freshness
follows from source positions, and payload formation follows from the
admitted many-sorted presentation.

A definition is admitted over the terms that exist at that point: the
primitive constructors and the earlier definitions. Its body mentions no
other constructor, because the definitions are acyclic in authored order,
and typing reads only the declarations of the symbols that occur.

The chronological theory stores the same declarations as the compiler, in
the kernel's actual insertion order. Their signatures agree; no
preconstructed table is assumed to be admitted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.FirstOrderAdmission

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.DefinitionalEquations
open Kernel FirstOrderSyntax FirstOrderTyping FirstOrderConversion FirstOrderRules

/-! ## Finite tables with distinct keys -/

theorem lookup_of_mem {Value : Type} {entries : List (Nat × Value)}
    (distinct : (entries.map Prod.fst).Nodup) {key : Nat} {value : Value}
    (member : (key, value) ∈ entries) : entries.lookup key = some value := by
  induction entries with
  | nil => cases member
  | cons entry rest inductionHypothesis =>
    rcases entry with ⟨otherKey, otherValue⟩
    obtain ⟨fresh, restDistinct⟩ :=
      List.nodup_cons.mp (by simpa only [List.map_cons] using distinct)
    rcases List.mem_cons.mp member with same | inRest
    · cases same
      simp
    · have different : key ≠ otherKey := fun same =>
        fresh (same ▸ List.mem_map_of_mem (f := Prod.fst) inRest)
      simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr different, ↓reduceIte] using
        inductionHypothesis restDistinct inRest

theorem lookup_eq_none {Value : Type} {entries : List (Nat × Value)} {key : Nat}
    (absent : ∀ entry ∈ entries, entry.1 ≠ key) : entries.lookup key = none := by
  induction entries with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
    rcases entry with ⟨otherKey, otherValue⟩
    have different : key ≠ otherKey := fun same =>
      absent (otherKey, otherValue) (by simp) same.symm
    simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr different, ↓reduceIte] using
      inductionHypothesis (fun other member => absent other (List.mem_cons_of_mem _ member))

theorem mem_of_lookup {Value : Type} {entries : List (Nat × Value)} {key : Nat}
    {value : Value} (found : entries.lookup key = some value) : (key, value) ∈ entries := by
  induction entries with
  | nil => simp at found
  | cons entry rest inductionHypothesis =>
    rcases entry with ⟨otherKey, otherValue⟩
    by_cases same : key = otherKey
    · subst same
      have equal : otherValue = value := by simpa [List.lookup_cons] using found
      subst equal
      simp
    · have tail : rest.lookup key = some value := by
        simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr same, ↓reduceIte] using found
      exact List.mem_cons_of_mem _ (inductionHypothesis tail)

theorem lookup_append_left {Value : Type} (first second : List (Nat × Value)) {key : Nat}
    {value : Value} (found : first.lookup key = some value) :
    (first ++ second).lookup key = some value := by
  induction first with
  | nil => simp at found
  | cons entry rest inductionHypothesis =>
    rcases entry with ⟨otherKey, otherValue⟩
    by_cases same : key = otherKey
    · subst same
      simpa [List.lookup_cons] using found
    · have tail : rest.lookup key = some value := by
        simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr same, ↓reduceIte] using found
      simpa only [List.cons_append, List.lookup_cons, beq_eq_false_iff_ne.mpr same,
        ↓reduceIte] using inductionHypothesis tail

theorem lookup_append_right {Value : Type} (first second : List (Nat × Value)) {key : Nat}
    (absent : first.lookup key = none) : (first ++ second).lookup key = second.lookup key := by
  induction first with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
    rcases entry with ⟨otherKey, otherValue⟩
    by_cases same : key = otherKey
    · subst same
      simp at absent
    · have tail : rest.lookup key = none := by
        simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr same, ↓reduceIte] using absent
      simpa only [List.cons_append, List.lookup_cons, beq_eq_false_iff_ne.mpr same,
        ↓reduceIte] using inductionHypothesis tail

/-! ## The symbols of an encoded term -/

mutual
  /-- The term symbols of an encoding are the positions of the constructors
  of the encoded pattern. -/
  theorem encodes_symbolsWithin {names : List String} {allowed : String → Prop}
      {pattern : Pattern} {expression : Preterm} (encoded : Encodes names pattern expression)
      (within : ConstructorsWithin allowed pattern) :
      Preterm.SymbolsWithin (fun index => ∃ name, index? names name = some index ∧ allowed name)
        expression := by
    cases encoded with
    | boundVariable index => trivial
    | constructor found arguments =>
      rw [Preterm.symbolsWithin_applyArgs]
      exact ⟨⟨_, found, within.1⟩, encodesList_symbolsWithin arguments within.2⟩
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem encodesList_symbolsWithin {names : List String} {allowed : String → Prop}
      {patterns : List Pattern} {expressions : List Preterm}
      (encoded : List.Forall₂ (Encodes names) patterns expressions)
      (within : ConstructorListWithin allowed patterns) :
      ∀ expression ∈ expressions,
        Preterm.SymbolsWithin
          (fun index => ∃ name, index? names name = some index ∧ allowed name) expression := by
    cases encoded with
    | nil => simp
    | cons first rest =>
      intro expression member
      rcases List.mem_cons.mp member with same | inRest
      · rw [same]
        exact encodes_symbolsWithin first within.1
      · exact encodesList_symbolsWithin rest within.2 expression inRest
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

theorem constructorsWithin_numbered {allowed : String → Prop} {names : List String}
    {pattern : Pattern} (within : ConstructorsWithin allowed pattern) :
    ConstructorsWithin allowed (numbered names pattern) := by
  refine constructorsWithin_applyBindings within ?_
  rintro ⟨name, value⟩ member
  obtain ⟨index, -, rfl⟩ := List.mem_map.mp (List.of_mem_zip member).2
  trivial

/-! ## The declarations, in the order of admission -/

/-- Term rows of the constructors that no definition defines. -/
def primitiveTerms (source : Presentation) : List (Nat × TermDecl) :=
  List.compileIndexed
    (fun rule =>
      if checkPrimitive source.rows rule.label then
        declaration? source.syntaxSignature.sorts rule
      else none)
    source.syntaxSignature.language.terms

/-- A definition as the kernel admits it: the position of its head, its
term declaration and its body. -/
def definitionRow? (source : Presentation) (row : Row) :
    Option (Nat × TermDecl × Definition.Body) := do
  let index ← index? source.syntaxSignature.names row.head
  let declaration ← source.syntaxSignature.termSignature index
  let body ← definitionSignature source.syntaxSignature source.rows index
  pure (index, declaration, body)

/-- The definitions, in authored order. -/
def definitionRows (source : Presentation) : List (Nat × TermDecl × Definition.Body) :=
  source.rows.filterMap (definitionRow? source)

def admissions (source : Presentation) : List Admission :=
  source.theory.sorts.map (fun row => .sort row.1 row.2) ++
    (primitiveTerms source).map (fun row => .term row.1 row.2) ++
    (definitionRows source).map (fun row => .definition row.1 row.2.1 row.2.2) ++
    source.theory.theorems.map (fun row => .axiomDecl row.1 row.2)

/-- The term table once the definitions `passes` have been admitted after
the primitive constructors. -/
def termsAfter (source : Presentation) (passes : List Row) : List (Nat × TermDecl) :=
  ((passes.filterMap (definitionRow? source)).map fun row => (row.1, row.2.1)).reverse ++
    (primitiveTerms source).reverse

def chronological (source : Presentation) : Theory where
  sorts := source.theory.sorts.reverse
  terms := termsAfter source source.rows
  definitions := ((definitionRows source).map fun row => (row.1, row.2.2)).reverse
  theorems := source.theory.theorems.reverse

/-! ## What each row is -/

/-- A definition is admitted at the position of its head, with the compiled
declaration and body. -/
theorem definitionRow?_eq (source : Presentation) {row : Row} (member : row ∈ source.rows) :
    ∃ declaration expression,
      Compiled source.syntaxSignature source.rows row
        (source.syntaxSignature.names.idxOf row.head) declaration expression ∧
      definitionRow? source row =
        some (source.syntaxSignature.names.idxOf row.head, declaration, ⟨[], expression⟩) := by
  obtain ⟨index, declaration, expression, compiled⟩ :=
    compiled_exists source.definitionalRows member
  have position : index = source.syntaxSignature.names.idxOf row.head := by
    have found := compiled.name
    unfold index? at found
    split at found
    · exact (Option.some.inj found).symm
    · cases found
  subst position
  exact ⟨declaration, expression, compiled,
    by simp [definitionRow?, compiled.name, compiled.term, compiled.body]⟩

theorem head_mem_names (source : Presentation) {row : Row} (member : row ∈ source.rows) :
    row.head ∈ source.syntaxSignature.names := by
  obtain ⟨declaration, expression, compiled, -⟩ := definitionRow?_eq source member
  have found := compiled.name
  unfold index? at found
  split at found
  · assumption
  · cases found

theorem idxOf_head_injective (source : Presentation) {first second : Row}
    (firstMember : first ∈ source.rows) (secondMember : second ∈ source.rows)
    (same : source.syntaxSignature.names.idxOf first.head =
      source.syntaxSignature.names.idxOf second.head) : first.head = second.head := by
  have firstLookup := getElem?_index? (index?_some _ _ (head_mem_names source firstMember))
  have secondLookup := getElem?_index? (index?_some _ _ (head_mem_names source secondMember))
  rw [same] at firstLookup
  exact Option.some.inj (firstLookup.symm.trans secondLookup)

/-- The admitted definitions of a list of rows, as a list of the same
length and order. -/
theorem filterMap_definitionRow? (source : Presentation) :
    ∀ passes : List Row, (∀ row ∈ passes, row ∈ source.rows) →
      List.Forall₂ (fun row entry =>
        ∃ expression, Compiled source.syntaxSignature source.rows row entry.1 entry.2.1
            expression ∧
          entry.1 = source.syntaxSignature.names.idxOf row.head ∧
          entry.2.2 = ⟨[], expression⟩)
        passes (passes.filterMap (definitionRow? source))
  | [], _ => .nil
  | row :: passes, within => by
      obtain ⟨declaration, expression, compiled, computed⟩ :=
        definitionRow?_eq source (within row (by simp))
      rw [List.filterMap_cons_some computed]
      exact .cons ⟨expression, compiled, rfl, rfl⟩
        (filterMap_definitionRow? source passes
          (fun other member => within other (List.mem_cons_of_mem _ member)))

theorem mem_filterMap_definitionRow? (source : Presentation) {passes : List Row}
    (within : ∀ row ∈ passes, row ∈ source.rows) {entry : Nat × TermDecl × Definition.Body}
    (member : entry ∈ passes.filterMap (definitionRow? source)) :
    ∃ row ∈ passes, ∃ expression,
      Compiled source.syntaxSignature source.rows row entry.1 entry.2.1 expression ∧
        entry.1 = source.syntaxSignature.names.idxOf row.head ∧ entry.2.2 = ⟨[], expression⟩ := by
  obtain ⟨row, rowMember, computed⟩ := List.mem_filterMap.mp member
  obtain ⟨declaration, expression, compiled, expected⟩ :=
    definitionRow?_eq source (within row rowMember)
  have same := Option.some.inj (computed.symm.trans expected)
  subst same
  exact ⟨row, rowMember, expression, compiled, rfl, rfl⟩

/-- Distinct heads have distinct positions. -/
theorem definition_keys_nodup (source : Presentation) :
    ∀ passes : List Row, (∀ row ∈ passes, row ∈ source.rows) →
      passes.Pairwise (fun earlier later => earlier.head ≠ later.head) →
      ((passes.filterMap (definitionRow? source)).map fun entry => entry.1).Nodup
  | [], _, _ => by simp
  | row :: passes, within, distinct => by
      obtain ⟨declaration, expression, compiled, computed⟩ :=
        definitionRow?_eq source (within row (by simp))
      obtain ⟨fresh, restDistinct⟩ := List.pairwise_cons.mp distinct
      have later : ∀ other ∈ passes, other ∈ source.rows :=
        fun other member => within other (List.mem_cons_of_mem _ member)
      rw [List.filterMap_cons_some computed, List.map_cons, List.nodup_cons]
      refine ⟨?_, definition_keys_nodup source passes later restDistinct⟩
      intro inKeys
      obtain ⟨entry, entryMember, sameKey⟩ := List.mem_map.mp inKeys
      obtain ⟨other, otherMember, -, -, position, -⟩ :=
        mem_filterMap_definitionRow? source later entryMember
      exact fresh other otherMember
        (idxOf_head_injective source (within row (by simp)) (later other otherMember)
          (by rw [← position, sameKey]))

/-! ## Lookups in the term table -/

theorem primitiveTerms_lookup (source : Presentation) (index : Nat) :
    (primitiveTerms source).reverse.lookup index =
      source.syntaxSignature.language.terms[index]?.bind (fun rule =>
        if checkPrimitive source.rows rule.label then
          declaration? source.syntaxSignature.sorts rule
        else none) :=
  List.lookup_compileIndexed_reverse _ _ _

theorem names_getElem? (source : Presentation) (index : Nat) :
    source.syntaxSignature.names[index]? =
      (source.syntaxSignature.language.terms[index]?).map (·.label) := by
  simp [Signature.names, constructorNames, List.getElem?_map]

theorem primitiveTerms_lookup_forward (source : Presentation) (index : Nat) :
    (primitiveTerms source).lookup index =
      source.syntaxSignature.language.terms[index]?.bind (fun rule =>
        if checkPrimitive source.rows rule.label then
          declaration? source.syntaxSignature.sorts rule
        else none) :=
  List.lookup_compileIndexed_zero _ _ _

theorem primitiveTerms_keys (source : Presentation) :
    ((primitiveTerms source).map Prod.fst).Nodup :=
  List.compileIndexed_keys_nodup _ _

/-- A defined position is not a primitive one. -/
theorem primitiveTerms_lookup_defined (source : Presentation) {row : Row}
    (member : row ∈ source.rows) :
    (primitiveTerms source).reverse.lookup (source.syntaxSignature.names.idxOf row.head) =
      none := by
  rw [primitiveTerms_lookup]
  have nameLookup := getElem?_index? (index?_some _ _ (head_mem_names source member))
  rw [names_getElem?] at nameLookup
  cases position : source.syntaxSignature.language.terms[
      source.syntaxSignature.names.idxOf row.head]? with
  | none => rfl
  | some rule =>
    have label : rule.label = row.head := by simpa [position] using nameLookup
    have defined : checkPrimitive source.rows rule.label = false := by
      rw [Bool.eq_false_iff]
      intro primitive
      exact (checkPrimitive_iff _ _).mp primitive row member label
    simp [defined]

/-- Positions of the definitions already admitted hold their declarations. -/
theorem termsAfter_defined (source : Presentation) {passes : List Row}
    (within : ∀ row ∈ passes, row ∈ source.rows)
    (distinct : passes.Pairwise (fun earlier later => earlier.head ≠ later.head)) {row : Row}
    (member : row ∈ passes) :
    (termsAfter source passes).lookup (source.syntaxSignature.names.idxOf row.head) =
      source.syntaxSignature.termSignature (source.syntaxSignature.names.idxOf row.head) := by
  obtain ⟨declaration, expression, compiled, computed⟩ :=
    definitionRow?_eq source (within row member)
  have entryMember : (source.syntaxSignature.names.idxOf row.head, declaration) ∈
      (passes.filterMap (definitionRow? source)).map fun entry => (entry.1, entry.2.1) :=
    List.mem_map.mpr ⟨_, List.mem_filterMap.mpr ⟨row, member, computed⟩, rfl⟩
  have keys : (((passes.filterMap (definitionRow? source)).map
      fun entry => (entry.1, entry.2.1)).map Prod.fst).Nodup := by
    simpa [List.map_map, Function.comp_def] using definition_keys_nodup source passes within distinct
  rw [compiled.term]
  apply lookup_append_left
  rw [List.lookup_reverse_of_nodup_keys _ keys]
  exact lookup_of_mem keys entryMember

/-- Primitive positions hold their declarations, whatever has been admitted
since. -/
theorem termsAfter_primitive (source : Presentation) {passes : List Row}
    (within : ∀ row ∈ passes, row ∈ source.rows) {index : Nat} {rule : GrammarRule}
    (position : source.syntaxSignature.language.terms[index]? = some rule)
    (primitive : Primitive source.rows rule.label) :
    (termsAfter source passes).lookup index = source.syntaxSignature.termSignature index := by
  have nameLookup : source.syntaxSignature.names[index]? = some rule.label := by
    rw [names_getElem?, position]
    rfl
  have absent : (((passes.filterMap (definitionRow? source)).map
      fun entry => (entry.1, entry.2.1)).reverse).lookup index = none := by
    apply lookup_eq_none
    intro entry entryMember sameKey
    obtain ⟨full, fullMember, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp entryMember)
    obtain ⟨row, rowMember, -, -, located, -⟩ :=
      mem_filterMap_definitionRow? source within fullMember
    have headLookup :=
      getElem?_index? (index?_some _ _ (head_mem_names source (within row rowMember)))
    have sameIndex : source.syntaxSignature.names.idxOf row.head = index := by
      rw [← located]
      exact sameKey
    rw [sameIndex, nameLookup] at headLookup
    exact primitive row (within row rowMember) (Option.some.inj headLookup)
  unfold termsAfter
  rw [lookup_append_right _ _ absent, primitiveTerms_lookup, position]
  simp [(checkPrimitive_iff _ _).mpr primitive, Signature.termSignature, position]

theorem termsAfter_outside (source : Presentation) {passes : List Row}
    (within : ∀ row ∈ passes, row ∈ source.rows) {index : Nat}
    (position : source.syntaxSignature.language.terms[index]? = none) :
    (termsAfter source passes).lookup index = none := by
  have absent : (((passes.filterMap (definitionRow? source)).map
      fun entry => (entry.1, entry.2.1)).reverse).lookup index = none := by
    apply lookup_eq_none
    intro entry entryMember sameKey
    obtain ⟨full, fullMember, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp entryMember)
    obtain ⟨row, rowMember, -, -, located, -⟩ :=
      mem_filterMap_definitionRow? source within fullMember
    have headLookup :=
      getElem?_index? (index?_some _ _ (head_mem_names source (within row rowMember)))
    have sameIndex : source.syntaxSignature.names.idxOf row.head = index := by
      rw [← located]
      exact sameKey
    rw [sameIndex, names_getElem?, position] at headLookup
    cases headLookup
  unfold termsAfter
  rw [lookup_append_right _ _ absent, primitiveTerms_lookup, position]
  rfl

/-- Every entry of the table is a declaration of the generated signature. -/
theorem termsAfter_sound (source : Presentation) {passes : List Row}
    (within : ∀ row ∈ passes, row ∈ source.rows) {index : Nat} {declaration : TermDecl}
    (found : (termsAfter source passes).lookup index = some declaration) :
    source.syntaxSignature.termSignature index = some declaration := by
  have entryMember := mem_of_lookup found
  rcases List.mem_append.mp entryMember with defined | primitive
  · obtain ⟨full, fullMember, same⟩ := List.mem_map.mp (List.mem_reverse.mp defined)
    obtain ⟨row, rowMember, expression, compiled, -, -⟩ :=
      mem_filterMap_definitionRow? source within fullMember
    cases same
    exact compiled.term
  · have lookup := lookup_of_mem (primitiveTerms_keys source) (List.mem_reverse.mp primitive)
    rw [primitiveTerms_lookup_forward] at lookup
    cases position : source.syntaxSignature.language.terms[index]? with
    | none => simp [position] at lookup
    | some rule =>
      by_cases primitiveRule : checkPrimitive source.rows rule.label = true
      · simpa [Signature.termSignature, position, primitiveRule] using lookup
      · simp [position, primitiveRule] at lookup

theorem chronological_sorts (source : Presentation) :
    (chronological source).sortSignature = source.theory.sortSignature := by
  funext index
  exact List.lookup_reverse_of_nodup_keys _ (List.compileIndexed_keys_nodup _ _) index

/-- After all the definitions, the term table is the generated signature. -/
theorem chronological_terms (source : Presentation) :
    (chronological source).termSignature = source.theory.termSignature := by
  rw [source.theory_termSignature]
  funext index
  change (termsAfter source source.rows).lookup index = _
  have within : ∀ row ∈ source.rows, row ∈ source.rows := fun _ member => member
  cases position : source.syntaxSignature.language.terms[index]? with
  | none =>
    rw [termsAfter_outside source within position]
    simp [Signature.termSignature, position]
  | some rule =>
    by_cases primitive : checkPrimitive source.rows rule.label = true
    · exact termsAfter_primitive source within position ((checkPrimitive_iff _ _).mp primitive)
    · have defined : ∃ row ∈ source.rows, rule.label = row.head := by
        by_contra none
        exact primitive ((checkPrimitive_iff _ _).mpr
          (fun row member same => none ⟨row, member, same⟩))
      obtain ⟨row, member, label⟩ := defined
      have nameLookup : source.syntaxSignature.names[index]? = some row.head := by
        rw [names_getElem?, position, ← label]
        rfl
      have located : source.syntaxSignature.names.idxOf row.head = index := by
        have found := index?_getElem? source.syntaxSignature.distinctConstructors nameLookup
        have expected := index?_some source.syntaxSignature.names row.head
          (head_mem_names source member)
        exact Option.some.inj (expected.symm.trans found)
      rw [← located]
      exact termsAfter_defined source within source.definitionalRows.acyclic.distinctHeads member

theorem chronological_definitions (source : Presentation) :
    (chronological source).definitionSignature = source.theory.definitionSignature := by
  rw [source.theory_definitionSignature]
  funext index
  change (((definitionRows source).map fun row => (row.1, row.2.2)).reverse).lookup index = _
  have within : ∀ row ∈ source.rows, row ∈ source.rows := fun _ member => member
  have keys : (((definitionRows source).map fun entry => (entry.1, entry.2.2)).map
      Prod.fst).Nodup := by
    simpa [List.map_map, Function.comp_def, definitionRows] using
      definition_keys_nodup source source.rows within
        source.definitionalRows.acyclic.distinctHeads
  rw [List.lookup_reverse_of_nodup_keys _ keys]
  cases expected : definitionSignature source.syntaxSignature source.rows index with
  | some body =>
    obtain ⟨row, member, declaration, expression, compiled, rfl⟩ :=
      compiled_of_lookup source.definitionalRows expected
    obtain ⟨otherDeclaration, otherExpression, otherCompiled, computed⟩ :=
      definitionRow?_eq source member
    have located : source.syntaxSignature.names.idxOf row.head = index := by
      have expectedName := index?_some source.syntaxSignature.names row.head
        (head_mem_names source member)
      exact Option.some.inj (expectedName.symm.trans compiled.name)
    subst located
    have sameBody : (⟨[], otherExpression⟩ : Definition.Body) = ⟨[], expression⟩ :=
      Option.some.inj (otherCompiled.body.symm.trans compiled.body)
    apply lookup_of_mem keys
    exact List.mem_map.mpr ⟨_, List.mem_filterMap.mpr ⟨row, member, computed⟩,
      by rw [sameBody]⟩
  | none =>
    apply lookup_eq_none
    intro entry entryMember sameKey
    obtain ⟨full, fullMember, rfl⟩ := List.mem_map.mp entryMember
    obtain ⟨row, rowMember, expression, compiled, -, -⟩ :=
      mem_filterMap_definitionRow? source within fullMember
    have body := compiled.body
    rw [sameKey, expected] at body
    cases body

theorem chronological_theorems (source : Presentation) :
    (chronological source).theoremSignature = source.theory.theoremSignature := by
  funext index
  exact List.lookup_reverse_of_nodup_keys _ (List.compileIndexed_keys_nodup _ _) index

/-! ## Formation of the payloads -/

private theorem parameter_context_formed (source : Presentation) {parameters : List TermParam}
    {context : Context} (compiled : parameters? source.syntaxSignature.sorts parameters = some context) :
    ∀ initial, Context.Extension source.theory.sortSignature initial context := by
  induction parameters generalizing context with
  | nil =>
      simp only [parameters?, Option.some.injEq] at compiled
      subst context
      exact Context.Extension.nil
  | cons parameter parameters ih =>
      cases parameter with
      | simple name type =>
          cases typeFound : type? source.syntaxSignature.sorts type with
          | none => simp [parameters?, typeFound] at compiled
          | some sort =>
              cases restFound : parameters? source.syntaxSignature.sorts parameters with
              | none => simp [parameters?, typeFound, restFound] at compiled
              | some remaining =>
                  have same : Binder.regular sort ∅ :: remaining = context := by
                    simpa [parameters?, typeFound, restFound] using compiled
                  subst context
                  cases type with
                  | base label =>
                      have known : source.theory.sortSignature sort = some (source.sortInfo label) := by
                        rw [source.theory_sortSignature, getElem?_index? typeFound]
                        rfl
                      intro initial
                      exact .cons (.regular known (by simp)) (ih restFound _)
                  | _ => simp [type?] at typeFound
      | _ => simp [parameters?] at compiled

/-- Compiling a constructor derives its real MM0 formation premises. -/
theorem constructor_formed (source : Presentation) {rule : GrammarRule} {declaration : TermDecl}
    (compiled : declaration? source.syntaxSignature.sorts rule = some declaration) :
    TermDecl.Admissible source.theory.sortSignature declaration := by
  obtain ⟨parameters, result, dependencies⟩ := declaration?_fields compiled
  refine ⟨parameter_context_formed source parameters [], ?_, ?_⟩
  · refine ⟨source.sortInfo rule.category, ?_, rfl⟩
    rw [source.theory_sortSignature, getElem?_index? result]
    rfl
  · simp [dependencies]

/-- Every declaration of the generated signature has regular formals with
no dependencies. -/
theorem signature_dependencyFree (source : Presentation) {index : Nat} {declaration : TermDecl}
    (lookup : source.syntaxSignature.termSignature index = some declaration) :
    declaration.DependencyFree ∧ TermDecl.Admissible source.theory.sortSignature declaration := by
  obtain ⟨rule, -, compiled⟩ := source.syntaxSignature.lookup_source lookup
  obtain ⟨parameters, -, dependencies⟩ := declaration?_fields compiled
  exact ⟨⟨parameters?_ordinary parameters, dependencies⟩, constructor_formed source compiled⟩

theorem primitive_terms_formed (source : Presentation) :
    ∀ row ∈ primitiveTerms source, TermDecl.Admissible source.theory.sortSignature row.2 := by
  intro row member
  obtain ⟨rule, -, compiled⟩ := List.mem_compileIndexed_value _ _ 0 member
  by_cases primitive : checkPrimitive source.rows rule.label = true
  · exact constructor_formed source (by simpa [primitive] using compiled)
  · simp [primitive] at compiled

theorem generated_axioms_formed (source : Presentation) :
    ∀ row ∈ source.theory.theorems,
      TheoremDecl.Admissible source.theory.sortSignature source.theory.termSignature row.2 := by
  intro row member
  obtain ⟨rule, belongs, compiled⟩ :=
    List.mem_compileIndexed_value (rule? source.syntaxSignature) source.rules 0 member
  rw [source.theory_termSignature]
  exact Presentation.compiled_admitted ((rule?_eq_some_iff _ _ _).mp compiled) (source.formedRules rule belongs)

/-- **Each definition is admitted over the terms that precede it.** The
body is typed in the finished signature. It mentions only primitive
constructors and earlier definitions, so it is typed over the table at its
turn, with no free bound variable. -/
theorem bodiesAdmissible (source : Presentation) :
    ∀ (later earlier : List Row), source.rows = earlier ++ later →
      Theory.BodiesAdmissible source.theory.sortSignature (termsAfter source earlier)
        (later.filterMap (definitionRow? source))
  | [], _, _ => trivial
  | row :: later, earlier, split => by
      have acyclic := source.definitionalRows.acyclic
      have member : row ∈ source.rows := by
        rw [split]
        simp
      have earlierWithin : ∀ other ∈ earlier, other ∈ source.rows := by
        intro other otherMember
        rw [split]
        exact List.mem_append_left _ otherMember
      have earlierDistinct : earlier.Pairwise (fun first second => first.head ≠ second.head) := by
        have all := acyclic.distinctHeads
        rw [split] at all
        exact (List.pairwise_append.mp all).1
      obtain ⟨declaration, expression, compiled, computed⟩ := definitionRow?_eq source member
      rw [List.filterMap_cons_some computed]
      have formed := acyclic.wellFormed row member
      -- The body avoids its own head and every later head.
      have bodyAvoids : ∀ other ∈ row :: later, Avoids other.head row.body := by
        intro other otherMember
        rcases List.mem_cons.mp otherMember with same | inLater
        · rw [same]
          exact acyclic.ownHead row member
        · have ordered := acyclic.laterHeads
          rw [split] at ordered
          exact (List.pairwise_cons.mp (List.pairwise_append.mp ordered).2.1).1 other inLater
      let allowed : String → Prop :=
        fun name => Primitive source.rows name ∨ ∃ other ∈ earlier, other.head = name
      have bodyWithin : ConstructorsWithin allowed (numbered row.formals row.body) := by
        apply constructorsWithin_numbered
        refine (constructorsWithin_primitive bodyAvoids).mono ?_
        intro name unusedLater
        by_cases isEarlier : ∃ other ∈ earlier, other.head = name
        · exact Or.inr isEarlier
        · refine Or.inl ?_
          intro other otherMember same
          rw [split] at otherMember
          rcases List.mem_append.mp otherMember with inEarlier | inLater
          · exact isEarlier ⟨other, inEarlier, same.symm⟩
          · exact unusedLater other inLater same
      have symbols := encodes_symbolsWithin compiled.encoded bodyWithin
      have agrees : ∀ index,
          (∃ name, index? source.syntaxSignature.names name = some index ∧ allowed name) →
          (termsAfter source earlier).lookup index =
            source.syntaxSignature.termSignature index := by
        rintro index ⟨name, found, primitive | ⟨other, otherMember, rfl⟩⟩
        · have nameLookup := getElem?_index? found
          rw [names_getElem?] at nameLookup
          cases position : source.syntaxSignature.language.terms[index]? with
          | none => simp [position] at nameLookup
          | some rule =>
            have label : rule.label = name := by simpa [position] using nameLookup
            exact termsAfter_primitive source earlierWithin position (label ▸ primitive)
        · have located : source.syntaxSignature.names.idxOf other.head = index := by
            have expectedName := index?_some source.syntaxSignature.names other.head
              (head_mem_names source (earlierWithin other otherMember))
            exact Option.some.inj (expectedName.symm.trans found)
          rw [← located]
          exact termsAfter_defined source earlierWithin earlierDistinct otherMember
      have typedAtTurn : Preterm.HasType (fun index => (termsAfter source earlier).lookup index)
          declaration.arguments expression [] declaration.resultSort :=
        compiled.typed.restrictSignature agrees symbols
      have regularDeclaration := (signature_dependencyFree source compiled.term).1
      have freeAtTurn := typedAtTurn.freeVars_empty regularDeclaration.arguments
        (fun symbol other lookup =>
          (signature_dependencyFree source (termsAfter_sound source earlierWithin lookup)).1)
      have admissible : Definition.AdmissibleBody source.theory.sortSignature
          (fun index => (termsAfter source earlier).lookup index) declaration
          ⟨[], expression⟩ :=
        { dummies := by
            intro sort impossible
            simp at impossible
          typed := by simpa [Definition.Body.context] using typedAtTurn
          free := ⟨∅, by simpa [Definition.Body.context] using freeAtTurn, by simp⟩ }
      refine ⟨admissible, ?_⟩
      · have next := bodiesAdmissible source later (earlier ++ [row])
          (by rw [split, List.append_assoc]; rfl)
        have extended : termsAfter source (earlier ++ [row]) =
            (source.syntaxSignature.names.idxOf row.head, declaration) ::
              termsAfter source earlier := by
          simp [termsAfter, List.filterMap_append, computed]
        rw [extended] at next
        exact next

/-- The whole compiler output earns sequential admission from the empty theory. -/
theorem admitted (source : Presentation) :
    Theory.Runs {} (admissions source) (chronological source) := by
  let sortsOnly : Theory := { sorts := source.theory.sorts.reverse }
  let constructors : Theory :=
    { sorts := source.theory.sorts.reverse, terms := (primitiveTerms source).reverse }
  let defined : Theory :=
    { sorts := source.theory.sorts.reverse
      terms := termsAfter source source.rows
      definitions := ((definitionRows source).map fun row => (row.1, row.2.2)).reverse }
  have within : ∀ row ∈ source.rows, row ∈ source.rows := fun _ member => member
  have sortsAgree : sortsOnly.sortSignature = source.theory.sortSignature :=
    chronological_sorts source
  have constructorSorts : constructors.sortSignature = source.theory.sortSignature :=
    chronological_sorts source
  have sorts : Theory.Runs {} (source.theory.sorts.map fun row => Admission.sort row.1 row.2) sortsOnly := by
    simpa [sortsOnly] using Theory.runs_sort_rows {} source.theory.sorts
      (List.compileIndexed_keys_nodup _ _) (fun _ _ => rfl)
  have terms : Theory.Runs sortsOnly
      ((primitiveTerms source).map fun row => Admission.term row.1 row.2) constructors := by
    have formed : ∀ row ∈ primitiveTerms source,
        TermDecl.Admissible sortsOnly.sortSignature row.2 := by
      rw [sortsAgree]
      exact primitive_terms_formed source
    simpa [constructors, sortsOnly] using Theory.runs_term_rows sortsOnly (primitiveTerms source)
      (List.compileIndexed_keys_nodup _ _) (fun _ _ => rfl) formed
  have definitions : Theory.Runs constructors
      ((definitionRows source).map fun row => Admission.definition row.1 row.2.1 row.2.2)
      defined := by
    have entries : ∀ entry ∈ definitionRows source, ∃ row ∈ source.rows, ∃ expression,
        Compiled source.syntaxSignature source.rows row entry.1 entry.2.1 expression ∧
          entry.1 = source.syntaxSignature.names.idxOf row.head ∧
          entry.2.2 = ⟨[], expression⟩ :=
      fun entry member => mem_filterMap_definitionRow? source within member
    have freshTerms : ∀ entry ∈ definitionRows source,
        constructors.termSignature entry.1 = none := by
      intro entry member
      obtain ⟨row, rowMember, -, -, located, -⟩ := entries entry member
      rw [located]
      exact primitiveTerms_lookup_defined source rowMember
    have formed : ∀ entry ∈ definitionRows source,
        TermDecl.Admissible constructors.sortSignature entry.2.1 := by
      intro entry member
      obtain ⟨row, rowMember, expression, compiled, -, -⟩ := entries entry member
      have result := (signature_dependencyFree source compiled.term).2
      rw [← constructorSorts] at result
      exact result
    have bodies : Theory.BodiesAdmissible constructors.sortSignature constructors.terms
        (definitionRows source) := by
      have all := bodiesAdmissible source source.rows [] rfl
      rw [← constructorSorts] at all
      simpa [termsAfter, constructors, definitionRows] using all
    simpa [constructors, defined, termsAfter, definitionRows] using
      Theory.runs_definition_rows constructors (definitionRows source)
        (definition_keys_nodup source source.rows within
          source.definitionalRows.acyclic.distinctHeads)
        freshTerms (fun _ _ => rfl) formed bodies
  have axioms : Theory.Runs defined
      (source.theory.theorems.map fun row => Admission.axiomDecl row.1 row.2) (chronological source) := by
    have formed : ∀ row ∈ source.theory.theorems,
        TheoremDecl.Admissible defined.sortSignature defined.termSignature row.2 := by
      change ∀ row ∈ source.theory.theorems, TheoremDecl.Admissible
        (chronological source).sortSignature (chronological source).termSignature row.2
      rw [chronological_sorts, chronological_terms]
      exact generated_axioms_formed source
    simpa [defined, chronological] using Theory.runs_axiom_rows defined source.theory.theorems
      (List.compileIndexed_keys_nodup _ _) (fun _ _ => rfl) formed
  simpa only [admissions, List.append_assoc] using
    sorts.append (terms.append (definitions.append axioms))

def specification (source : Presentation) : List SpecificationEntry :=
  (admissions source).map SpecificationAdmission.entryOfAdmission

def declarations (source : Presentation) : List ProofDeclaration :=
  (admissions source).map (fun admission => ⟨admission, false⟩)

theorem specification_consumed (source : Presentation) :
    SpecificationAdmission.Runs ⟨{}, specification source⟩ (declarations source)
      ⟨chronological source, []⟩ := by
  simpa [specification, declarations] using SpecificationAdmission.of_theory_run (admitted source) []

theorem verified (source : Presentation) :
    SpecificationAdmission.verify? (specification source) (declarations source) =
      some (chronological source) :=
  (SpecificationAdmission.verify_eq_some_iff _ _ _).mpr (specification_consumed source)

end Mettapedia.Languages.MM0.Translation.FirstOrderAdmission
