import Mettapedia.OSLF.MeTTaIL.GeneralEquationMeasures
import Mettapedia.GSLT.LanguageDef.WellSortedChecker
import Mettapedia.OSLF.MeTTaIL.ScopedPattern

/-!
# Finite canonical universes for arbitrary finite supported terms

The alphabet is extracted from actual source, authored schemas and provider
snapshot terms. The enumerator has no language-specific state decoder. Its
parameters bound tree size and variable spelling; binder display metadata is
erased, while multi-binder arities and every de Bruijn index remain explicit.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.GeneralFiniteTermUniverse

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternTreeSize
open Mettapedia.GSLT.LanguageDef.WellSorted

structure Alphabet where
  constructors : List String
  freeNames : List String
  arities : List Nat
  deriving Repr, DecidableEq

def constructors : Pattern → List String
  | .bvar _ | .fvar _ => []
  | .apply label arguments => label :: arguments.flatMap constructors
  | .lambda _ body | .multiLambda _ _ body => constructors body
  | .subst body replacement => constructors body ++ constructors replacement
  | .collection _ elements _ => elements.flatMap constructors
decreasing_by all_goals sizeOf_pattern_dec

def arities : Pattern → List Nat
  | .bvar _ | .fvar _ => []
  | .apply _ arguments => arguments.flatMap arities
  | .lambda _ body => arities body
  | .multiLambda arity _ body => arity :: arities body
  | .subst body replacement => arities body ++ arities replacement
  | .collection _ elements _ => elements.flatMap arities
decreasing_by all_goals sizeOf_pattern_dec

def fromPatterns (patterns : List Pattern) : Alphabet where
  constructors := (patterns.flatMap constructors).eraseDups
  freeNames := (patterns.flatMap Pattern.freeFvarNames).eraseDups
  arities := (patterns.flatMap arities).eraseDups

def languagePatterns (language : LanguageDef) : List Pattern :=
  language.equations.flatMap (fun equation => [equation.left, equation.right]) ++
    language.rewrites.flatMap (fun rule => [rule.left, rule.right])

def alphabet (language : LanguageDef) (source : Pattern) (providerTerms : List Pattern) : Alphabet :=
  fromPatterns (source :: (languagePatterns language ++ providerTerms))

def Supported (alphabet : Alphabet) (pattern : Pattern) : Prop :=
  (∀ label ∈ constructors pattern, label ∈ alphabet.constructors) ∧
    (∀ name ∈ pattern.freeFvarNames, name ∈ alphabet.freeNames) ∧
    (∀ arity ∈ arities pattern, arity ∈ alphabet.arities)

theorem supported_fromPatterns (patterns : List Pattern) (pattern : Pattern)
    (member : pattern ∈ patterns) : Supported (fromPatterns patterns) pattern := by
  constructor
  · intro label occurs
    exact List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨pattern, member, occurs⟩)
  constructor
  · intro name occurs
    exact List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨pattern, member, occurs⟩)
  · intro arity occurs
    exact List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨pattern, member, occurs⟩)

theorem source_supported (language : LanguageDef) (source : Pattern) (providerTerms : List Pattern) :
    Supported (alphabet language source providerTerms) source :=
  supported_fromPatterns _ source (by simp)

def IndicesBelow (bound : Nat) : Pattern → Prop
  | .bvar index => index < bound
  | .fvar _ => True
  | .apply _ arguments => ∀ argument ∈ arguments, IndicesBelow bound argument
  | .lambda _ body | .multiLambda _ _ body => IndicesBelow bound body
  | .subst body replacement => IndicesBelow bound body ∧ IndicesBelow bound replacement
  | .collection _ elements _ => ∀ element ∈ elements, IndicesBelow bound element
decreasing_by all_goals sizeOf_pattern_dec

def rows (pool : List Pattern) : Nat → List (List Pattern)
  | 0 => [[]]
  | budget + 1 => [] :: pool.flatMap (fun first => (rows pool budget).map (first :: ·))

theorem rows_complete (pool : List Pattern) (budget : Nat) (patterns : List Pattern)
    (short : patterns.length ≤ budget) (covered : ∀ pattern ∈ patterns, pattern ∈ pool) :
    patterns ∈ rows pool budget := by
  induction budget generalizing patterns with
  | zero =>
    have empty : patterns = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [empty, rows]
  | succ budget ih =>
    cases patterns with
    | nil => simp [rows]
    | cons first rest =>
      have tail : rest ∈ rows pool budget := ih rest (by simpa using short)
        (by intro pattern member; exact covered pattern (by simp [member]))
      simp only [rows, List.mem_cons, List.mem_flatMap, List.mem_map]
      exact Or.inr ⟨first, covered first (by simp), rest, tail, rfl⟩

theorem length_le_listNodes (patterns : List Pattern) : patterns.length ≤ listNodes patterns := by
  induction patterns with
  | nil => rfl
  | cons first rest ih =>
    have positive := nodes_positive first
    simp only [List.length_cons, listNodes]
    omega

/-- A finite structural enumeration. Rows retain their order and duplicates;
no collection or occurrence quotient is introduced by this algorithm. -/
def terms (alphabet : Alphabet) (indexBound : Nat) : Nat → List Pattern
  | 0 => []
  | budget + 1 =>
      (List.range indexBound).map Pattern.bvar ++
      alphabet.freeNames.map Pattern.fvar ++
      alphabet.constructors.flatMap (fun label =>
        (rows (terms alphabet indexBound budget) budget).map (Pattern.apply label)) ++
      (terms alphabet indexBound budget).map (Pattern.lambda none) ++
      alphabet.arities.flatMap (fun arity =>
        (terms alphabet indexBound budget).map (Pattern.multiLambda arity [])) ++
      [CollType.vec, .hashBag, .hashSet].flatMap (fun kind =>
        (rows (terms alphabet indexBound budget) budget).map (fun elements =>
          Pattern.collection kind elements none))

theorem terms_bvar (alphabet : Alphabet) (indexBound budget index : Nat) (below : index < indexBound) :
    Pattern.bvar index ∈ terms alphabet indexBound (budget + 1) := by simp [terms, below]

theorem terms_fvar (alphabet : Alphabet) (indexBound budget : Nat) (name : String)
    (declared : name ∈ alphabet.freeNames) : Pattern.fvar name ∈ terms alphabet indexBound (budget + 1) := by
  simp [terms, declared]

theorem terms_apply (alphabet : Alphabet) (indexBound budget : Nat) (label : String)
    (arguments : List Pattern) (declared : label ∈ alphabet.constructors)
    (row : arguments ∈ rows (terms alphabet indexBound budget) budget) :
    Pattern.apply label arguments ∈ terms alphabet indexBound (budget + 1) := by
  simp only [terms, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨label, declared, arguments, row, rfl⟩)))

theorem terms_lambda (alphabet : Alphabet) (indexBound budget : Nat) (body : Pattern)
    (member : body ∈ terms alphabet indexBound budget) :
    Pattern.lambda none body ∈ terms alphabet indexBound (budget + 1) := by
  simp only [terms, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inl (Or.inl (Or.inr ⟨body, member, rfl⟩))

theorem terms_multiLambda (alphabet : Alphabet) (indexBound budget arity : Nat) (body : Pattern)
    (declared : arity ∈ alphabet.arities) (member : body ∈ terms alphabet indexBound budget) :
    Pattern.multiLambda arity [] body ∈ terms alphabet indexBound (budget + 1) := by
  simp only [terms, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inl (Or.inr ⟨arity, declared, body, member, rfl⟩)

theorem terms_collection (alphabet : Alphabet) (indexBound budget : Nat) (kind : CollType)
    (elements : List Pattern) (row : elements ∈ rows (terms alphabet indexBound budget) budget) :
    Pattern.collection kind elements none ∈ terms alphabet indexBound (budget + 1) := by
  simp only [terms, List.mem_append, List.mem_flatMap, List.mem_map]
  refine Or.inr ⟨kind, ?_, elements, row, rfl⟩
  cases kind <;> simp

theorem objectList_spec (patterns : List Pattern) :
    isObjectPatternList patterns = true ↔ ∀ pattern ∈ patterns, isObjectPattern pattern = true := by
  induction patterns with
  | nil => simp [isObjectPatternList]
  | cons first rest ih => simp [isObjectPatternList, ih]

theorem terms_complete (alphabet : Alphabet) (indexBound : Nat) (pattern : Pattern)
    (budget : Nat) (small : nodes pattern ≤ budget) (support : Supported alphabet pattern)
    (indices : IndicesBelow indexBound pattern)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : isObjectPattern pattern = true) : pattern ∈ terms alphabet indexBound budget := by
  induction pattern using Pattern.inductionOn generalizing budget with
  | hbvar index =>
    cases budget with
    | zero => simp only [nodes] at small; omega
    | succ budget => exact terms_bvar alphabet indexBound budget index (by simpa only [IndicesBelow] using indices)
  | hfvar name =>
    cases budget with
    | zero => simp only [nodes] at small; omega
    | succ budget => exact terms_fvar alphabet indexBound budget name (support.2.1 name (by simp [Pattern.freeFvarNames]))
  | happly label arguments ih =>
    cases budget with
    | zero => have positive := nodes_positive (Pattern.apply label arguments); omega
    | succ budget =>
      have listBound : listNodes arguments ≤ budget := by simp only [nodes] at small; omega
      have row := rows_complete (terms alphabet indexBound budget) budget arguments
        ((length_le_listNodes arguments).trans listBound) (by
          intro argument member
          have supported : Supported alphabet argument := by
            refine ⟨?_, ?_, ?_⟩
            · intro constructor occurs
              exact support.1 constructor (by simp only [constructors, List.mem_cons, List.mem_flatMap]; exact Or.inr ⟨argument, member, occurs⟩)
            · intro name occurs
              exact support.2.1 name (by simp only [Pattern.freeFvarNames, List.mem_flatMap]; exact ⟨argument, member, occurs⟩)
            · intro arity occurs
              exact support.2.2 arity (by simp only [arities, List.mem_flatMap]; exact ⟨argument, member, occurs⟩)
          have canon := Pattern.hasCanonicalBinderMetadataList_eq_true_iff arguments |>.mp canonical
          have objects := (objectList_spec arguments).mp object
          exact ih argument member budget ((member_nodes_le member).trans listBound) supported
            ((by simpa only [IndicesBelow] using indices : ∀ p ∈ arguments, IndicesBelow indexBound p) argument member) (canon argument member) (objects argument member))
      exact terms_apply alphabet indexBound budget label arguments (support.1 label (by simp [constructors])) row
  | hlambda name body ih =>
    cases budget with
    | zero => have positive := nodes_positive (Pattern.lambda name body); omega
    | succ budget =>
      simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
      have unnamed : name = none := by simpa using canonical.1
      subst name
      exact terms_lambda alphabet indexBound budget body
        (ih budget (by simp only [nodes] at small; omega)
          (by simpa only [Supported, constructors, arities, Pattern.freeFvarNames] using support)
          (by simpa only [IndicesBelow] using indices) canonical.2 (by simpa only [isObjectPattern] using object))
  | hmultiLambda arity names body ih =>
    cases budget with
    | zero => have positive := nodes_positive (Pattern.multiLambda arity names body); omega
    | succ budget =>
      simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
      have unnamed : names = [] := by simpa using canonical.1
      subst names
      have supported : Supported alphabet body := by
        refine ⟨by simpa only [constructors] using support.1, by simpa only [Pattern.freeFvarNames] using support.2.1, ?_⟩
        intro size occurs
        exact support.2.2 size (by simp [arities, occurs])
      exact terms_multiLambda alphabet indexBound budget arity body
        (support.2.2 arity (by simp [arities]))
        (ih budget (by simp only [nodes] at small; omega) supported (by simpa only [IndicesBelow] using indices) canonical.2
          (by simpa only [isObjectPattern] using object))
  | hsubst body replacement bodyIH replacementIH => simp only [isObjectPattern, Bool.false_eq_true] at object
  | hcollection kind elements rest ih =>
    simp only [isObjectPattern, Bool.and_eq_true] at object
    have closed : rest = none := by simpa using object.1
    subst rest
    cases budget with
    | zero => have positive := nodes_positive (Pattern.collection kind elements none); omega
    | succ budget =>
      have listBound : listNodes elements ≤ budget := by simp only [nodes] at small; omega
      have row := rows_complete (terms alphabet indexBound budget) budget elements
        ((length_le_listNodes elements).trans listBound) (by
          intro element member
          have supported : Supported alphabet element := by
            refine ⟨?_, ?_, ?_⟩
            · intro constructor occurs
              exact support.1 constructor (by simp only [constructors, List.mem_flatMap]; exact ⟨element, member, occurs⟩)
            · intro name occurs
              exact support.2.1 name (by simp only [Pattern.freeFvarNames, Option.toList_none, List.append_nil, List.mem_flatMap]; exact ⟨element, member, occurs⟩)
            · intro arity occurs
              exact support.2.2 arity (by simp only [arities, List.mem_flatMap]; exact ⟨element, member, occurs⟩)
          have canon := Pattern.hasCanonicalBinderMetadataList_eq_true_iff elements |>.mp canonical
          have objects := (objectList_spec elements).mp object.2
          exact ih element member budget ((member_nodes_le member).trans listBound) supported
            ((by simpa only [IndicesBelow] using indices : ∀ p ∈ elements, IndicesBelow indexBound p) element member) (canon element member) (objects element member))
      exact terms_collection alphabet indexBound budget kind elements row

def maximumArity (alphabet : Alphabet) : Nat := alphabet.arities.foldr max 0

theorem arity_le_maximum (alphabet : Alphabet) (arity : Nat)
    (member : arity ∈ alphabet.arities) : arity ≤ maximumArity alphabet := by
  unfold maximumArity
  generalize alphabet.arities = values at member ⊢
  induction values with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst arity
      exact Nat.le_max_left _ _
    · exact (ih later).trans (Nat.le_max_right _ _)

theorem indicesBelow_mono (small large : Nat) (pattern : Pattern)
    (bounded : IndicesBelow small pattern) (order : small ≤ large) : IndicesBelow large pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp only [IndicesBelow] at *; omega
  | hfvar name => simp only [IndicesBelow]
  | happly label arguments ih =>
    simp only [IndicesBelow] at *
    intro argument member
    exact ih argument member (bounded argument member)
  | hlambda name body ih => simpa only [IndicesBelow] using ih (by simpa only [IndicesBelow] using bounded)
  | hmultiLambda arity names body ih => simpa only [IndicesBelow] using ih (by simpa only [IndicesBelow] using bounded)
  | hsubst body replacement bodyIH replacementIH =>
    simp only [IndicesBelow] at *
    exact ⟨bodyIH bounded.1, replacementIH bounded.2⟩
  | hcollection kind elements rest ih =>
    simp only [IndicesBelow] at *
    intro element member
    exact ih element member (bounded element member)

/-- Every locally scoped term has a derived global index bound. Large
multi-binder arities are covered by their finite alphabet, not silently
assumed to contribute to the tree-node measure. -/
theorem scoped_indices (alphabet : Alphabet) (pattern : Pattern) (depth budget : Nat)
    (small : nodes pattern ≤ budget)
    (scope : pattern.isWellScopedAt depth = true)
    (aritiesBound : ∀ arity ∈ arities pattern, arity ≤ maximumArity alphabet) :
    IndicesBelow (depth + budget * (maximumArity alphabet + 1)) pattern := by
  induction pattern using Pattern.inductionOn generalizing depth budget with
  | hbvar index =>
    simp only [Pattern.isWellScopedAt, decide_eq_true_eq] at scope
    simp only [IndicesBelow]
    omega
  | hfvar name => simp only [IndicesBelow]
  | happly label arguments ih =>
    simp only [IndicesBelow]
    intro argument member
    have scopedTerm := (Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff
      depth arguments).mp scope argument member
    have supported : ∀ arity ∈ arities argument, arity ≤ maximumArity alphabet := by
      intro arity occurs
      exact aritiesBound arity (by simp only [arities, List.mem_flatMap]; exact ⟨argument, member, occurs⟩)
    exact ih argument member depth budget ((member_nodes_le member).trans (by simp only [nodes] at small; omega))
      scopedTerm supported
  | hlambda name body ih =>
    have bodyBound : nodes body + 1 ≤ budget := by simp only [nodes] at small; omega
    have shifted := Nat.mul_le_mul_right (maximumArity alphabet + 1) bodyBound
    rw [Nat.add_mul, Nat.one_mul] at shifted
    have bounded := ih (depth + 1) (nodes body) (Nat.le_refl _) scope
      (by simpa only [arities] using aritiesBound)
    simpa only [IndicesBelow] using indicesBelow_mono
      (depth + 1 + nodes body * (maximumArity alphabet + 1))
      (depth + budget * (maximumArity alphabet + 1)) body bounded (by omega)
  | hmultiLambda arity names body ih =>
    have bodyBound : nodes body + 1 ≤ budget := by simp only [nodes] at small; omega
    have shifted := Nat.mul_le_mul_right (maximumArity alphabet + 1) bodyBound
    rw [Nat.add_mul, Nat.one_mul] at shifted
    have declared := aritiesBound arity (by simp [arities])
    have bodyArities : ∀ size ∈ arities body, size ≤ maximumArity alphabet := by
      intro size member
      exact aritiesBound size (by simp [arities, member])
    have bounded := ih (depth + arity) (nodes body) (Nat.le_refl _) scope bodyArities
    simpa only [IndicesBelow] using indicesBelow_mono
      (depth + arity + nodes body * (maximumArity alphabet + 1))
      (depth + budget * (maximumArity alphabet + 1)) body bounded (by omega)
  | hsubst body replacement bodyIH replacementIH =>
    simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at scope
    have bodyBound : nodes body + 1 ≤ budget := by simp only [nodes] at small; omega
    have replacementBound : nodes replacement ≤ budget := by simp only [nodes] at small; omega
    have shifted := Nat.mul_le_mul_right (maximumArity alphabet + 1) bodyBound
    rw [Nat.add_mul, Nat.one_mul] at shifted
    have bodyArities : ∀ size ∈ arities body, size ≤ maximumArity alphabet := by
      intro size member
      exact aritiesBound size (by simp only [arities, List.mem_append]; exact Or.inl member)
    have replacementArities : ∀ size ∈ arities replacement, size ≤ maximumArity alphabet := by
      intro size member
      exact aritiesBound size (by simp only [arities, List.mem_append]; exact Or.inr member)
    simp only [IndicesBelow]
    refine ⟨indicesBelow_mono (depth + 1 + nodes body * (maximumArity alphabet + 1))
      (depth + budget * (maximumArity alphabet + 1)) body (bodyIH (depth + 1) (nodes body) (Nat.le_refl _) scope.1 bodyArities)
      (by omega), replacementIH depth budget replacementBound scope.2 replacementArities⟩
  | hcollection kind elements rest ih =>
    simp only [IndicesBelow]
    intro element member
    have scopedTerm := (Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff
      depth elements).mp scope element member
    have supported : ∀ arity ∈ arities element, arity ≤ maximumArity alphabet := by
      intro arity occurs
      exact aritiesBound arity (by simp only [arities, List.mem_flatMap]; exact ⟨element, member, occurs⟩)
    exact ih element member depth budget ((member_nodes_le member).trans (by simp only [nodes] at small; omega))
      scopedTerm supported

/-- The final filter constructs the actual sorted finite carrier. Failed
sorting contributes no term, and completeness uses the independent typing
judgment and the earned checker theorem. -/
def typedUniverse (alphabet : Alphabet) (indexBound budget : Nat) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr) : List Pattern :=
  (terms alphabet indexBound budget).filter fun pattern =>
    decide (nodes pattern ≤ budget) && checkOpenPatternWellSorted language free bound expected pattern

theorem typedUniverse_sound (alphabet : Alphabet) (indexBound budget : Nat) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr) (pattern : Pattern)
    (member : pattern ∈ typedUniverse alphabet indexBound budget language free bound expected) :
    nodes pattern ≤ budget ∧ OpenPatternWellSorted language free bound expected pattern := by
  have checks := (List.mem_filter.mp member).2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at checks
  exact ⟨checks.1, checkOpenPatternWellSorted_sound checks.2⟩

theorem typedUniverse_complete (alphabet : Alphabet) (indexBound budget : Nat) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr) (pattern : Pattern)
    (typed : OpenPatternWellSorted language free bound expected pattern)
    (small : nodes pattern ≤ budget) (support : Supported alphabet pattern)
    (indices : IndicesBelow indexBound pattern) :
    pattern ∈ typedUniverse alphabet indexBound budget language free bound expected := by
  apply List.mem_filter.mpr
  refine ⟨terms_complete alphabet indexBound pattern budget small support indices typed.2.1 typed.2.2.1, ?_⟩
  simp only [small, decide_true, checkOpenPatternWellSorted_complete typed, Bool.and_self]

def sourceUniverse (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (providerTerms : List Pattern) : List Pattern :=
  let symbols := alphabet language source providerTerms
  typedUniverse symbols (bound.length + nodes source * (maximumArity symbols + 1))
    (nodes source) language free bound expected

theorem sourceUniverse_contains_source (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) (providerTerms : List Pattern)
    (typed : OpenPatternWellSorted language free bound expected source) :
    source ∈ sourceUniverse language free bound expected source providerTerms := by
  have support := source_supported language source providerTerms
  apply typedUniverse_complete _ _ _ language free bound expected source typed (Nat.le_refl _) support
  exact scoped_indices _ source bound.length (nodes source) (Nat.le_refl _) typed.2.2.2
    (fun arity member => arity_le_maximum _ arity (support.2.2 arity member))

end Mettapedia.OSLF.Framework.GeneralFiniteTermUniverse
