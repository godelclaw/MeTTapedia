import Mettapedia.Languages.MeTTa.HE.Space
import Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge
import Mathlib.Data.Multiset.Filter

/-!
# HE type occurrences and explicit enumeration profiles

This module gives relational counterparts of the published `get atom types`,
`match_types`, `type_cast`, `check_argument_type`, and
`check_if_function_type_is_applicable` pseudocode.  No constructor mentions an
executable type checker or a fuel budget.

Type occurrences are collected from a multiset space. The language contract
does not identify their enumeration with the storage order. First-success
casts and function selection use an explicit enumeration policy; changing that
policy can change a selected binding. `StorageTypesRel` is the separately
named list-storage profile used by the existing executable correspondences.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Match.Merge

/-! ## Type lookup -/

/-- Ordered extraction of direct declarations from a list representation.
This is a storage-profile relation, not the order of a language-level space. -/
inductive AnnotationTypesRel (target : Atom) :
    List Atom → List Atom → Prop where
  | nil : AnnotationTypesRel target [] []
  | hit {type : Atom} {tail types : List Atom} :
      AnnotationTypesRel target tail types →
      AnnotationTypesRel target
        (.expression [.symbol ":", target, type] :: tail) (type :: types)
  | skip {head : Atom} {tail types : List Atom} :
      (∀ type, head ≠ .expression [.symbol ":", target, type]) →
      AnnotationTypesRel target tail types →
      AnnotationTypesRel target (head :: tail) types

/-- Ordered annotation extraction is functional. -/
theorem AnnotationTypesRel.unique
    {target : Atom} {atoms left right : List Atom}
    (hleft : AnnotationTypesRel target atoms left)
    (hright : AnnotationTypesRel target atoms right) : left = right := by
  induction hleft generalizing right with
  | nil =>
      cases hright
      rfl
  | hit htail ih =>
      cases hright with
      | hit hright => exact congrArg (List.cons _) (ih hright)
      | skip hskip _ => exact (hskip _ rfl).elim
  | skip hskip htail ih =>
      cases hright with
      | hit _ => exact (hskip _ rfl).elim
      | skip _ hright => exact ih hright

/-- Intrinsic type supplied by a grounded payload. -/
inductive IntrinsicGroundedTypeRel : GroundedValue → Atom → Prop where
  | int (value : Int) :
      IntrinsicGroundedTypeRel (.int value) (.symbol "Number")
  | bool (value : Bool) :
      IntrinsicGroundedTypeRel (.bool value) (.symbol "Bool")
  | string (value : String) :
      IntrinsicGroundedTypeRel (.string value) (.symbol "String")
  | custom (type payload : String) :
      IntrinsicGroundedTypeRel (.custom type payload) (.symbol type)

theorem IntrinsicGroundedTypeRel.unique {value : GroundedValue} {left right : Atom}
    (a : IntrinsicGroundedTypeRel value left) (b : IntrinsicGroundedTypeRel value right) : left = right := by
  cases a <;> cases b <;> rfl

/-- The content of a declaration, independent of a space representation. -/
def annotationType? (target : Atom) : Atom → Option Atom
  | .expression [.symbol ":", subject, type] =>
      if subject == target then some type else none
  | _ => none

theorem annotationType?_eq_some_iff {target row type : Atom} :
    annotationType? target row = some type ↔
      row = .expression [.symbol ":", target, type] := by
  constructor
  · intro found
    simp only [annotationType?] at found
    split at found
    next subject candidate _shape =>
      split at found
      next same =>
        cases found
        exact congrArg (fun atom : Atom => Atom.expression [Atom.symbol ":", atom, type])
          (beq_iff_eq.mp same)
      next => contradiction
    next => contradiction
  · rintro rfl
    simp [annotationType?]

/-- All stored declaration occurrences, retaining duplicate copies. -/
def annotationOccurrences (atoms : Multiset Atom) (subject : Atom) : Multiset Atom :=
  atoms.filterMap (annotationType? subject)

/-- The fallback is applied after the complete collection is known empty. -/
def withUndefined (types : Multiset Atom) : Multiset Atom :=
  if types = 0 then {Atom.undefinedType} else types

@[simp] theorem withUndefined_nonempty (types : Multiset Atom) : withUndefined types ≠ 0 := by
  unfold withUndefined
  split <;> simp_all

/-- The source type collection. Its space and result are multisets; no rule
selects a list-storage traversal. Enumeration is a separate contract. -/
inductive TypeOccurrencesRel (atoms : Multiset Atom) : Atom → Multiset Atom → Prop where
  | variable (name : String) : TypeOccurrencesRel atoms (.var name) {Atom.undefinedType}
  | grounded {value : GroundedValue} {type : Atom} :
      IntrinsicGroundedTypeRel value type → TypeOccurrencesRel atoms (.grounded value) {type}
  | symbol (name : String) : TypeOccurrencesRel atoms (.symbol name)
      (withUndefined (annotationOccurrences atoms (.symbol name)))
  | unit : TypeOccurrencesRel atoms (.expression []) {Atom.undefinedType}
  | expression (head : Atom) (tail : List Atom) :
      TypeOccurrencesRel atoms (.expression (head :: tail))
        (withUndefined (annotationOccurrences atoms (.expression (head :: tail))))

theorem TypeOccurrencesRel.unique {atoms : Multiset Atom} {subject : Atom} {first second : Multiset Atom}
    (left : TypeOccurrencesRel atoms subject first) (right : TypeOccurrencesRel atoms subject second) :
    first = second := by
  cases left <;> cases right <;> try rfl
  exact congrArg (fun type : Atom => ({type} : Multiset Atom))
    (IntrinsicGroundedTypeRel.unique ‹_› ‹_›)

theorem TypeOccurrencesRel.nonempty {atoms : Multiset Atom} {subject : Atom} {types : Multiset Atom}
    (collected : TypeOccurrencesRel atoms subject types) : types ≠ 0 := by
  cases collected <;> simp_all

theorem AnnotationTypesRel.complete (target : Atom) (atoms : List Atom) :
    AnnotationTypesRel target atoms (atoms.filterMap (annotationType? target)) := by
  induction atoms with
  | nil => exact .nil
  | cons head tail ih =>
      cases found : annotationType? target head with
      | none =>
          rw [List.filterMap_cons, found]
          refine .skip ?_ ih
          intro type same
          subst head
          simp [annotationType?] at found
      | some type =>
          have same := annotationType?_eq_some_iff.mp found
          rw [List.filterMap_cons, found]
          exact same ▸ AnnotationTypesRel.hit ih

theorem AnnotationTypesRel.occurrences {target : Atom} {atoms types : List Atom}
    (extracted : AnnotationTypesRel target atoms types) :
    annotationOccurrences (atoms : Multiset Atom) target = (types : Multiset Atom) :=
  congrArg (fun list : List Atom => (list : Multiset Atom))
    ((AnnotationTypesRel.complete target atoms).unique extracted)

/-- The complete type list for the list-storage enumeration profile. -/
inductive StorageTypesRel : Space → Atom → List Atom → Prop where
  | variable (space : Space) (name : String) :
      StorageTypesRel space (.var name) [Atom.undefinedType]
  | groundedKnown {space : Space} {value : GroundedValue} {type : Atom} :
      IntrinsicGroundedTypeRel value type →
      type ≠ Atom.undefinedType →
      StorageTypesRel space (.grounded value) [type]
  | groundedUndefined {space : Space} {value : GroundedValue} :
      IntrinsicGroundedTypeRel value Atom.undefinedType →
      StorageTypesRel space (.grounded value) [Atom.undefinedType]
  | symbolKnown {space : Space} {name : String} {types : List Atom} :
      AnnotationTypesRel (.symbol name) space.atoms types →
      types ≠ [] →
      StorageTypesRel space (.symbol name) types
  | symbolUndefined {space : Space} {name : String} :
      AnnotationTypesRel (.symbol name) space.atoms [] →
      StorageTypesRel space (.symbol name) [Atom.undefinedType]
  | unit (space : Space) :
      StorageTypesRel space (.expression []) [Atom.undefinedType]
  | expressionKnown {space : Space} {head : Atom} {tail types : List Atom} :
      AnnotationTypesRel (.expression (head :: tail)) space.atoms types →
      types ≠ [] →
      StorageTypesRel space (.expression (head :: tail)) types
  | expressionUndefined {space : Space} {head : Atom} {tail : List Atom} :
      AnnotationTypesRel (.expression (head :: tail)) space.atoms [] →
      StorageTypesRel space (.expression (head :: tail)) [Atom.undefinedType]

/-- This particular storage enumeration is functional. Other complete
enumerations need not return this list in this order. -/
theorem StorageTypesRel.unique {space : Space} {atom : Atom} {left right : List Atom}
    (a : StorageTypesRel space atom left) (b : StorageTypesRel space atom right) : left = right := by
  cases a with
  | «variable» => cases b; rfl
  | groundedKnown intrinsic ordinary =>
      cases b with
      | groundedKnown other _ => exact congrArg (fun type => [type]) (intrinsic.unique other)
      | groundedUndefined other => exact (ordinary (intrinsic.unique other)).elim
  | groundedUndefined intrinsic =>
      cases b with
      | groundedKnown other ordinary => exact (ordinary (other.unique intrinsic)).elim
      | groundedUndefined => rfl
  | symbolKnown annotations nonempty =>
      cases b with
      | symbolKnown other _ => exact annotations.unique other
      | symbolUndefined other => exact (nonempty (annotations.unique other)).elim
  | symbolUndefined annotations =>
      cases b with
      | symbolKnown other nonempty => exact (nonempty (other.unique annotations)).elim
      | symbolUndefined => rfl
  | unit => cases b; rfl
  | expressionKnown annotations nonempty =>
      cases b with
      | expressionKnown other _ => exact annotations.unique other
      | expressionUndefined other => exact (nonempty (annotations.unique other)).elim
  | expressionUndefined annotations =>
      cases b with
      | expressionKnown other nonempty => exact (nonempty (other.unique annotations)).elim
      | expressionUndefined => rfl

theorem StorageTypesRel.nonempty {space : Space} {atom : Atom} {types : List Atom}
    (queried : StorageTypesRel space atom types) : types ≠ [] := by
  cases queried <;> simp_all

/-- Forgetting storage order yields the independently collected source
occurrences, including all duplicate declarations and the empty fallback. -/
theorem StorageTypesRel.occurrences {space : Space} {subject : Atom} {types : List Atom}
    (queried : StorageTypesRel space subject types) :
    TypeOccurrencesRel (space.atoms : Multiset Atom) subject (types : Multiset Atom) := by
  cases queried with
  | «variable» => exact .variable _
  | groundedKnown intrinsic _ | groundedUndefined intrinsic => exact .grounded intrinsic
  | @symbolKnown name _ declarations nonempty =>
      have nonzero : (types : Multiset Atom) ≠ 0 := by simpa using nonempty
      simpa only [withUndefined, declarations.occurrences, if_neg nonzero] using
        (TypeOccurrencesRel.symbol (atoms := (space.atoms : Multiset Atom)) name)
  | @symbolUndefined name declarations =>
      simpa [withUndefined, declarations.occurrences] using
        (TypeOccurrencesRel.symbol (atoms := (space.atoms : Multiset Atom)) name)
  | unit => exact .unit
  | @expressionKnown head tail _ declarations nonempty =>
      have nonzero : (types : Multiset Atom) ≠ 0 := by simpa using nonempty
      simpa only [withUndefined, declarations.occurrences, if_neg nonzero] using
        (TypeOccurrencesRel.expression (atoms := (space.atoms : Multiset Atom)) head tail)
  | @expressionUndefined head tail declarations =>
      simpa [withUndefined, declarations.occurrences] using
        (TypeOccurrencesRel.expression (atoms := (space.atoms : Multiset Atom)) head tail)

/-- The list-storage profile is total; this does not privilege its order. -/
theorem StorageTypesRel.total (space : Space) (subject : Atom) :
    ∃ types, StorageTypesRel space subject types := by
  cases subject with
  | var name => exact ⟨_, .variable space name⟩
  | grounded value =>
      have intrinsic : ∃ type, IntrinsicGroundedTypeRel value type := by cases value <;> exact ⟨_, by constructor⟩
      obtain ⟨type, intrinsic⟩ := intrinsic
      by_cases same : type = Atom.undefinedType
      · subst type; exact ⟨_, .groundedUndefined intrinsic⟩
      · exact ⟨_, .groundedKnown intrinsic same⟩
  | symbol name =>
      have declarations := AnnotationTypesRel.complete (.symbol name) space.atoms
      by_cases empty : space.atoms.filterMap (annotationType? (.symbol name)) = []
      · exact ⟨_, .symbolUndefined (empty ▸ declarations)⟩
      · exact ⟨_, .symbolKnown declarations empty⟩
  | expression children =>
      cases children with
      | nil => exact ⟨_, .unit space⟩
      | cons head tail =>
          have declarations := AnnotationTypesRel.complete (.expression (head :: tail)) space.atoms
          by_cases empty : space.atoms.filterMap (annotationType? (.expression (head :: tail))) = []
          · exact ⟨_, .expressionUndefined (empty ▸ declarations)⟩
          · exact ⟨_, .expressionKnown declarations empty⟩

/-- A singleton undefined collection is independent of storage order. -/
theorem StorageTypesRel.undefined_iff_occurrences (space : Space) (subject : Atom) :
    StorageTypesRel space subject [Atom.undefinedType] ↔
      TypeOccurrencesRel (space.atoms : Multiset Atom) subject {Atom.undefinedType} := by
  constructor
  · exact StorageTypesRel.occurrences
  · intro collected
    obtain ⟨types, queried⟩ := StorageTypesRel.total space subject
    have perm : types.Perm [Atom.undefinedType] :=
      Multiset.coe_eq_coe.mp (queried.occurrences.unique collected)
    have same : types = [Atom.undefinedType] := List.perm_singleton.mp perm
    exact same ▸ queried

/-- A legal complete query, without choosing an execution policy. This is
not an evaluator policy: incompatible enumerations are not pooled into a run. -/
def CompleteTypeQueryRel (space : Space) (subject : Atom) (types : List Atom) : Prop :=
  TypeOccurrencesRel (space.atoms : Multiset Atom) subject (types : Multiset Atom)

/-- A complete enumeration has exactly the source occurrence bag. A policy
may choose storage order, reverse order, or another complete traversal. -/
structure TypeEnumeration where
  query : Space → Atom → List Atom → Prop
  sound : ∀ {space subject types}, query space subject types →
    TypeOccurrencesRel (space.atoms : Multiset Atom) subject (types : Multiset Atom)
  complete : ∀ space subject, ∃ types, query space subject types
  unique : ∀ {space subject first second}, query space subject first →
    query space subject second → first = second

namespace TypeEnumeration

def storage : TypeEnumeration :=
  ⟨StorageTypesRel, StorageTypesRel.occurrences, StorageTypesRel.total, StorageTypesRel.unique⟩

/-- Alternative policies can be built without extending a closed policy enum. -/
def reorder (enumeration : TypeEnumeration) (order : List Atom → List Atom)
    (preserves : ∀ types, (order types).Perm types) : TypeEnumeration where
  query space subject selected := ∃ types, enumeration.query space subject types ∧ selected = order types
  sound := by
    rintro space subject _ ⟨types, queried, rfl⟩
    have same : (order types : Multiset Atom) = (types : Multiset Atom) :=
      Multiset.coe_eq_coe.mpr (preserves types)
    rw [same]
    exact enumeration.sound queried
  complete space subject := by
    obtain ⟨types, queried⟩ := enumeration.complete space subject
    exact ⟨order types, types, queried, rfl⟩
  unique := by
    rintro space subject _ _ ⟨first, firstQuery, rfl⟩ ⟨second, secondQuery, rfl⟩
    exact congrArg order (enumeration.unique firstQuery secondQuery)

theorem admissible (enumeration : TypeEnumeration) {space : Space} {subject : Atom} {types : List Atom}
    (queried : enumeration.query space subject types) : CompleteTypeQueryRel space subject types :=
  enumeration.sound queried

/-- Two complete policies agree on occurrences, not necessarily on order. -/
theorem occurrences_perm (first second : TypeEnumeration) {space : Space} {subject : Atom}
    {left right : List Atom} (a : first.query space subject left) (b : second.query space subject right) :
    left.Perm right := Multiset.coe_eq_coe.mp ((first.sound a).unique (second.sound b))

/-- A singleton undefined collection has the same enumeration under every
complete policy. No storage order or choice between policies is observed. -/
theorem undefined_iff_occurrences (enumeration : TypeEnumeration) (space : Space) (subject : Atom) :
    enumeration.query space subject [Atom.undefinedType] ↔
      TypeOccurrencesRel (space.atoms : Multiset Atom) subject {Atom.undefinedType} := by
  constructor
  · exact enumeration.sound
  · intro collected
    obtain ⟨types, queried⟩ := enumeration.complete space subject
    have same : types = [Atom.undefinedType] :=
      List.perm_singleton.mp (Multiset.coe_eq_coe.mp ((enumeration.sound queried).unique collected))
    exact same ▸ queried

/-- Reordering storage cannot change which complete enumerations the source
allows. The enumeration used at a first-success boundary remains explicit. -/
theorem complete_query_space_perm {first second : Space} (same : first.atoms.Perm second.atoms)
    (subject : Atom) (types : List Atom) :
    CompleteTypeQueryRel first subject types ↔ CompleteTypeQueryRel second subject types := by
  change TypeOccurrencesRel (first.atoms : Multiset Atom) subject (types : Multiset Atom) ↔
    TypeOccurrencesRel (second.atoms : Multiset Atom) subject (types : Multiset Atom)
  rw [Multiset.coe_eq_coe.mpr same]

end TypeEnumeration

/-- Type membership in the explicit list-storage profile. -/
def TypeOfRel (space : Space) (atom type : Atom) : Prop :=
  ∃ types, StorageTypesRel space atom types ∧ type ∈ types

/-! ## Type matching and casting -/

/-- Declarative `match_types`.  `%Undefined%` and `Atom` are wildcards; every
other case uses the already independent spec match and merge relations. -/
inductive TypeMatchRel : Atom → Atom → Bindings → Bindings → Prop where
  | undefinedLeft (right : Atom) (bindings : Bindings) :
      TypeMatchRel Atom.undefinedType right bindings bindings
  | atomLeft (right : Atom) (bindings : Bindings) :
      TypeMatchRel Atom.atomType right bindings bindings
  | undefinedRight (left : Atom) (bindings : Bindings) :
      TypeMatchRel left Atom.undefinedType bindings bindings
  | atomRight (left : Atom) (bindings : Bindings) :
      TypeMatchRel left Atom.atomType bindings bindings
  | structural {left right : Atom} {bindings matched output : Bindings} :
      left ≠ Atom.undefinedType →
      left ≠ Atom.atomType →
      right ≠ Atom.undefinedType →
      right ≠ Atom.atomType →
      MatchRel equalityGroundedSemantic left right matched →
      MergeRel equalityGroundedSemantic bindings matched output →
      TypeMatchRel left right bindings output

/-- Undefined demand is a wildcard without a binding update, for every
source derivation rather than only the selected runtime match. -/
theorem TypeMatchRel.wildcard_output {expected actual : Atom} {before after : Bindings}
    (matched : TypeMatchRel expected actual before after)
    (wildcard : expected = Atom.undefinedType ∨ expected = Atom.atomType ∨
      actual = Atom.undefinedType ∨ actual = Atom.atomType) : after = before := by
  cases matched with
  | undefinedLeft | atomLeft | undefinedRight | atomRight => rfl
  | structural leftUndefined leftAtom rightUndefined rightAtom _ _ =>
      rcases wildcard with same | same | same | same
      · exact (leftUndefined same).elim
      · exact (leftAtom same).elim
      · exact (rightUndefined same).elim
      · exact (rightAtom same).elim

theorem TypeMatchRel.undefined_output {actual : Atom} {before after : Bindings}
    (matched : TypeMatchRel Atom.undefinedType actual before after) : after = before :=
  matched.wildcard_output (Or.inl rfl)

/-- Outside the two wildcard types, every type-match derivation exposes one
ordinary spec match followed by one spec merge. -/
theorem TypeMatchRel.structural_of_nonWildcard
    {left right : Atom} {bindings output : Bindings}
    (hLeftUndefined : left ≠ Atom.undefinedType)
    (hLeftAtom : left ≠ Atom.atomType)
    (hRightUndefined : right ≠ Atom.undefinedType)
    (hRightAtom : right ≠ Atom.atomType)
    (hmatch : TypeMatchRel left right bindings output) :
    ∃ matched,
      MatchRel equalityGroundedSemantic left right matched ∧
        MergeRel equalityGroundedSemantic bindings matched output := by
  cases hmatch with
  | undefinedLeft => exact (hLeftUndefined rfl).elim
  | atomLeft => exact (hLeftAtom rfl).elim
  | undefinedRight => exact (hRightUndefined rfl).elim
  | atomRight => exact (hRightAtom rfl).elim
  | structural _ _ _ _ hspec hmerge => exact ⟨_, hspec, hmerge⟩

/-- A fresh expected variable receives a symbolic actual type. This is a
source match/merge derivation, independent of an executable type matcher. -/
theorem TypeMatchRel.expected_variable_symbol (name actual : String) (before : Bindings)
    (notUndefined : actual ≠ "%Undefined%") (notAtom : actual ≠ "Atom")
    (fresh : before.classValues name = []) :
    TypeMatchRel (.var name) (.symbol actual) before (before.assign name (.symbol actual)) := by
  apply TypeMatchRel.structural (matched := Bindings.empty.assign name (.symbol actual))
  · intro same; cases same
  · intro same; cases same
  · simpa [Atom.undefinedType] using notUndefined
  · simpa [Atom.atomType] using notAtom
  · exact .varNonVar rfl (semanticLoopFree_single_assignment (by intro occurs; cases occurs))
  · apply MergeRel.mk (order := [.value name (.symbol actual)])
    · exact List.Perm.refl _
    · exact .value (.fresh fresh) .nil

/-- One complete type enumeration at a use site. The incoming constraints
and expected type belong to its protected context. List position describes
this enumeration, not the physical order of the source space. -/
abbrev TypeLookupRel := Bindings → Atom → Atom → List Atom → Prop

def enumerationLookup (enumeration : TypeEnumeration) (space : Space) : TypeLookupRel :=
  fun _ subject _ candidates => enumeration.query space subject candidates

/-- Admissibility for an individual query. It is not a whole-run enumeration policy. -/
def completeTypeLookupRel (space : Space) : TypeLookupRel :=
  fun _ subject _ candidates => CompleteTypeQueryRel space subject candidates

/-- Literal lookup with the historical list-storage enumeration. -/
def rawTypeLookupRel (space : Space) : TypeLookupRel :=
  fun _ subject _ candidates => StorageTypesRel space subject candidates

/-- One physical type occurrence in the ordered list returned at this use. -/
def TypeAtRel (lookup : TypeLookupRel) (bindings : Bindings)
    (subject expected actual : Atom) : Prop :=
  ∃ candidates, lookup bindings subject expected candidates ∧ actual ∈ candidates

/-- Relational `type_cast`, with first success relative to the supplied type
enumeration. Operand orientation is the historical expected/actual profile;
matching is explicitly parameterized in the completed relation below.
On total failure, every discovered actual-type occurrence contributes an error. -/
inductive TypeCastRel (space : Space) (atom expectedType : Atom)
    (bindings : Bindings) : ResultPair →
      (lookup : TypeLookupRel := rawTypeLookupRel space) → Prop where
  | success {types earlierTypes laterTypes : List Atom} {actualType : Atom}
      {output : Bindings} :
      lookup bindings atom expectedType types →
      types = earlierTypes ++ actualType :: laterTypes →
      (∀ earlier ∈ earlierTypes, ∀ candidate,
        ¬TypeMatchRel expectedType earlier bindings candidate) →
      TypeMatchRel expectedType actualType bindings output →
      TypeCastRel space atom expectedType bindings (lookup := lookup) (atom, output)
  | failure {types : List Atom} {actualType : Atom} :
      lookup bindings atom expectedType types →
      actualType ∈ types →
      (∀ candidateType ∈ types, ∀ candidate,
        ¬TypeMatchRel expectedType candidateType bindings candidate) →
      TypeCastRel space atom expectedType bindings (lookup := lookup)
        (mkError atom (.badType expectedType actualType), bindings)

/-- A completed cast accounts for the ordered type query, rather than one
possible result. The first applicable type contributes one chosen principal
binding presentation; complete failure retains one error per type occurrence.
Lookup and type matching are independent local source policies. The default
matching policy retains the historical raw relation. -/
inductive TypeCastBatchRel (space : Space) (atom expectedType : Atom)
    (bindings : Bindings) : ResultSet →
      (lookup : TypeLookupRel := rawTypeLookupRel space) →
      (matching : Atom → Atom → Bindings → Bindings → Prop := TypeMatchRel) → Prop where
  | success {lookup : TypeLookupRel}
      {matching : Atom → Atom → Bindings → Bindings → Prop}
      {types earlierTypes laterTypes : List Atom} {actualType : Atom}
      {output : Bindings} :
      lookup bindings atom expectedType types →
      types = earlierTypes ++ actualType :: laterTypes →
      (∀ earlier ∈ earlierTypes, ∀ candidate,
        ¬matching expectedType earlier bindings candidate) →
      matching expectedType actualType bindings output →
      TypeCastBatchRel space atom expectedType bindings (lookup := lookup)
        (matching := matching) [(atom, output)]
  | failure {lookup : TypeLookupRel}
      {matching : Atom → Atom → Bindings → Bindings → Prop} {types : List Atom} :
      lookup bindings atom expectedType types →
      (∀ candidateType ∈ types, ∀ candidate,
        ¬matching expectedType candidateType bindings candidate) →
      TypeCastBatchRel space atom expectedType bindings (lookup := lookup) (matching := matching)
        (types.map fun actualType => (mkError atom (.badType expectedType actualType), bindings))

/-- Every complete raw type query under undefined demand publishes one
unchanged atom/binding pair. A prefix without a type occurrence is not used
as evidence for failure. -/
theorem TypeCastBatchRel.undefined_exact {space : Space} {atom : Atom} {bindings : Bindings}
    {results : ResultSet} (source : TypeCastBatchRel space atom Atom.undefinedType bindings results) :
    results = [(atom,bindings)] := by
  cases source with
  | success _queried _selected _rejected matched =>
      simp only [matched.undefined_output]
  | failure queried rejected =>
      have nonempty := (show StorageTypesRel space atom _ from queried).nonempty
      obtain ⟨actual,member⟩ := List.exists_mem_of_ne_nil _ nonempty
      exact (rejected actual member bindings (.undefinedLeft _ _)).elim

/-- Every occurrence of the default raw cast has the existing independent
single-result source derivation. The batch additionally fixes its count. -/
theorem TypeCastBatchRel.member
    {space : Space} {atom expected : Atom} {bindings : Bindings}
    {lookup : TypeLookupRel} {results : ResultSet}
    (completed : TypeCastBatchRel space atom expected bindings results (lookup := lookup))
    {result : ResultPair} (present : result ∈ results) :
    TypeCastRel space atom expected bindings result (lookup := lookup) := by
  cases completed with
  | success queried selected rejected matched =>
      obtain rfl := List.mem_singleton.mp present
      exact .success queried selected rejected matched
  | failure queried rejected =>
      obtain ⟨actual,member,rfl⟩ := List.mem_map.mp present
      exact .failure queried member rejected

/-- Duplicate annotation occurrences remain duplicate failure occurrences. -/
theorem TypeCastBatchRel.failure_length
    {space : Space} {atom expected : Atom} {bindings : Bindings}
    {lookup : TypeLookupRel} {types : List Atom}
    {matching : Atom → Atom → Bindings → Bindings → Prop}
    (queried : lookup bindings atom expected types)
    (rejected : ∀ actual ∈ types, ∀ output, ¬matching expected actual bindings output) :
    ∃ results, TypeCastBatchRel space atom expected bindings results (lookup := lookup)
      (matching := matching) ∧
      results.length = types.length :=
  ⟨_, .failure queried rejected, by simp⟩

/-- A completed cast cannot mix errors with a successful occurrence. -/
theorem TypeCastBatchRel.no_mixed_errors
    {space : Space} {atom expected : Atom} {bindings : Bindings}
    {lookup : TypeLookupRel} {results : ResultSet}
    {matching : Atom → Atom → Bindings → Bindings → Prop}
    (completed : TypeCastBatchRel space atom expected bindings results (lookup := lookup)
      (matching := matching))
    {good result : ResultPair} (presentGood : good ∈ results)
    (accepted : isErrorAtom good.1 = false) (present : result ∈ results) :
    isErrorAtom result.1 = false := by
  cases completed with
  | success =>
      obtain rfl := List.mem_singleton.mp presentGood
      obtain rfl := List.mem_singleton.mp present
      exact accepted
  | failure =>
      obtain ⟨_,_,same⟩ := List.mem_map.mp presentGood
      have failed : isErrorAtom good.1 = true := by
        rw [←same]
        rfl
      cases accepted.symm.trans failed

/-- A local implication between complete query contracts transports the
whole cast, retaining first-success precedence and every failed occurrence. -/
theorem TypeCastBatchRel.change_lookup
    {space : Space} {atom expected : Atom} {bindings : Bindings} {results : ResultSet}
    {firstLookup secondLookup : TypeLookupRel}
    {matching : Atom → Atom → Bindings → Bindings → Prop}
    (source : TypeCastBatchRel space atom expected bindings results
      (lookup := firstLookup) (matching := matching))
    (query : ∀ types, firstLookup bindings atom expected types →
      secondLookup bindings atom expected types) :
    TypeCastBatchRel space atom expected bindings results
      (lookup := secondLookup) (matching := matching) := by
  cases source with
  | success queried selected rejected matched =>
      exact .success (query _ queried) selected rejected matched
  | failure queried rejected => exact .failure (query _ queried) rejected

/-- A cast using a complete enumeration is admitted by the source's open
enumeration contract. First-success precedence is retained relative to the
chosen enumeration; this is not an order-independence theorem. -/
theorem TypeCastBatchRel.admit_enumeration
    {enumeration : TypeEnumeration} {space : Space} {atom expected : Atom}
    {bindings : Bindings} {results : ResultSet}
    {matching : Atom → Atom → Bindings → Bindings → Prop}
    (source : TypeCastBatchRel space atom expected bindings results
      (lookup := enumerationLookup enumeration space) (matching := matching)) :
    TypeCastBatchRel space atom expected bindings results
      (lookup := completeTypeLookupRel space) (matching := matching) :=
  source.change_lookup (fun _ queried => enumeration.admissible queried)

/-- Storage permutation preserves the entire set of source-admissible cast
derivations, including the enumeration used by first-success selection.
It does not require two fixed enumeration policies to make the same choice. -/
theorem TypeCastBatchRel.complete_space_perm
    {first second : Space} (same : first.atoms.Perm second.atoms)
    {atom expected : Atom} {bindings : Bindings} {results : ResultSet}
    {matching : Atom → Atom → Bindings → Bindings → Prop} :
    TypeCastBatchRel first atom expected bindings results
      (lookup := completeTypeLookupRel first) (matching := matching) ↔
    TypeCastBatchRel second atom expected bindings results
      (lookup := completeTypeLookupRel second) (matching := matching) := by
  constructor
  · intro source
    cases source with
    | success queried selected rejected matched =>
        exact .success ((TypeEnumeration.complete_query_space_perm same _ _).mp queried)
          selected rejected matched
    | failure queried rejected =>
        exact .failure ((TypeEnumeration.complete_query_space_perm same _ _).mp queried) rejected
  · intro source
    cases source with
    | success queried selected rejected matched =>
        exact .success ((TypeEnumeration.complete_query_space_perm same _ _).mpr queried)
          selected rejected matched
    | failure queried rejected =>
        exact .failure ((TypeEnumeration.complete_query_space_perm same _ _).mpr queried) rejected

namespace EnumerationControls

private def subject : Atom := .symbol "value"
private def declarations : Space := ⟨[
  .expression [.symbol ":", subject, .symbol "A"],
  .expression [.symbol ":", subject, .symbol "A"],
  .expression [.symbol ":", subject, .symbol "B"]]⟩

private theorem storage_query :
    TypeEnumeration.storage.query declarations subject [.symbol "A", .symbol "A", .symbol "B"] :=
  .symbolKnown (.hit (.hit (.hit .nil))) (by decide)

private def backwards : TypeEnumeration :=
  TypeEnumeration.storage.reorder List.reverse List.reverse_perm

/-- A complete alternate traversal keeps both copies of the A declaration. -/
theorem duplicate_occurrences_retained :
    CompleteTypeQueryRel declarations subject [.symbol "B", .symbol "A", .symbol "A"] ∧
    Multiset.count (.symbol "A")
      ([Atom.symbol "B", Atom.symbol "A", Atom.symbol "A"] : Multiset Atom) = 2 := by
  constructor
  · exact backwards.admissible ⟨_, storage_query, rfl⟩
  · decide

/-- The interface rejects a traversal that silently drops a duplicate. -/
theorem dropped_duplicate_not_complete (enumeration : TypeEnumeration) :
    ¬enumeration.query declarations subject [.symbol "A", .symbol "B"] := by
  intro queried
  have sameLength := (enumeration.occurrences_perm .storage queried storage_query).length_eq
  contradiction

/-- Negative control: actual first-success cast derivations under two legal
enumerations can bind the expected type differently. An unconditional
order-invariance claim for selected bindings would therefore be false. -/
theorem first_success_can_change_binding :
    TypeCastBatchRel declarations subject (.var "t") Bindings.empty
      [(subject, Bindings.empty.assign "t" (.symbol "A"))]
      (lookup := enumerationLookup .storage declarations) ∧
    TypeCastBatchRel declarations subject (.var "t") Bindings.empty
      [(subject, Bindings.empty.assign "t" (.symbol "B"))]
      (lookup := enumerationLookup backwards declarations) ∧
    Bindings.empty.assign "t" (.symbol "A") ≠ Bindings.empty.assign "t" (.symbol "B") := by
  refine ⟨?_, ?_, by decide⟩
  · exact .success (earlierTypes := []) storage_query rfl (by simp)
      (.expected_variable_symbol "t" "A" _ (by decide) (by decide) (by decide))
  · exact .success (earlierTypes := []) ⟨_, storage_query, rfl⟩ rfl (by simp)
      (.expected_variable_symbol "t" "B" _ (by decide) (by decide) (by decide))

end EnumerationControls

/-- A local comparison on the actual complete query suffices to change the
matching policy. First-success selection and every failure occurrence are
preserved; no whole-evaluator correspondence is assumed. -/
theorem TypeCastBatchRel.change_matching
    {space : Space} {atom expected : Atom} {bindings : Bindings}
    {lookup : TypeLookupRel} {results : ResultSet}
    {firstMatching secondMatching : Atom → Atom → Bindings → Bindings → Prop}
    (source : TypeCastBatchRel space atom expected bindings results (lookup := lookup)
      (matching := firstMatching))
    (same : ∀ types, lookup bindings atom expected types →
      ∀ actual ∈ types, ∀ output,
        firstMatching expected actual bindings output ↔ secondMatching expected actual bindings output) :
    TypeCastBatchRel space atom expected bindings results (lookup := lookup)
      (matching := secondMatching) := by
  cases source with
  | @success _ _ types earlier later actual output queried selected rejected matched =>
      apply TypeCastBatchRel.success queried selected
      · intro prior present candidate accepted
        apply rejected prior present candidate
        apply (same types queried prior ?_ candidate).mpr accepted
        rw [selected]
        exact List.mem_append_left _ present
      · apply (same types queried actual ?_ output).mp matched
        rw [selected]
        simp
  | failure queried rejected =>
      apply TypeCastBatchRel.failure queried
      intro actual present candidate accepted
      exact rejected actual present candidate ((same _ queried actual present candidate).mpr accepted)

theorem TypeCastBatchRel.matching_iff
    {space : Space} {atom expected : Atom} {bindings : Bindings}
    {lookup : TypeLookupRel} {results : ResultSet}
    {firstMatching secondMatching : Atom → Atom → Bindings → Bindings → Prop}
    (same : ∀ types, lookup bindings atom expected types →
      ∀ actual ∈ types, ∀ output,
        firstMatching expected actual bindings output ↔ secondMatching expected actual bindings output) :
    TypeCastBatchRel space atom expected bindings results (lookup := lookup) (matching := firstMatching) ↔
      TypeCastBatchRel space atom expected bindings results (lookup := lookup) (matching := secondMatching) :=
  ⟨fun source => source.change_matching same,
    fun source => source.change_matching (fun types queried actual present output =>
      (same types queried actual present output).symm)⟩

/-- Every complete finite type query has a completed cast under any local
matching policy. This is source existence, not an executable choice of a
particular unifier or a termination assumption about recursive evaluation. -/
theorem TypeCastBatchRel.total
    {space : Space} {atom expected : Atom} {bindings : Bindings}
    {lookup : TypeLookupRel} {types : List Atom}
    {matching : Atom → Atom → Bindings → Bindings → Prop}
    (queried : lookup bindings atom expected types) :
    ∃ results, TypeCastBatchRel space atom expected bindings results
      (lookup := lookup) (matching := matching) := by
  classical
  have scan : ∀ items : List Atom,
      (∀ actual ∈ items, ∀ output, ¬matching expected actual bindings output) ∨
      ∃ earlier actual later output, items = earlier ++ actual :: later ∧
        (∀ prior ∈ earlier, ∀ candidate, ¬matching expected prior bindings candidate) ∧
        matching expected actual bindings output := by
    intro items
    induction items with
    | nil => exact Or.inl (by intro actual present; cases present)
    | cons actual rest ih =>
        by_cases available : ∃ output, matching expected actual bindings output
        · obtain ⟨output,matched⟩ := available
          exact Or.inr ⟨[],actual,rest,output,rfl,by simp,matched⟩
        · rcases ih with rejected | ⟨earlier,candidate,later,output,selected,rejected,matched⟩
          · left
            intro value present output matched
            rcases List.mem_cons.mp present with rfl | present
            · exact available ⟨output,matched⟩
            · exact rejected value present output matched
          · right
            refine ⟨actual :: earlier,candidate,later,output,?_,?_,matched⟩
            · simpa only [List.cons_append] using congrArg (List.cons actual) selected
            · intro value present output matched
              rcases List.mem_cons.mp present with rfl | present
              · exact available ⟨output,matched⟩
              · exact rejected value present output matched
  rcases scan types with rejected | ⟨earlier,actual,later,output,selected,rejected,matched⟩
  · exact ⟨_,.failure queried rejected⟩
  · exact ⟨_,.success queried selected rejected matched⟩

/-! ## Function applicability -/

/-- A published function type `(-> arg₁ ... argₙ result)`.  The published
schema permits `n = 0`, represented by `(-> result)`; the bare `(->)` has no
return type and therefore has no witness. -/
def FunctionTypeRel (functionType : Atom) (argumentTypes : List Atom)
    (returnType : Atom) : Prop :=
  functionType =
    .expression (.symbol "->" :: (argumentTypes ++ [returnType]))

/-- The argument and return projections of one published arrow are unique.
This keeps arity and policy reasoning at the declarative boundary rather than
reconstructing list facts in every evaluator correspondence proof. -/
theorem FunctionTypeRel.unique
    {functionType : Atom}
    {leftArguments rightArguments : List Atom}
    {leftReturn rightReturn : Atom}
    (left : FunctionTypeRel functionType leftArguments leftReturn)
    (right : FunctionTypeRel functionType rightArguments rightReturn) :
    leftArguments = rightArguments ∧ leftReturn = rightReturn := by
  have parts : leftArguments ++ [leftReturn] =
      rightArguments ++ [rightReturn] := by
    rw [FunctionTypeRel] at left right
    exact List.cons.inj (Atom.expression.inj (left.symm.trans right)) |>.2
  constructor
  · have dropped := congrArg List.dropLast parts
    simpa [List.dropLast_concat] using dropped
  · have last := congrArg List.getLast? parts
    simpa [List.getLast?_concat] using last

/-- A successful left-to-right argument check.  Each step selects one actual
type and threads the bindings produced by declarative type matching. -/
inductive ArgumentsApplicableRel (space : Space) :
    List Atom → List Atom → Bindings → Bindings →
      (lookup : TypeLookupRel := rawTypeLookupRel space) → Prop where
  | nil (bindings : Bindings) :
      ArgumentsApplicableRel space (lookup := lookup) [] [] bindings bindings
  | cons {argument expectedType actualType : Atom}
      {arguments expectedTypes : List Atom}
      {bindings next output : Bindings} :
      TypeAtRel lookup bindings argument expectedType actualType →
      TypeMatchRel expectedType actualType bindings next →
      ArgumentsApplicableRel space (lookup := lookup) arguments expectedTypes next output →
      ArgumentsApplicableRel space (lookup := lookup)
        (argument :: arguments) (expectedType :: expectedTypes)
        bindings output

/-- One complete successful applicability path, including the return-type
check. -/
inductive ApplicationSuccessRel (space : Space) :
    Atom → Atom → Atom → Bindings → Bindings →
      (lookup : TypeLookupRel := rawTypeLookupRel space) → Prop where
  | mk {expression functionType expectedType operator returnType : Atom}
      {arguments argumentTypes : List Atom}
      {bindings afterArguments output : Bindings} :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel functionType argumentTypes returnType →
      ArgumentsApplicableRel space (lookup := lookup) arguments argumentTypes
        bindings afterArguments →
      TypeMatchRel expectedType returnType afterArguments output →
      ApplicationSuccessRel space (lookup := lookup) expression functionType expectedType
        bindings output

/-- One observable outcome of function-type applicability. -/
inductive ApplicabilityOutcome where
  | success (bindings : Bindings)
  | error (errorAtom : Atom)
  deriving Repr

/-- Declarative `check_if_function_type_is_applicable`.  Error constructors
carry the same errors as the pseudocode and require absence of any complete
success whenever another type path could otherwise mask the error. -/
inductive ApplicabilityRel (space : Space) :
    Atom → Atom → Atom → Bindings → ApplicabilityOutcome →
      (lookup : TypeLookupRel := rawTypeLookupRel space) → Prop where
  | success {expression functionType expectedType : Atom}
      {bindings output : Bindings} :
      ApplicationSuccessRel space (lookup := lookup) expression functionType expectedType
        bindings output →
      ApplicabilityRel space (lookup := lookup) expression functionType expectedType bindings
        (.success output)
  | wrongArity {expression functionType expectedType operator returnType : Atom}
      {arguments argumentTypes : List Atom} {bindings : Bindings} :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel functionType argumentTypes returnType →
      arguments.length ≠ argumentTypes.length →
      ApplicabilityRel space (lookup := lookup) expression functionType expectedType bindings
        (.error (mkError expression .incorrectNumberOfArguments))
  | badArgument {expression functionType expectedType operator returnType : Atom}
      {argumentsBefore argumentsAfter : List Atom}
      {typesBefore typesAfter : List Atom}
      {badArgument expectedArgument actualType : Atom}
      {bindings beforeBad : Bindings} :
      expression = .expression
        (operator :: (argumentsBefore ++ badArgument :: argumentsAfter)) →
      FunctionTypeRel functionType
        (typesBefore ++ expectedArgument :: typesAfter) returnType →
      argumentsAfter.length = typesAfter.length →
      ArgumentsApplicableRel space (lookup := lookup) argumentsBefore typesBefore
        bindings beforeBad →
      TypeAtRel lookup beforeBad badArgument expectedArgument actualType →
      (∀ candidate,
        ¬TypeMatchRel expectedArgument actualType beforeBad candidate) →
      (∀ output,
        ¬ApplicationSuccessRel space (lookup := lookup) expression functionType expectedType
          bindings output) →
      ApplicabilityRel space (lookup := lookup) expression functionType expectedType bindings
        (.error (mkError expression
          -- The pseudocode prints `idx - 1` despite iterating expression
          -- positions from one.  The reference evaluator and the documented
          -- `BadArgType` interface reports one-based argument positions.
          (.badArgType (argumentsBefore.length + 1)
            expectedArgument actualType)))
  | badReturn {expression functionType expectedType operator returnType : Atom}
      {arguments argumentTypes : List Atom}
      {bindings afterArguments : Bindings} :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel functionType argumentTypes returnType →
      ArgumentsApplicableRel space (lookup := lookup) arguments argumentTypes
        bindings afterArguments →
      (∀ candidate,
        ¬TypeMatchRel expectedType returnType afterArguments candidate) →
      (∀ output,
        ¬ApplicationSuccessRel space (lookup := lookup) expression functionType expectedType
          bindings output) →
      ApplicabilityRel space (lookup := lookup) expression functionType expectedType bindings
        (.error (mkError expression (.badType expectedType returnType)))

/-! ## Boundary examples -/

private def declaredIntSpace : Space :=
  Space.ofList [
    .expression [.symbol ":", .symbol "x", .symbol "Int"]]

/-- Positive lookup: a direct type assignment is visible. -/
example : TypeOfRel declaredIntSpace (.symbol "x") (.symbol "Int") := by
  refine ⟨[.symbol "Int"], ?_, by simp⟩
  apply StorageTypesRel.symbolKnown
  · change AnnotationTypesRel (.symbol "x")
      [.expression [.symbol ":", .symbol "x", .symbol "Int"]]
      [.symbol "Int"]
    exact .hit .nil
  · simp

/-- Negative lookup: a variable with no intrinsic type is not assigned `Int`.-/
theorem variable_not_int_type :
    ¬TypeOfRel Space.empty (.var "x") (.symbol "Int") := by
  rintro ⟨types, htypes, hmem⟩
  cases htypes
  simp [Atom.undefinedType] at hmem

private theorem symbolTypeMatchEmpty (name : String)
    (hUndefined : name ≠ "%Undefined%") (hAtom : name ≠ "Atom") :
    TypeMatchRel (.symbol name) (.symbol name)
      Bindings.empty Bindings.empty := by
  apply TypeMatchRel.structural
  · simpa [Atom.undefinedType] using hUndefined
  · simpa [Atom.atomType] using hAtom
  · simpa [Atom.undefinedType] using hUndefined
  · simpa [Atom.atomType] using hAtom
  · exact MatchRel.symSym name semanticLoopFree_empty
  · exact MergeRel.mk
      (by simp [constraints, Bindings.empty])
      MergeConstraintsRel.nil

/-- Positive cast: the first declared type matches the expected type. -/
example : TypeCastRel declaredIntSpace (.symbol "x") (.symbol "Int")
    Bindings.empty (.symbol "x", Bindings.empty) := by
  apply TypeCastRel.success
      (types := [.symbol "Int"]) (earlierTypes := []) (laterTypes := [])
      (actualType := .symbol "Int")
  · apply StorageTypesRel.symbolKnown
    · change AnnotationTypesRel (.symbol "x")
        [.expression [.symbol ":", .symbol "x", .symbol "Int"]]
        [.symbol "Int"]
      exact .hit .nil
    · simp
  · rfl
  · simp
  · exact symbolTypeMatchEmpty "Int" (by decide) (by decide)

private theorem boolIntTypeMismatch (candidate : Bindings) :
    ¬TypeMatchRel (.symbol "Bool") (.symbol "Int")
      Bindings.empty candidate := by
  intro hmatch
  obtain ⟨matched, hspec, _⟩ := hmatch.structural_of_nonWildcard
    (by decide) (by decide) (by decide) (by decide)
  exact symbol_mismatch_not_match (by decide) matched hspec

/-- Negative cast outcome: an incompatible declared type produces the
published `BadType` error. -/
example : TypeCastRel declaredIntSpace (.symbol "x") (.symbol "Bool")
    Bindings.empty
    (mkError (.symbol "x") (.badType (.symbol "Bool") (.symbol "Int")),
      Bindings.empty) := by
  apply TypeCastRel.failure (types := [.symbol "Int"])
      (actualType := .symbol "Int")
  · apply StorageTypesRel.symbolKnown
    · change AnnotationTypesRel (.symbol "x")
        [.expression [.symbol ":", .symbol "x", .symbol "Int"]]
        [.symbol "Int"]
      exact .hit .nil
    · simp
  · simp
  · intro candidateType hmem candidate
    simp only [List.mem_singleton] at hmem
    subst candidateType
    exact boolIntTypeMismatch candidate

private def binaryNumberType : Atom :=
  .expression [
    .symbol "->", .symbol "Number", .symbol "Number", .symbol "Number"]

private def binaryNumberCall : Atom :=
  .expression [
    .symbol "add", .grounded (.int 1), .grounded (.int 2)]

private theorem groundedNumberType (value : Int) :
    TypeOfRel Space.empty (.grounded (.int value)) (.symbol "Number") := by
  refine ⟨[.symbol "Number"], ?_, by simp⟩
  exact StorageTypesRel.groundedKnown (IntrinsicGroundedTypeRel.int value)
    (by simp [Atom.undefinedType])

/-- Positive applicability: both numeric arguments and the return type accept
a complete binding-threading path. -/
example : ApplicabilityRel Space.empty binaryNumberCall binaryNumberType
    Atom.undefinedType Bindings.empty (.success Bindings.empty) := by
  apply ApplicabilityRel.success
  apply ApplicationSuccessRel.mk
      (operator := .symbol "add")
      (arguments := [.grounded (.int 1), .grounded (.int 2)])
      (argumentTypes := [.symbol "Number", .symbol "Number"])
      (returnType := .symbol "Number")
      (afterArguments := Bindings.empty)
  · rfl
  · rfl
  · exact ArgumentsApplicableRel.cons (groundedNumberType 1)
      (symbolTypeMatchEmpty "Number" (by decide) (by decide))
      (ArgumentsApplicableRel.cons (groundedNumberType 2)
        (symbolTypeMatchEmpty "Number" (by decide) (by decide))
        (ArgumentsApplicableRel.nil Bindings.empty))
  · exact TypeMatchRel.undefinedLeft (.symbol "Number") Bindings.empty

/-- Negative applicability outcome: a unary call cannot inhabit a binary
function type and produces `IncorrectNumberOfArguments`. -/
theorem binary_function_rejects_unary_arity : ApplicabilityRel Space.empty
    (.expression [.symbol "add", .grounded (.int 1)]) binaryNumberType
    Atom.undefinedType Bindings.empty
    (.error (mkError
      (.expression [.symbol "add", .grounded (.int 1)])
      .incorrectNumberOfArguments)) := by
  apply ApplicabilityRel.wrongArity
      (operator := .symbol "add")
      (arguments := [.grounded (.int 1)])
      (argumentTypes := [.symbol "Number", .symbol "Number"])
      (returnType := .symbol "Number")
  · rfl
  · rfl
  · decide

/-- The published arrow schema admits the nullary case `(-> R)`. -/
theorem nullary_function_type :
    FunctionTypeRel
      (.expression [.symbol "->", .symbol "R"]) [] (.symbol "R") := by
  rfl

/-- A nullary call follows the ordinary successful applicability path. -/
theorem nullary_function_applicable :
    ApplicabilityRel Space.empty
      (.expression [.symbol "constant"])
      (.expression [.symbol "->", .symbol "R"])
      Atom.undefinedType Bindings.empty (.success Bindings.empty) := by
  apply ApplicabilityRel.success
  apply ApplicationSuccessRel.mk
      (operator := .symbol "constant")
      (arguments := [])
      (argumentTypes := [])
      (returnType := .symbol "R")
      (afterArguments := Bindings.empty)
  · rfl
  · exact nullary_function_type
  · exact ArgumentsApplicableRel.nil Bindings.empty
  · exact TypeMatchRel.undefinedLeft (.symbol "R") Bindings.empty

/-- The bare arrow has no return component and remains malformed. -/
theorem bare_arrow_not_function_type :
    ¬∃ argumentTypes returnType,
      FunctionTypeRel (.expression [.symbol "->"])
        argumentTypes returnType := by
  rintro ⟨argumentTypes, returnType, hfunction⟩
  simp [FunctionTypeRel] at hfunction

end Mettapedia.Languages.MeTTa.HE.Spec.Type
