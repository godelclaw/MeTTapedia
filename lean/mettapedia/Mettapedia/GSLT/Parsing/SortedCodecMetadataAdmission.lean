import Mettapedia.GSLT.Parsing.CanonicalProjectionSExprAdapter

/-!
# Finite source metadata for a sorted canonical codec

Source categories, logical sorts, and production occurrences are separate
carriers. The finite checker validates their references, projected shapes, and
ordered arguments. Schema declarations are then compiled from the accepted
source rows; neither category suffixes nor constructor spelling infer a sort.

Occurrence and origin fields survive lowering. Origins are uninterpreted
evidence labels here: their presence does not prove module provenance. The
schema is structural. Source derivability, directed list cardinality, lexical
priority, auxiliary-event erasure, and native parser adequacy remain distinct
obligations. Historical metta-venus and other source dialects can provide these
rows without being identified with one another.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SortedCodecMetadataAdmission

open SortedCanonicalSExprCodec
open CanonicalGrammar (CanonicalTerm Sym Production)
open CanonicalProjectionSExprAdapter (Layout)

inductive SortKind where
  | token (representation : TokenRepresentation) (tokenHead : String)
  | list (elementSort listKey : String)
  | constructors
  deriving DecidableEq, Repr

structure SortRow where
  name : String
  shape : SortKind
  deriving DecidableEq, Repr

inductive CategoryKind where
  | rule
  | token
  | erased
  deriving DecidableEq, Repr

structure SourceCategory where
  name : String
  logicalSort : Option String
  kind : CategoryKind
  deriving DecidableEq, Repr

inductive Slot where
  | argument (category : String)
  | fixed (terminal : String) (surface : Option String)
  | erased (category : String)
  deriving DecidableEq, Repr

inductive Projection where
  | constructor (head : String)
  | transparent
  | listEmpty
  | listSingleton
  | listCons (left : Bool)
  | erased
  deriving DecidableEq, Repr

structure ProductionRow where
  occurrence : Nat
  origin : Option String
  resultCategory : String
  rhs : List Slot
  projection : Projection
  deriving DecidableEq, Repr

structure Metadata where
  sorts : List SortRow
  categories : List SourceCategory
  productions : List ProductionRow
  deriving DecidableEq, Repr

/-- Exact finite lookup. Uniqueness is checked separately, so the theorem about
this function cannot turn a duplicate declaration into a first-row policy. -/
def lookup? {α : Type} (key : α → String) (rows : List α) (name : String) : Option α :=
  rows.find? (fun row => key row == name)

theorem lookup_sound {α : Type} (key : α → String) (rows : List α)
    (name : String) (row : α) (found : lookup? key rows name = some row) :
    row ∈ rows ∧ key row = name := by
  have selected : (fun entry => key entry == name) row = true :=
    List.find?_some (p := fun entry => key entry == name) (a := row) found
  exact ⟨List.mem_of_find?_eq_some found, beq_iff_eq.mp selected⟩

theorem lookup_complete {α : Type} (key : α → String) (rows : List α)
    (unique : (rows.map key).Nodup) (name : String) (row : α)
    (member : row ∈ rows) (named : key row = name) :
    lookup? key rows name = some row := by
  induction rows with
  | nil => simp at member
  | cons first rest ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases List.mem_cons.mp member with same | member
      · subst row
        simp [lookup?, named]
      · have different : key first ≠ name := by
          intro same
          apply unique.1
          exact List.mem_map.mpr ⟨row, member, named.trans same.symm⟩
        simpa [lookup?, different] using ih unique.2 member

theorem declared_iff_lookup {α : Type} (key : α → String) (rows : List α)
    (unique : (rows.map key).Nodup) (name : String) (predicate : α → Prop) :
    (∃ row ∈ rows, key row = name ∧ predicate row) ↔
      ∃ row, lookup? key rows name = some row ∧ predicate row := by
  constructor
  · rintro ⟨row, member, named, property⟩
    exact ⟨row, lookup_complete key rows unique name row member named, property⟩
  · rintro ⟨row, found, property⟩
    have info := lookup_sound key rows name row found
    exact ⟨row, info.1, info.2, property⟩

def sort? (metadata : Metadata) : String → Option SortRow :=
  lookup? SortRow.name metadata.sorts

def category? (metadata : Metadata) : String → Option SourceCategory :=
  lookup? SourceCategory.name metadata.categories

def argumentNames (slots : List Slot) : List String :=
  slots.filterMap fun
    | .argument category => some category
    | _ => none

def argumentSort? (metadata : Metadata) (name : String) : Option String := do
  let row ← category? metadata name
  if row.kind = .erased then none else row.logicalSort

def argumentSorts? (metadata : Metadata) : List String → Option (List String)
  | [] => some []
  | name :: names => do
      return (← argumentSort? metadata name) :: (← argumentSorts? metadata names)

/-- A successful ordered lowering has one logical sort per source argument.
The relation permits repeated categories and retains their positions. -/
inductive ArgumentSorts (metadata : Metadata) : List String → List String → Prop where
  | nil : ArgumentSorts metadata [] []
  | cons (name sort : String) (names sorts : List String)
      (row : SourceCategory) (member : row ∈ metadata.categories)
      (named : row.name = name) (visible : row.kind ≠ .erased)
      (logical : row.logicalSort = some sort)
      (rest : ArgumentSorts metadata names sorts) :
      ArgumentSorts metadata (name :: names) (sort :: sorts)

theorem argumentSort_iff (metadata : Metadata)
    (unique : (metadata.categories.map SourceCategory.name).Nodup)
    (name sort : String) :
    argumentSort? metadata name = some sort ↔
      ∃ row ∈ metadata.categories, row.name = name ∧ row.kind ≠ .erased ∧
        row.logicalSort = some sort := by
  constructor
  · intro found
    cases chosen : category? metadata name with
    | none => simp [argumentSort?, chosen] at found
    | some row =>
        have info := lookup_sound SourceCategory.name metadata.categories name row chosen
        by_cases erased : row.kind = .erased
        · simp [argumentSort?, chosen, erased] at found
        · exact ⟨row, info.1, info.2, erased, by simpa [argumentSort?, chosen, erased] using found⟩
  · rintro ⟨row, member, named, visible, logical⟩
    have chosen := lookup_complete SourceCategory.name metadata.categories unique name row member named
    simpa [argumentSort?, category?, chosen, visible] using logical

theorem argumentSorts_iff (metadata : Metadata)
    (unique : (metadata.categories.map SourceCategory.name).Nodup)
    (names sorts : List String) :
    argumentSorts? metadata names = some sorts ↔ ArgumentSorts metadata names sorts := by
  induction names generalizing sorts with
  | nil =>
      cases sorts with
      | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
      | cons sort sorts =>
          constructor
          · simp [argumentSorts?]
          · intro impossible; cases impossible
  | cons name names ih =>
      constructor
      · intro found
        cases first : argumentSort? metadata name with
        | none => simp [argumentSorts?, first] at found
        | some sort =>
            cases rest : argumentSorts? metadata names with
            | none => simp [argumentSorts?, first, rest] at found
            | some tail =>
                have same : sort :: tail = sorts := by simpa [argumentSorts?, first, rest] using found
                subst sorts
                obtain ⟨row, member, named, visible, logical⟩ :=
                  (argumentSort_iff metadata unique name sort).mp first
                exact .cons name sort names tail row member named visible logical (ih tail |>.mp rest)
      · intro relation
        cases relation with
        | cons _ sort _ tail row member named visible logical relation =>
            have first := (argumentSort_iff metadata unique name sort).mpr
              ⟨row, member, named, visible, logical⟩
            simp [argumentSorts?, first, (ih tail).mpr relation]

theorem argumentSorts_length (metadata : Metadata) {names sorts : List String}
    (relation : ArgumentSorts metadata names sorts) : names.length = sorts.length := by
  induction relation with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ _ _ ih => simpa using congrArg Nat.succ ih

def hasSort (metadata : Metadata) (name : String) : Bool :=
  metadata.sorts.any (fun row => row.name == name)

def sortCheck (metadata : Metadata) (row : SortRow) : Bool :=
  match row.shape with
  | .list elementSort _ => hasSort metadata elementSort
  | _ => true

def categoryCheck (metadata : Metadata) (row : SourceCategory) : Bool :=
  match row.kind, row.logicalSort with
  | .erased, none => true
  | .rule, some sort => hasSort metadata sort
  | .token, some sort =>
      match sort? metadata sort with
      | some ⟨_, .token _ head⟩ => head == row.name
      | _ => false
  | _, _ => false

def slotCheck (metadata : Metadata) : Slot → Bool
  | .fixed _ _ => true
  | .argument name =>
      match category? metadata name with
      | some row => row.kind != .erased && row.logicalSort.isSome
      | none => false
  | .erased name =>
      match category? metadata name with
      | some row => row.kind == .erased && row.logicalSort.isNone
      | none => false

def projectionCheck (profile : Notation) (result : String)
    (sorts : List String) (shape : SortKind) : Projection → Bool
  | .constructor head =>
      shape == .constructors && head != profile.listName && head != profile.symbolName
  | .transparent => sorts == [result]
  | .listEmpty =>
      match shape with | .list _ _ => sorts.isEmpty | _ => false
  | .listSingleton =>
      match shape with | .list element _ => sorts == [element] | _ => false
  | .listCons left =>
      match shape with
      | .list element _ =>
          if left then sorts == [result, element] else sorts == [element, result]
      | _ => false
  | .erased => false

/-- Physical recursion of a list macro remains distinct from its logical sort.
Transparent aliases may share a sort; they do not change the macro's spine. -/
def listSpineCheck (row : ProductionRow) : Bool :=
  match row.projection with
  | .listCons true =>
      match argumentNames row.rhs with
      | [spine, _] => spine == row.resultCategory
      | _ => false
  | .listCons false =>
      match argumentNames row.rhs with
      | [_, spine] => spine == row.resultCategory
      | _ => false
  | _ => true

def productionCheck (metadata : Metadata) (profile : Notation) (row : ProductionRow) : Bool :=
  row.rhs.all (slotCheck metadata) && listSpineCheck row &&
    match category? metadata row.resultCategory with
    | none => false
    | some category =>
        match category.kind, category.logicalSort with
        | .erased, none => row.projection == .erased && (argumentNames row.rhs).isEmpty
        | .rule, some result =>
            match sort? metadata result, argumentSorts? metadata (argumentNames row.rhs) with
            | some sortRow, some sorts =>
                projectionCheck profile result sorts sortRow.shape row.projection
            | _, _ => false
        | _, _ => false

def constructorKey? (metadata : Metadata) (row : ProductionRow) : Option (String × String) := do
  let .constructor head := row.projection | none
  let category ← category? metadata row.resultCategory
  let sort ← category.logicalSort
  pure (sort, head)

def uniqueConstructors (metadata : Metadata) : Bool :=
  decide ((metadata.productions.filterMap (constructorKey? metadata)).Nodup)

/-- The executable metadata gate. It rejects all bad rows rather than silently
filtering them while building the structural schema. -/
def check (metadata : Metadata) (profile : Notation) : Bool :=
  decide ((metadata.sorts.map SortRow.name).Nodup) &&
  decide ((metadata.categories.map SourceCategory.name).Nodup) &&
  decide ((metadata.productions.map ProductionRow.occurrence).Nodup) &&
  metadata.sorts.all (sortCheck metadata) &&
  metadata.categories.all (categoryCheck metadata) &&
  metadata.productions.all (productionCheck metadata profile) &&
  uniqueConstructors metadata

def SortContract (metadata : Metadata) (row : SortRow) : Prop :=
  match row.shape with
  | .list elementSort _ => ∃ element ∈ metadata.sorts, element.name = elementSort
  | _ => True

def CategoryContract (metadata : Metadata) (row : SourceCategory) : Prop :=
  match row.kind, row.logicalSort with
  | .erased, none => True
  | .rule, some sort => ∃ declaration ∈ metadata.sorts, declaration.name = sort
  | .token, some sort =>
      ∃ declaration ∈ metadata.sorts, declaration.name = sort ∧
        match declaration.shape with
        | .token _ head => head = row.name
        | _ => False
  | _, _ => False

def SlotContract (metadata : Metadata) : Slot → Prop
  | .fixed _ _ => True
  | .argument name =>
      ∃ row ∈ metadata.categories, row.name = name ∧ row.kind ≠ .erased ∧
        row.logicalSort ≠ none
  | .erased name =>
      ∃ row ∈ metadata.categories, row.name = name ∧ row.kind = .erased ∧
        row.logicalSort = none

def ProjectionContract (profile : Notation) (result : String)
    (sorts : List String) (shape : SortKind) : Projection → Prop
  | .constructor head =>
      shape = .constructors ∧ head ≠ profile.listName ∧ head ≠ profile.symbolName
  | .transparent => sorts = [result]
  | .listEmpty =>
      match shape with | .list _ _ => sorts = [] | _ => False
  | .listSingleton =>
      match shape with | .list element _ => sorts = [element] | _ => False
  | .listCons left =>
      match shape with
      | .list element _ =>
          if left then sorts = [result, element] else sorts = [element, result]
      | _ => False
  | .erased => False

def ListSpineContract (row : ProductionRow) : Prop :=
  match row.projection with
  | .listCons true =>
      match argumentNames row.rhs with
      | [spine, _] => spine = row.resultCategory
      | _ => False
  | .listCons false =>
      match argumentNames row.rhs with
      | [_, spine] => spine = row.resultCategory
      | _ => False
  | _ => True

/-- Independent row contract: all references name actual declarations; argument
sorts are related in order; transparent and list projections have their exact
signatures. It does not identify structural sorting with grammar derivability. -/
def ProductionContract (metadata : Metadata) (profile : Notation) (row : ProductionRow) : Prop :=
  (∀ slot ∈ row.rhs, SlotContract metadata slot) ∧ ListSpineContract row ∧
    ∃ category ∈ metadata.categories, category.name = row.resultCategory ∧
      match category.kind, category.logicalSort with
      | .erased, none => row.projection = .erased ∧ argumentNames row.rhs = []
      | .rule, some result =>
          ∃ declaration ∈ metadata.sorts, declaration.name = result ∧
            ∃ sorts, ArgumentSorts metadata (argumentNames row.rhs) sorts ∧
              ProjectionContract profile result sorts declaration.shape row.projection
      | _, _ => False

structure Valid (metadata : Metadata) (profile : Notation) : Prop where
  uniqueSorts : (metadata.sorts.map SortRow.name).Nodup
  uniqueCategories : (metadata.categories.map SourceCategory.name).Nodup
  uniqueOccurrences : (metadata.productions.map ProductionRow.occurrence).Nodup
  sorts : ∀ row ∈ metadata.sorts, SortContract metadata row
  categories : ∀ row ∈ metadata.categories, CategoryContract metadata row
  productions : ∀ row ∈ metadata.productions, ProductionContract metadata profile row
  uniqueHeads : (metadata.productions.filterMap (constructorKey? metadata)).Nodup

theorem sortCheck_iff (metadata : Metadata) (row : SortRow) :
    sortCheck metadata row = true ↔ SortContract metadata row := by
  cases shape : row.shape <;> simp [sortCheck, SortContract, shape, hasSort, List.any_eq_true]

theorem categoryCheck_iff (metadata : Metadata)
    (unique : (metadata.sorts.map SortRow.name).Nodup) (row : SourceCategory) :
    categoryCheck metadata row = true ↔ CategoryContract metadata row := by
  cases kind : row.kind with
  | rule =>
      cases logical : row.logicalSort <;>
        simp [categoryCheck, CategoryContract, kind, logical, hasSort, List.any_eq_true]
  | erased =>
      cases logical : row.logicalSort <;> simp [categoryCheck, CategoryContract, kind, logical]
  | token =>
      cases logical : row.logicalSort with
      | none => simp [categoryCheck, CategoryContract, kind, logical]
      | some sort =>
          simp only [categoryCheck, CategoryContract, kind, logical]
          constructor
          · intro checked
            cases chosen : sort? metadata sort with
            | none => simp [chosen] at checked
            | some declaration =>
                have info := lookup_sound SortRow.name metadata.sorts sort declaration chosen
                refine ⟨declaration, info.1, info.2, ?_⟩
                cases declaration with
                | mk name shape =>
                    cases shape <;> simp [chosen] at checked ⊢
                    exact checked
          · rintro ⟨declaration, member, named, shaped⟩
            have chosen := lookup_complete SortRow.name metadata.sorts unique sort declaration member named
            cases declaration with
            | mk name shape =>
                cases shape <;> simp at shaped
                simpa [sort?, chosen] using shaped

theorem slotCheck_iff (metadata : Metadata)
    (unique : (metadata.categories.map SourceCategory.name).Nodup) (slot : Slot) :
    slotCheck metadata slot = true ↔ SlotContract metadata slot := by
  cases slot with
  | fixed _ _ => simp [slotCheck, SlotContract]
  | argument name =>
      constructor
      · intro checked
        cases chosen : category? metadata name with
        | none => simp [slotCheck, chosen] at checked
        | some row =>
            have info := lookup_sound SourceCategory.name metadata.categories name row chosen
            refine ⟨row, info.1, info.2, ?_⟩
            cases logical : row.logicalSort with
            | none => simp [slotCheck, chosen, logical] at checked
            | some sort => simpa [slotCheck, chosen, logical] using checked
      · rintro ⟨row, member, named, visible, logical⟩
        have chosen := lookup_complete SourceCategory.name metadata.categories unique name row member named
        cases actual : row.logicalSort <;> simp [actual] at logical
        simp [slotCheck, category?, chosen, visible, actual]
  | erased name =>
      constructor
      · intro checked
        cases chosen : category? metadata name with
        | none => simp [slotCheck, chosen] at checked
        | some row =>
            have info := lookup_sound SourceCategory.name metadata.categories name row chosen
            refine ⟨row, info.1, info.2, ?_⟩
            cases logical : row.logicalSort with
            | none => simpa [slotCheck, chosen, logical] using checked
            | some sort => simp [slotCheck, chosen, logical] at checked
      · rintro ⟨row, member, named, erased, logical⟩
        have chosen := lookup_complete SourceCategory.name metadata.categories unique name row member named
        simp [slotCheck, category?, chosen, erased, logical]

theorem projectionCheck_iff (profile : Notation) (result : String)
    (sorts : List String) (shape : SortKind) (projection : Projection) :
    projectionCheck profile result sorts shape projection = true ↔
      ProjectionContract profile result sorts shape projection := by
  cases projection <;> cases shape <;> simp [projectionCheck, ProjectionContract]

theorem listSpineCheck_iff (row : ProductionRow) :
    listSpineCheck row = true ↔ ListSpineContract row := by
  cases projection : row.projection with
  | constructor _ => simp [listSpineCheck, ListSpineContract, projection]
  | transparent => simp [listSpineCheck, ListSpineContract, projection]
  | listEmpty => simp [listSpineCheck, ListSpineContract, projection]
  | listSingleton => simp [listSpineCheck, ListSpineContract, projection]
  | erased => simp [listSpineCheck, ListSpineContract, projection]
  | listCons left =>
      simp only [listSpineCheck, ListSpineContract, projection]
      cases left <;> cases argumentNames row.rhs with
      | nil => simp
      | cons first rest =>
          cases rest with
          | nil => simp
          | cons second tail => cases tail <;> simp

theorem productionCheck_iff (metadata : Metadata) (profile : Notation)
    (uniqueSorts : (metadata.sorts.map SortRow.name).Nodup)
    (uniqueCategories : (metadata.categories.map SourceCategory.name).Nodup)
    (row : ProductionRow) :
    productionCheck metadata profile row = true ↔ ProductionContract metadata profile row := by
  unfold productionCheck ProductionContract
  rw [declared_iff_lookup SourceCategory.name metadata.categories uniqueCategories]
  simp only [Bool.and_eq_true, List.all_eq_true, slotCheck_iff metadata uniqueCategories,
    listSpineCheck_iff, and_assoc]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  cases chosen : category? metadata row.resultCategory with
  | none =>
      change lookup? SourceCategory.name metadata.categories row.resultCategory = none at chosen
      simp [chosen]
  | some category =>
      simp only [category?] at chosen
      simp only [chosen, Option.some.injEq, exists_eq_left']
      cases kind : category.kind with
      | token => cases logical : category.logicalSort <;> simp
      | erased => cases logical : category.logicalSort <;> simp
      | rule =>
          cases logical : category.logicalSort with
          | none => simp
          | some result =>
              dsimp only
              rw [declared_iff_lookup SortRow.name metadata.sorts uniqueSorts]
              cases found : sort? metadata result with
              | none =>
                  change lookup? SortRow.name metadata.sorts result = none at found
                  simp [found]
              | some declaration =>
                  simp only [sort?] at found
                  simp only [found, Option.some.injEq, exists_eq_left']
                  cases arguments : argumentSorts? metadata (argumentNames row.rhs) with
                  | none =>
                      have absent : ∀ sorts, ¬ ArgumentSorts metadata (argumentNames row.rhs) sorts := by
                        intro sorts relation
                        have lowered := (argumentSorts_iff metadata uniqueCategories _ sorts).mpr relation
                        simp [arguments] at lowered
                      simp [absent]
                  | some sorts =>
                      have exactSorts : ∀ other,
                          ArgumentSorts metadata (argumentNames row.rhs) other ↔ sorts = other := by
                        intro other
                        rw [← argumentSorts_iff metadata uniqueCategories, arguments]
                        simp
                      simp only [exactSorts, exists_eq_left']
                      exact projectionCheck_iff profile result sorts declaration.shape row.projection

/-- Soundness and completeness are relative to the concrete finite contract,
not to a dialect name or a digest of exported rows. -/
theorem check_iff (metadata : Metadata) (profile : Notation) :
    check metadata profile = true ↔ Valid metadata profile := by
  simp only [check, uniqueConstructors, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨uniqueSorts, uniqueCategories⟩, uniqueOccurrences⟩, sorts⟩, categories⟩,
      productions⟩, heads⟩
    refine ⟨uniqueSorts, uniqueCategories, uniqueOccurrences, ?_, ?_, ?_, heads⟩
    · intro row member
      exact (sortCheck_iff metadata row).mp (sorts row member)
    · intro row member
      exact (categoryCheck_iff metadata uniqueSorts row).mp (categories row member)
    · intro row member
      exact (productionCheck_iff metadata profile uniqueSorts uniqueCategories row).mp
        (productions row member)
  · intro valid
    refine ⟨⟨⟨⟨⟨⟨valid.uniqueSorts, valid.uniqueCategories⟩, valid.uniqueOccurrences⟩, ?_⟩, ?_⟩,
      ?_⟩, valid.uniqueHeads⟩
    · intro row member
      exact (sortCheck_iff metadata row).mpr (valid.sorts row member)
    · intro row member
      exact (categoryCheck_iff metadata valid.uniqueSorts row).mpr (valid.categories row member)
    · intro row member
      exact (productionCheck_iff metadata profile valid.uniqueSorts valid.uniqueCategories row).mpr
        (valid.productions row member)

structure LoweredConstructor where
  source : ProductionRow
  resultSort : String
  declaration : Constructor
  deriving DecidableEq, Repr

/-- Only constructor rows become constructor declarations. The metadata gate
is applied before the complete family is exposed to a codec consumer. -/
def constructorRow? (metadata : Metadata) (row : ProductionRow) : Option LoweredConstructor := do
  let .constructor head := row.projection | none
  let category ← category? metadata row.resultCategory
  if category.kind ≠ .rule then none else do
    let result ← category.logicalSort
    let arguments ← argumentSorts? metadata (argumentNames row.rhs)
    pure ⟨row, result, ⟨head, arguments⟩⟩

def LowersConstructor (metadata : Metadata) (row : ProductionRow)
    (lowered : LoweredConstructor) : Prop :=
  lowered.source = row ∧ row.projection = .constructor lowered.declaration.name ∧
    (∃ category ∈ metadata.categories, category.name = row.resultCategory ∧
      category.kind = .rule ∧ category.logicalSort = some lowered.resultSort) ∧
    ArgumentSorts metadata (argumentNames row.rhs) lowered.declaration.arguments

theorem constructorRow_iff (metadata : Metadata)
    (unique : (metadata.categories.map SourceCategory.name).Nodup)
    (row : ProductionRow) (lowered : LoweredConstructor) :
    constructorRow? metadata row = some lowered ↔ LowersConstructor metadata row lowered := by
  unfold LowersConstructor
  rw [declared_iff_lookup SourceCategory.name metadata.categories unique]
  constructor
  · intro found
    cases projection : row.projection <;> simp only [constructorRow?, projection] at found
    all_goals try contradiction
    rename_i head
    cases chosen : category? metadata row.resultCategory with
    | none => simp [chosen] at found
    | some category =>
        by_cases rule : category.kind = .rule
        · cases logical : category.logicalSort with
          | none => simp [chosen, rule, logical] at found
          | some result =>
              cases arguments : argumentSorts? metadata (argumentNames row.rhs) with
              | none => simp [chosen, arguments] at found
              | some sorts =>
                  have same : (⟨row, result, ⟨head, sorts⟩⟩ : LoweredConstructor) = lowered := by
                    simpa [chosen, rule, logical, arguments] using found
                  subst lowered
                  exact ⟨rfl, rfl, ⟨category, chosen, rule, logical⟩,
                    (argumentSorts_iff metadata unique _ sorts).mp arguments⟩
        · simp [chosen, rule] at found
  · rintro ⟨same, projection, ⟨category, chosen, rule, logical⟩, arguments⟩
    have loweredArguments := (argumentSorts_iff metadata unique _ _).mpr arguments
    cases lowered with
    | mk source result declaration =>
        cases declaration with
        | mk head sorts =>
            simp only at same projection logical loweredArguments
            subst source
            simp [constructorRow?, projection, category?, chosen, rule, logical, loweredArguments]

def constructorRows (metadata : Metadata) : List LoweredConstructor :=
  metadata.productions.filterMap (constructorRow? metadata)

theorem mem_constructorRows_iff (metadata : Metadata)
    (unique : (metadata.categories.map SourceCategory.name).Nodup)
    (lowered : LoweredConstructor) :
    lowered ∈ constructorRows metadata ↔
      ∃ row ∈ metadata.productions, LowersConstructor metadata row lowered := by
  simp only [constructorRows, List.mem_filterMap, constructorRow_iff metadata unique]

theorem constructorRows_preserve_occurrence (metadata : Metadata)
    (unique : (metadata.categories.map SourceCategory.name).Nodup)
    (lowered : LoweredConstructor) (member : lowered ∈ constructorRows metadata) :
    lowered.source ∈ metadata.productions := by
  obtain ⟨row, source, loweredCorrect⟩ := (mem_constructorRows_iff metadata unique lowered).mp member
  simpa [loweredCorrect.1] using source

theorem constructorRow_exists (metadata : Metadata) (profile : Notation)
    (valid : Valid metadata profile) (row : ProductionRow) (member : row ∈ metadata.productions)
    (head : String) (projection : row.projection = .constructor head) :
    ∃ lowered, constructorRow? metadata row = some lowered := by
  obtain ⟨_, _, category, categoryMember, named, contract⟩ := valid.productions row member
  cases kind : category.kind <;> cases logical : category.logicalSort <;>
    simp [kind, logical, projection] at contract
  rename_i result
  obtain ⟨declaration, _, _, sorts, arguments, _⟩ := contract
  refine ⟨⟨row, result, ⟨head, sorts⟩⟩, ?_⟩
  exact (constructorRow_iff metadata valid.uniqueCategories row _).mpr
    ⟨rfl, projection, ⟨category, categoryMember, named, kind, logical⟩, arguments⟩

def LoweredConstructor.key (row : LoweredConstructor) : String × String :=
  (row.resultSort, row.declaration.name)

theorem constructorRow_key (metadata : Metadata)
    (unique : (metadata.categories.map SourceCategory.name).Nodup)
    (row : ProductionRow) (lowered : LoweredConstructor)
    (compiled : constructorRow? metadata row = some lowered) :
    constructorKey? metadata row = some lowered.key := by
  obtain ⟨_, projection, ⟨category, member, named, _, logical⟩, _⟩ :=
    (constructorRow_iff metadata unique row lowered).mp compiled
  have chosen := lookup_complete SourceCategory.name metadata.categories unique
    row.resultCategory category member named
  simp [constructorKey?, projection, category?, chosen, logical, LoweredConstructor.key]

/-- Complete compilation retains the source-order sequence of constructor
keys. A refused row cannot disappear from an admitted family. -/
theorem constructorRows_keys (metadata : Metadata) (profile : Notation)
    (valid : Valid metadata profile) :
    (constructorRows metadata).map LoweredConstructor.key =
      metadata.productions.filterMap (constructorKey? metadata) := by
  rw [constructorRows, List.map_filterMap]
  apply List.filterMap_congr
  intro row member
  cases projection : row.projection <;>
    simp only [constructorRow?, constructorKey?, projection]
  all_goals try rfl
  rename_i head
  obtain ⟨lowered, compiled⟩ := constructorRow_exists metadata profile valid row member head projection
  have key := constructorRow_key metadata valid.uniqueCategories row lowered compiled
  simp only [constructorRow?, projection] at compiled
  simp only [constructorKey?, projection] at key
  rw [compiled, Option.map_some, key]

theorem constructorRows_unique_keys (metadata : Metadata) (profile : Notation)
    (valid : Valid metadata profile) :
    ((constructorRows metadata).map LoweredConstructor.key).Nodup := by
  rw [constructorRows_keys metadata profile valid]
  exact valid.uniqueHeads

theorem constructorRows_unique_occurrences (metadata : Metadata) (profile : Notation)
    (valid : Valid metadata profile) :
    ((constructorRows metadata).map (fun row => row.source.occurrence)).Nodup := by
  have unique : (metadata.productions.filterMap
      (fun row => (constructorRow? metadata row).map (fun result => result.source.occurrence))).Nodup := by
    have subsequence : List.Sublist (metadata.productions.filterMap
        (fun row => (constructorRow? metadata row).map (fun result => result.source.occurrence)))
          (metadata.productions.map ProductionRow.occurrence) := by
      induction metadata.productions with
      | nil => simp
      | cons row rows ih =>
          cases compiled : constructorRow? metadata row with
          | none => simpa [compiled] using ih.cons (row.occurrence)
          | some lowered =>
              have source := (constructorRow_iff metadata valid.uniqueCategories row lowered).mp compiled
              simpa [compiled, source.1] using ih.cons_cons (row.occurrence)
    exact valid.uniqueOccurrences.sublist subsequence
  simpa only [constructorRows, List.map_filterMap] using unique

/-- Finite schema extraction in source-row order. Ordered argument lists were
computed from actual source slots; list and token wrappers come from sort rows. -/
def schema (metadata : Metadata) (acceptsToken : String → String → Bool) : Schema where
  shape? sort := do
    let row ← sort? metadata sort
    pure <| match row.shape with
      | .token representation _ => .token representation
      | .list element _ => .list element
      | .constructors => .constructors
          (((constructorRows metadata).filter (fun row => row.resultSort == sort)).map
            LoweredConstructor.declaration)
  acceptsToken := acceptsToken

def layout (metadata : Metadata) : Layout where
  tokenHead sort :=
    match sort? metadata sort with
    | some ⟨_, .token _ head⟩ => head
    | _ => ""
  listKey sort :=
    match sort? metadata sort with
    | some ⟨_, .list _ key⟩ => key
    | _ => ""

structure AdmittedMetadata (profile : Notation) where
  data : Metadata
  valid : Valid data profile

def admit? (metadata : Metadata) (profile : Notation) : Option (AdmittedMetadata profile) :=
  if accepted : check metadata profile = true then
    some ⟨metadata, (check_iff metadata profile).mp accepted⟩
  else none

theorem admit_isSome_iff (metadata : Metadata) (profile : Notation) :
    (admit? metadata profile).isSome = true ↔ Valid metadata profile := by
  simp only [admit?]
  split
  · rename_i accepted
    simp [(check_iff metadata profile).mp accepted]
  · rename_i refused
    simp [← check_iff, refused]

theorem schema_token (metadata : Metadata) (profile : Notation) (valid : Valid metadata profile)
    (acceptsToken : String → String → Bool) (row : SortRow) (member : row ∈ metadata.sorts)
    (representation : TokenRepresentation) (head : String)
    (shape : row.shape = .token representation head) :
    (schema metadata acceptsToken).shape? row.name = some (.token representation) ∧
      (layout metadata).tokenHead row.name = head := by
  have found := lookup_complete SortRow.name metadata.sorts valid.uniqueSorts row.name row member rfl
  cases row with
  | mk name kind => cases shape; simp [schema, layout, sort?, found]

theorem schema_list (metadata : Metadata) (profile : Notation) (valid : Valid metadata profile)
    (acceptsToken : String → String → Bool) (row : SortRow) (member : row ∈ metadata.sorts)
    (element key : String) (shape : row.shape = .list element key) :
    (schema metadata acceptsToken).shape? row.name = some (.list element) ∧
      (layout metadata).listKey row.name = key := by
  have found := lookup_complete SortRow.name metadata.sorts valid.uniqueSorts row.name row member rfl
  cases row with
  | mk name kind => cases shape; simp [schema, layout, sort?, found]

theorem schema_constructors (metadata : Metadata) (profile : Notation) (valid : Valid metadata profile)
    (acceptsToken : String → String → Bool) (row : SortRow) (member : row ∈ metadata.sorts)
    (shape : row.shape = .constructors) :
    (schema metadata acceptsToken).shape? row.name = some (.constructors
      (((constructorRows metadata).filter (fun source => source.resultSort == row.name)).map
        LoweredConstructor.declaration)) := by
  have found := lookup_complete SortRow.name metadata.sorts valid.uniqueSorts row.name row member rfl
  cases row with
  | mk name kind => cases shape; simp [schema, sort?, found]

/-- Visible lowering is intentionally partial. A terminal with no surface
text and an erased profile event need a separate source correspondence. -/
def surfaceSlot? (metadata : Metadata) : Slot → Option Sym
  | .fixed _ (some text) => some (.fixed text)
  | .fixed _ none => none
  | .erased _ => none
  | .argument name => do
      let category ← category? metadata name
      match category.kind with
      | .rule => some (.rule name)
      | .token => some (.token name)
      | .erased => none

inductive SurfaceSlot (metadata : Metadata) : Slot → Sym → Prop where
  | fixed (raw text : String) : SurfaceSlot metadata (.fixed raw (some text)) (.fixed text)
  | rule (name : String) (category : SourceCategory) (member : category ∈ metadata.categories)
      (named : category.name = name) (kind : category.kind = .rule) :
      SurfaceSlot metadata (.argument name) (.rule name)
  | token (name : String) (category : SourceCategory) (member : category ∈ metadata.categories)
      (named : category.name = name) (kind : category.kind = .token) :
      SurfaceSlot metadata (.argument name) (.token name)

theorem surfaceSlot_iff (metadata : Metadata)
    (unique : (metadata.categories.map SourceCategory.name).Nodup) (slot : Slot) (symbol : Sym) :
    surfaceSlot? metadata slot = some symbol ↔ SurfaceSlot metadata slot symbol := by
  constructor
  · intro lowered
    cases slot with
    | fixed raw surface =>
        cases surface with
        | none => simp [surfaceSlot?] at lowered
        | some text =>
            have same : Sym.fixed text = symbol := by simpa [surfaceSlot?] using lowered
            subst symbol
            exact .fixed raw text
    | erased name => simp [surfaceSlot?] at lowered
    | argument name =>
        cases chosen : category? metadata name with
        | none => simp [surfaceSlot?, chosen] at lowered
        | some category =>
            have info := lookup_sound SourceCategory.name metadata.categories name category chosen
            cases kind : category.kind with
            | rule =>
                have same : Sym.rule name = symbol := by simpa [surfaceSlot?, chosen, kind] using lowered
                subst symbol
                exact .rule name category info.1 info.2 kind
            | token =>
                have same : Sym.token name = symbol := by simpa [surfaceSlot?, chosen, kind] using lowered
                subst symbol
                exact .token name category info.1 info.2 kind
            | erased => simp [surfaceSlot?, chosen, kind] at lowered
  · intro relation
    cases relation with
    | fixed raw text => rfl
    | rule name category member named kind =>
        have chosen := lookup_complete SourceCategory.name metadata.categories unique name category member named
        simp [surfaceSlot?, category?, chosen, kind]
    | token name category member named kind =>
        have chosen := lookup_complete SourceCategory.name metadata.categories unique name category member named
        simp [surfaceSlot?, category?, chosen, kind]

def surfaceSymbols? (metadata : Metadata) : List Slot → Option (List Sym)
  | [] => some []
  | slot :: slots => do
      return (← surfaceSlot? metadata slot) :: (← surfaceSymbols? metadata slots)

theorem surfaceSymbols_iff (metadata : Metadata)
    (unique : (metadata.categories.map SourceCategory.name).Nodup)
    (slots : List Slot) (symbols : List Sym) :
    surfaceSymbols? metadata slots = some symbols ↔
      List.Forall₂ (SurfaceSlot metadata) slots symbols := by
  induction slots generalizing symbols with
  | nil => cases symbols <;> simp [surfaceSymbols?, List.forall₂_nil_left_iff]
  | cons slot slots ih =>
      constructor
      · intro lowered
        cases first : surfaceSlot? metadata slot with
        | none => simp [surfaceSymbols?, first] at lowered
        | some symbol =>
            cases rest : surfaceSymbols? metadata slots with
            | none => simp [surfaceSymbols?, first, rest] at lowered
            | some tail =>
                have same : symbol :: tail = symbols := by simpa [surfaceSymbols?, first, rest] using lowered
                subst symbols
                exact .cons ((surfaceSlot_iff metadata unique slot symbol).mp first) ((ih tail).mp rest)
      · intro relation
        cases relation with
        | cons first rest =>
            simp [surfaceSymbols?, (surfaceSlot_iff metadata unique _ _).mpr first, (ih _).mpr rest]

/-- Labels are supplied independently from constructor heads. When a client
uses these productions as a CanonicalGrammar table it must provide an injective
occurrence-label assignment or check the resulting label table separately. -/
def surfaceProduction? (metadata : Metadata) (labelOf : Nat → String)
    (row : ProductionRow) : Option Production := do
  let category ← category? metadata row.resultCategory
  if category.kind ≠ .rule then none else do
    let symbols ← surfaceSymbols? metadata row.rhs
    pure ⟨labelOf row.occurrence, row.resultCategory, symbols⟩

def SurfaceProduction (metadata : Metadata) (labelOf : Nat → String)
    (row : ProductionRow) (production : Production) : Prop :=
  production.label = labelOf row.occurrence ∧ production.lhs = row.resultCategory ∧
    (∃ category ∈ metadata.categories, category.name = row.resultCategory ∧ category.kind = .rule) ∧
    List.Forall₂ (SurfaceSlot metadata) row.rhs production.rhs

theorem surfaceProduction_iff (metadata : Metadata) (labelOf : Nat → String)
    (unique : (metadata.categories.map SourceCategory.name).Nodup)
    (row : ProductionRow) (production : Production) :
    surfaceProduction? metadata labelOf row = some production ↔
      SurfaceProduction metadata labelOf row production := by
  unfold SurfaceProduction
  rw [declared_iff_lookup SourceCategory.name metadata.categories unique]
  constructor
  · intro lowered
    cases chosen : category? metadata row.resultCategory with
    | none => simp [surfaceProduction?, chosen] at lowered
    | some category =>
        by_cases rule : category.kind = .rule
        · cases symbols : surfaceSymbols? metadata row.rhs with
          | none => simp [surfaceProduction?, chosen, symbols] at lowered
          | some rhs =>
              have same : (⟨labelOf row.occurrence, row.resultCategory, rhs⟩ : Production) = production := by
                simpa [surfaceProduction?, chosen, rule, symbols] using lowered
              subst production
              exact ⟨rfl, rfl, ⟨category, chosen, rule⟩,
                (surfaceSymbols_iff metadata unique row.rhs rhs).mp symbols⟩
        · simp [surfaceProduction?, chosen, rule] at lowered
  · rintro ⟨label, lhs, ⟨category, chosen, rule⟩, symbols⟩
    have lowered := (surfaceSymbols_iff metadata unique row.rhs production.rhs).mpr symbols
    cases production with
    | mk name result rhs =>
        simp only at label lhs lowered
        subst name
        subst result
        simp [surfaceProduction?, category?, chosen, rule, lowered]

theorem surfaceProduction_order (metadata : Metadata) (labelOf : Nat → String)
    (unique : (metadata.categories.map SourceCategory.name).Nodup)
    (row : ProductionRow) (production : Production)
    (lowered : surfaceProduction? metadata labelOf row = some production) :
    row.rhs.length = production.rhs.length :=
  ((surfaceProduction_iff metadata labelOf unique row production).mp lowered).2.2.2.length_eq

theorem surfaceProduction_occurrence_separation (metadata : Metadata) (labelOf : Nat → String)
    (labels : Function.Injective labelOf)
    (unique : (metadata.categories.map SourceCategory.name).Nodup)
    (first second : ProductionRow) (left right : Production)
    (loweredLeft : surfaceProduction? metadata labelOf first = some left)
    (loweredRight : surfaceProduction? metadata labelOf second = some right)
    (sameLabel : left.label = right.label) : first.occurrence = second.occurrence := by
  have leftLabel := ((surfaceProduction_iff metadata labelOf unique first left).mp loweredLeft).1
  have rightLabel := ((surfaceProduction_iff metadata labelOf unique second right).mp loweredRight).1
  exact labels (leftLabel.symm.trans (sameLabel.trans rightLabel))

def AdmittedMetadata.schema {profile : Notation} (metadata : AdmittedMetadata profile)
    (acceptsToken : String → String → Bool) : Schema :=
  SortedCodecMetadataAdmission.schema metadata.data acceptsToken

def AdmittedMetadata.layout {profile : Notation} (metadata : AdmittedMetadata profile) : Layout :=
  SortedCodecMetadataAdmission.layout metadata.data

end Mettapedia.GSLT.Parsing.SortedCodecMetadataAdmission
