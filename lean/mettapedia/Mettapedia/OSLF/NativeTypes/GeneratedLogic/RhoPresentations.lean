import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalPresentations
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagCanonicalParts

/-!
# ρ's presentations at the front door

ρ's canonical forms list the presentations of their terms (`listing`), so the front door decides constructor formers,
splits, emptiness and types modulo ρ's equations (`decider`):

- **Splits** of a canonical process deal its parallel components (`atoms`: none for `0`, the elements of a bag, the
  process itself otherwise) into two, each part read as a bag (`splits_complete`, `splits_sound`). Names and
  continuations do not split, and a process is empty exactly when it is `0` (`empty_iff`).
- **Constructor presentations** of a canonical term are its own arguments, except that a quoted process `@P` is also
  the quotation of the drop of itself, `@*@P` (`builds_complete`, `builds_sound`).
- **Types**: a canonical element has the type of its kind (a process, a name, or an input continuation) and none of
  the other two (`typed_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Rho

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.ScopedPattern (binderSafeAt isWellScopedAt_of_binderSafeAt)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
  (canonicalize canonicalizeList normalizeQuote collapseBag bagContents bagSplice sortPatterns normalizeBagElements
    IsCanonical IsCanonicalList canonicalize_isCanonical canonicalize_eq_of_isCanonical canonicalizeList_isCanonical
    isCanonicalList_mem isCanonicalList_of_forall canonicalizeList_eq_of_isCanonical canonicalizeList_eq_map
    normalizeBagElements_eq_sort_bagContents bagContents_append canonicalizeList_append sortPatterns_perm
    collapse_normalize_singleton_of_isCanonical bagContents_collapse_normalized flatMap_bagSplice_eq_self
    mem_bagSplice canonicalize_apply_general normalizeQuote_eq_quote_of_not_drop)
open Mettapedia.OSLF.MeTTaIL.PatternCode (sortPatterns_eq_of_perm)
open Mettapedia.OSLF.NativeTypes.Instances.Rho.TypedEquations
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagForms (deals perm_of_mem_deals exists_deal)

/-! ## Presentations of admitted terms, read off their typing -/

/-- **The ways an admitted term is built by a constructor**: from arguments of the constructor's parameters' kinds. -/
theorem apply_cases {constructor : String} {parts : List Pattern}
    (admitted : domain (.apply constructor parts) = true) :
    (constructor = "PZero" ∧ parts = []) ∨
      (∃ channel, constructor = "PDrop" ∧ parts = [channel] ∧ name channel = true) ∨
      (∃ quoted, constructor = "NQuote" ∧ parts = [quoted] ∧ process quoted = true) ∨
      (∃ channel payload, constructor = "POutput" ∧ parts = [channel, payload] ∧ name channel = true ∧
        process payload = true) ∨
      (∃ channel body, constructor = "PInput" ∧ parts = [channel, body] ∧ name channel = true ∧
        continuation body = true) := by
  have formed : ∃ sort, HasSort rhoCalc FreeTypeContext.empty [] (.apply constructor parts) sort ∧
      isObjectPattern (.apply constructor parts) = true ∧ Sealed 0 (.apply constructor parts) := by
    simp only [domain, Bool.or_eq_true] at admitted
    rcases admitted with (admitted | admitted) | admitted
    · exact ⟨"Proc", process_iff.mp admitted⟩
    · exact ⟨"Name", name_iff.mp admitted⟩
    · simp [continuation] at admitted
  obtain ⟨sort, typed, object, sealed⟩ := formed
  obtain ⟨rule, member, label, notBare, -, argumentsTyped⟩ := hasType_apply_inversion typed
  subst label
  simp only [rhoCalc, List.mem_cons, List.not_mem_nil, or_false] at member
  simp only [isObjectPattern] at object
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · cases argumentsTyped
    exact Or.inl ⟨rfl, rfl⟩
  · cases argumentsTyped with
    | @cons _ channel arguments parameter parameters expected _ parameterType channelTyped argumentsTyped =>
      cases argumentsTyped
      have expectedEquality : expected = TypeExpr.name := by
        simpa [parameterType?, TypeExpr.name, TypeExpr.baseType] using parameterType.symm
      subst expected
      simp only [isObjectPatternList, Bool.and_true] at object
      exact Or.inr (Or.inl ⟨channel, rfl, rfl,
        name_iff.mpr ⟨channelTyped, object, (sealed_unary (by decide)).mp sealed⟩⟩)
  · cases argumentsTyped with
    | @cons _ quoted arguments parameter parameters expected _ parameterType quotedTyped argumentsTyped =>
      cases argumentsTyped
      have expectedEquality : expected = TypeExpr.proc := by
        simpa [parameterType?, TypeExpr.proc, TypeExpr.baseType] using parameterType.symm
      subst expected
      simp only [isObjectPatternList, Bool.and_true] at object
      exact Or.inr (Or.inr (Or.inl ⟨quoted, rfl, rfl,
        process_iff.mpr ⟨quotedTyped, object, sealed_quote.mp sealed⟩⟩))
  · simp [UsesBareCollection, TypeExpr.bag, TypeExpr.proc, TypeExpr.baseType] at notBare
  · cases argumentsTyped with
    | @cons _ channel arguments parameter parameters channelType _ channelParameterType channelTyped
        argumentsTyped =>
      cases argumentsTyped with
      | @cons _ payload arguments parameter parameters payloadType _ payloadParameterType payloadTyped
          argumentsTyped =>
        cases argumentsTyped
        have channelTypeEquality : channelType = TypeExpr.name := by
          simpa [parameterType?, TypeExpr.name, TypeExpr.baseType] using channelParameterType.symm
        have payloadTypeEquality : payloadType = TypeExpr.proc := by
          simpa [parameterType?, TypeExpr.proc, TypeExpr.baseType] using payloadParameterType.symm
        subst channelType
        subst payloadType
        simp only [isObjectPatternList, Bool.and_true, Bool.and_eq_true] at object
        obtain ⟨channelSealed, payloadSealed⟩ := sealed_binary.mp sealed
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨channel, payload, rfl, rfl,
          name_iff.mpr ⟨channelTyped, object.1, channelSealed⟩,
          process_iff.mpr ⟨payloadTyped, object.2, payloadSealed⟩⟩)))
  · cases argumentsTyped with
    | @cons _ channel arguments parameter parameters channelType _ channelParameterType channelTyped
        argumentsTyped =>
      cases argumentsTyped with
      | @cons _ abstraction arguments parameter parameters bodyType bodyRepresentation bodyParameterType
          abstractionTyped argumentsTyped =>
        cases argumentsTyped
        have channelTypeEquality : channelType = TypeExpr.name := by
          simpa [parameterType?, TypeExpr.name, TypeExpr.baseType] using channelParameterType.symm
        have bodyTypeEquality : bodyType = TypeExpr.arrow TypeExpr.name TypeExpr.proc := by
          simpa [parameterType?, TypeExpr.name, TypeExpr.proc, TypeExpr.funType, TypeExpr.baseType] using
            bodyParameterType.symm
        subst channelType
        subst bodyType
        simp only [isObjectPatternList, Bool.and_true, Bool.and_eq_true] at object
        obtain ⟨channelSealed, abstractionSealed⟩ := sealed_binary.mp sealed
        cases abstraction with
        | lambda binder body =>
          cases binder with
          | none =>
            cases abstractionTyped with
            | lambda bodyTyped =>
              exact Or.inr (Or.inr (Or.inr (Or.inr ⟨channel, .lambda none body, rfl, rfl,
                name_iff.mpr ⟨channelTyped, object.1, channelSealed⟩,
                continuation_lambda_iff.mpr ⟨by simpa [isObjectPattern] using object.2, bodyTyped,
                  sealed_lambda.mp abstractionSealed⟩⟩)))
          | some binderName => simp [MatchesParameterRepresentation] at bodyRepresentation
        | bvar index => simp [MatchesParameterRepresentation] at bodyRepresentation
        | fvar name => simp [MatchesParameterRepresentation] at bodyRepresentation
        | apply name arguments => simp [MatchesParameterRepresentation] at bodyRepresentation
        | multiLambda arity binders body => simp [MatchesParameterRepresentation] at bodyRepresentation
        | subst body replacement => simp [MatchesParameterRepresentation] at bodyRepresentation
        | collection collectionType elements rest => simp [MatchesParameterRepresentation] at bodyRepresentation

/-- A term built by a constructor with the sort of names is built by quotation. -/
theorem name_label {constructor : String} {parts : List Pattern}
    (typed : HasSort rhoCalc FreeTypeContext.empty [] (.apply constructor parts) "Name") : constructor = "NQuote" := by
  obtain ⟨rule, member, label, -, sortEquality, -⟩ := hasType_apply_inversion typed
  subst label
  simp only [rhoCalc, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-- **An admitted name is the quotation of an admitted process.** -/
theorem name_cases {term : Pattern} (admitted : name term = true) :
    ∃ quoted, term = .apply "NQuote" [quoted] ∧ process quoted = true := by
  obtain ⟨typed, object, sealed⟩ := name_iff.mp admitted
  cases term with
  | apply constructor parts =>
    have quote := name_label typed
    subst quote
    rcases apply_cases (by simp [domain, admitted] : domain (.apply "NQuote" parts) = true) with
      ⟨equal, -⟩ | ⟨_, equal, -⟩ | ⟨quoted, -, rfl, quotedProcess⟩ | ⟨_, _, equal, -⟩ | ⟨_, _, equal, -⟩
    · exact absurd equal (by decide)
    · exact absurd equal (by decide)
    · exact ⟨quoted, rfl, quotedProcess⟩
    · exact absurd equal (by decide)
    · exact absurd equal (by decide)
  | lambda binder body => exact absurd typed not_hasSort_lambda
  | collection kind elements rest => exact absurd (collection_sort typed).1 (by decide)
  | bvar index =>
    cases typed with
    | bvar lookup => simp at lookup
  | fvar free =>
    cases typed with
    | fvar lookup => simp [FreeTypeContext.empty] at lookup
  | multiLambda arity binders body => cases typed
  | subst body replacement => simp [isObjectPattern] at object

/-! ## Canonical terms -/

theorem isCanonical_of_canonical {term : Pattern} (canonState : canonicalize term = term) : IsCanonical term := by
  rw [← canonState]
  exact canonicalize_isCanonical term

/-- A canonical quotation quotes a canonical process that is not a drop. -/
theorem canonical_quoted {quoted : Pattern} (canonState : canonicalize (.apply "NQuote" [quoted]) = .apply "NQuote" [quoted]) :
    canonicalize quoted = quoted ∧ ∀ channel, quoted ≠ .apply "PDrop" [channel] := by
  have canonical : IsCanonical quoted ∧ ∀ channel, quoted ≠ .apply "PDrop" [channel] :=
    isCanonical_of_canonical canonState
  exact ⟨canonicalize_eq_of_isCanonical canonical.1, canonical.2⟩

/-! ## Parallel components -/

/-- **The parallel components of a term**: none for `0`, the elements of a bag, the term itself otherwise. -/
abbrev atoms (term : Pattern) : List Pattern := bagContents [term]

/-- A parallel component: canonical, not `0`, and not a bag. -/
def Atomic (atom : Pattern) : Prop :=
  IsCanonical atom ∧ atom ≠ .apply "PZero" [] ∧ ∀ nested, atom ≠ .collection .hashBag nested none

theorem mem_atoms {term atom : Pattern} (member : atom ∈ atoms term) :
    atom ∈ bagSplice term ∧ atom ≠ .apply "PZero" [] := by
  simpa [atoms, bagContents] using member

/-- **The parallel components of a canonical term are atomic.** -/
theorem atoms_atomic {term : Pattern} (canonical : IsCanonical term) {atom : Pattern} (member : atom ∈ atoms term) :
    Atomic atom := by
  obtain ⟨spliced, notZero⟩ := mem_atoms member
  rcases mem_bagSplice spliced with ⟨elements, rfl, inside⟩ | ⟨rfl, notBag⟩
  · change 2 ≤ elements.length ∧ sortPatterns elements = elements ∧
      (∀ element ∈ elements, element ≠ .apply "PZero" [] ∧ ∀ nested, element ≠ .collection .hashBag nested none) ∧
      IsCanonicalList elements at canonical
    exact ⟨isCanonicalList_mem canonical.2.2.2 inside, notZero, (canonical.2.2.1 atom inside).2⟩
  · exact ⟨canonical, notZero, notBag⟩

/-- **The parallel components of a formed process are formed.** -/
theorem atoms_good {term : Pattern} (good : Good FreeTypeContext.empty [] 0 term) {atom : Pattern}
    (member : atom ∈ atoms term) : Good FreeTypeContext.empty [] 0 atom := by
  obtain ⟨spliced, -⟩ := mem_atoms member
  rcases mem_bagSplice spliced with ⟨elements, rfl, inside⟩ | ⟨rfl, -⟩
  · exact good_of_bag good atom inside
  · exact good

theorem bagContents_atomic {elements : List Pattern} (atomic : ∀ atom ∈ elements, Atomic atom) :
    bagContents elements = elements := by
  unfold bagContents
  rw [flatMap_bagSplice_eq_self (fun atom member => (atomic atom member).2.2)]
  exact List.filter_eq_self.mpr fun atom member => by simpa using (atomic atom member).2.1

theorem canonicalize_bag (elements : List Pattern) :
    canonicalize (.collection .hashBag elements none) =
      collapseBag (sortPatterns (bagContents (canonicalizeList elements))) := by
  rw [← normalizeBagElements_eq_sort_bagContents]
  rfl

/-- **A bag of atomic components has the canonical form of their sorted collapse.** -/
theorem canonicalize_bag_atomic {elements : List Pattern} (atomic : ∀ atom ∈ elements, Atomic atom) :
    canonicalize (.collection .hashBag elements none) = collapseBag (sortPatterns elements) := by
  rw [canonicalize_bag, canonicalizeList_eq_of_isCanonical
    (isCanonicalList_of_forall fun atom member => (atomic atom member).1), bagContents_atomic atomic]

/-- **A canonical term is the sorted collapse of its parallel components.** -/
theorem collapse_atoms {term : Pattern} (canonical : IsCanonical term) :
    collapseBag (sortPatterns (atoms term)) = term := by
  rw [← normalizeBagElements_eq_sort_bagContents]
  exact collapse_normalize_singleton_of_isCanonical canonical

/-- **The parallel components of a bag's canonical form are its elements' components, sorted.** -/
theorem atoms_canonicalize_bag (elements : List Pattern) :
    atoms (canonicalize (.collection .hashBag elements none)) =
      sortPatterns (bagContents (canonicalizeList elements)) := by
  rw [← normalizeBagElements_eq_sort_bagContents]
  exact bagContents_collapse_normalized (canonicalizeList_isCanonical elements)

/-! ## The listing -/

/-- **The splits of a canonical process**: its parallel components dealt into two, each part read as a bag. -/
def splitsOf (term : Pattern) (kind : CollType) : List (Pattern × Pattern) :=
  if kind = .hashBag ∧ process term = true then
    (deals (atoms term)).map fun pair =>
      (canonicalizeSorted (.collection .hashBag pair.1 none), canonicalizeSorted (.collection .hashBag pair.2 none))
  else []

theorem splitsOf_eq (term : Pattern) (kind : CollType) :
    splitsOf term kind =
      if kind = .hashBag ∧ process term = true then
        (deals (atoms term)).map fun pair =>
          (canonicalize (.collection .hashBag pair.1 none), canonicalize (.collection .hashBag pair.2 none))
      else [] := by
  rw [splitsOf, canonicalizeSorted_eq_fun]

/-- **The presentations of a canonical term by a constructor**: its own arguments, and for a quoted process `@P`
also the drop of itself, `@*@P`. -/
def builds (term : Pattern) (constructor : String) : List (List Pattern) :=
  match term with
  | .apply label arguments =>
    if constructor = label then
      arguments :: if label = "NQuote" ∧ arguments.length = 1 then [[.apply "PDrop" [.apply label arguments]]] else []
    else []
  | _ => []

/-- The constructor a term's presentations are listed for: its head. -/
def constructorsOf : Pattern → List String
  | .apply label _ => [label]
  | _ => []

theorem mem_builds {term : Pattern} {constructor : String} {arguments : List Pattern}
    (member : arguments ∈ builds term constructor) :
    ∃ others, term = .apply constructor others ∧
      (arguments = others ∨ (constructor = "NQuote" ∧ others.length = 1 ∧ arguments = [.apply "PDrop" [term]])) := by
  cases term
  case apply label others =>
    simp only [builds] at member
    split_ifs at member with same quote
    · subst same
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨arguments, rfl, Or.inl rfl⟩
      · exact ⟨others, rfl, Or.inr ⟨quote.1, quote.2, rfl⟩⟩
    · subst same
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      exact ⟨others, rfl, Or.inl member⟩
    · simp at member
  all_goals simp [builds] at member

theorem self_mem_builds (label : String) (arguments : List Pattern) :
    arguments ∈ builds (.apply label arguments) label := by
  simp [builds]

theorem drop_mem_builds (quoted : Pattern) :
    [.apply "PDrop" [.apply "NQuote" [quoted]]] ∈ builds (.apply "NQuote" [quoted]) "NQuote" := by
  simp [builds]

/-- The kinds of ρ's elements, as types. -/
def elementTypes : List TypeExpr := [TypeExpr.proc, TypeExpr.name, .arrow TypeExpr.name TypeExpr.proc]

/-- **The type of a canonical element**: that of its kind. -/
def typedAt (term : Pattern) (type : TypeExpr) : Bool :=
  (type == TypeExpr.proc && process term) || (type == TypeExpr.name && name term) ||
    (type == .arrow TypeExpr.name TypeExpr.proc && continuation term)

variable {relEnv : RelationEnv}

/-- **The listed splits are complete**: every split of an admitted canonical term has admitted parts whose canonical
forms are listed. -/
theorem splits_complete {state : Pattern} {kind : CollType} {first second : Pattern} (admitted : domain state = true)
    (canonState : canonicalizeSorted state = state)
    (split : (referenceStructure relEnv rhoCalc reading).split state kind first second) :
    domain first = true ∧ domain second = true ∧
      (canonicalizeSorted first, canonicalizeSorted second) ∈ splitsOf state kind := by
  rw [canonicalizeSorted_eq_fun] at canonState ⊢
  rw [splitsOf_eq]
  obtain ⟨-, left, right, equivalent, rfl, rfl⟩ := split
  obtain ⟨bagProcess, rfl, -⟩ := process_of_collection (invariant admitted equivalent)
  have stateProcess := process_invariant bagProcess (ObjectEquivalent.equivalence.symm equivalent)
  have bagGood : Good FreeTypeContext.empty [] 0 (.collection .hashBag (left ++ right) none) := by
    obtain ⟨typed, object, sealed⟩ := process_iff.mp bagProcess
    exact ⟨object, typed, sealed⟩
  have elementsGood := good_of_bag bagGood
  have leftGood := bag_good fun element member => elementsGood element (List.mem_append_left _ member)
  have rightGood := bag_good fun element member => elementsGood element (List.mem_append_right _ member)
  refine ⟨domain_of_process (process_iff.mpr ⟨leftGood.typed, leftGood.object, leftGood.formed⟩),
    domain_of_process (process_iff.mpr ⟨rightGood.typed, rightGood.object, rightGood.formed⟩), ?_⟩
  rw [if_pos ⟨rfl, stateProcess⟩]
  have canonBag : canonicalize (.collection .hashBag (left ++ right) none) = state :=
    (canonicalize_eq_of_objectEquivalent equivalent).symm.trans canonState
  have stateCanonical := isCanonical_of_canonical canonState
  have perm : (bagContents (canonicalizeList left) ++ bagContents (canonicalizeList right)).Perm (atoms state) := by
    rw [← canonBag, atoms_canonicalize_bag, canonicalizeList_append, bagContents_append]
    exact sortPatterns_perm _
  obtain ⟨pair, member, leftPerm, rightPerm⟩ := exists_deal perm
  have atomic : ∀ atom ∈ pair.1 ++ pair.2, Atomic atom :=
    fun atom inside => atoms_atomic stateCanonical ((perm_of_mem_deals member).subset inside)
  refine List.mem_map.mpr ⟨pair, member, ?_⟩
  rw [canonicalize_bag_atomic (fun atom inside => atomic atom (List.mem_append_left _ inside)),
    canonicalize_bag_atomic (fun atom inside => atomic atom (List.mem_append_right _ inside)),
    canonicalize_bag left, canonicalize_bag right, sortPatterns_eq_of_perm leftPerm, sortPatterns_eq_of_perm rightPerm]

/-- **The listed splits are sound**: each is the canonical form of a split with admitted parts. -/
theorem splits_sound {state : Pattern} {kind : CollType} {pair : Pattern × Pattern} (admitted : domain state = true)
    (canonState : canonicalizeSorted state = state) (member : pair ∈ splitsOf state kind) :
    ∃ first second, (referenceStructure relEnv rhoCalc reading).split state kind first second ∧
      domain first = true ∧ domain second = true ∧ canonicalizeSorted first = pair.1 ∧
        canonicalizeSorted second = pair.2 := by
  rw [canonicalizeSorted_eq_fun] at canonState ⊢
  rw [splitsOf_eq] at member
  split_ifs at member with guard
  · obtain ⟨rfl, stateProcess⟩ := guard
    obtain ⟨deal, dealMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨stateTyped, stateObject, stateSealed⟩ := process_iff.mp stateProcess
    have stateCanonical := isCanonical_of_canonical canonState
    have dealPerm := perm_of_mem_deals dealMember
    have dealGood : ∀ atom ∈ deal.1 ++ deal.2, Good FreeTypeContext.empty [] 0 atom :=
      fun atom inside => atoms_good ⟨stateObject, stateTyped, stateSealed⟩ (dealPerm.subset inside)
    have atomic : ∀ atom ∈ deal.1 ++ deal.2, Atomic atom :=
      fun atom inside => atoms_atomic stateCanonical (dealPerm.subset inside)
    have bagGood := bag_good dealGood
    have firstGood := bag_good fun atom inside => dealGood atom (List.mem_append_left _ inside)
    have secondGood := bag_good fun atom inside => dealGood atom (List.mem_append_right _ inside)
    have equivalent : ObjectEquivalent relEnv rhoCalc reading state (.collection .hashBag (deal.1 ++ deal.2) none) := by
      refine (objectEquivalent_iff admitted
        (domain_of_process (process_iff.mpr ⟨bagGood.typed, bagGood.object, bagGood.formed⟩))).mpr ?_
      rw [canonState, canonicalize_bag_atomic atomic, sortPatterns_eq_of_perm dealPerm, collapse_atoms stateCanonical]
    exact ⟨_, _, ⟨stateObject, deal.1, deal.2, equivalent, rfl, rfl⟩,
      domain_of_process (process_iff.mpr ⟨firstGood.typed, firstGood.object, firstGood.formed⟩),
      domain_of_process (process_iff.mpr ⟨secondGood.typed, secondGood.object, secondGood.formed⟩), rfl, rfl⟩
  · simp at member

/-- **An admitted canonical term is empty exactly when it is `0`.** -/
theorem empty_iff {state : Pattern} {kind : CollType} (admitted : domain state = true)
    (canonState : canonicalizeSorted state = state) :
    ((kind == .hashBag && state == .apply "PZero" []) = true ↔
      (referenceStructure relEnv rhoCalc reading).empty state kind) := by
  rw [canonicalizeSorted_eq_fun] at canonState
  simp only [Bool.and_eq_true, beq_iff_eq]
  have emptyGood := bag_good (free := FreeTypeContext.empty) (bound := []) (depth := 0) (elements := [])
    fun _ member => nomatch member
  have emptyProcess : process (.collection .hashBag [] none) = true :=
    process_iff.mpr ⟨emptyGood.typed, emptyGood.object, emptyGood.formed⟩
  have emptyCanon : canonicalize (.collection .hashBag [] none) = .apply "PZero" [] := by
    rw [← canonicalizeSorted_eq]
    rfl
  constructor
  · rintro ⟨rfl, rfl⟩
    refine ⟨rfl, (objectEquivalent_iff admitted (domain_of_process emptyProcess)).mpr ?_⟩
    rw [emptyCanon, ← canonicalizeSorted_eq]
    rfl
  · rintro ⟨-, equivalent⟩
    obtain ⟨-, rfl, -⟩ := process_of_collection (invariant admitted equivalent)
    refine ⟨rfl, ?_⟩
    rw [← canonState, canonicalize_eq_of_objectEquivalent equivalent, emptyCanon]

theorem listed_constructor {state : Pattern} {constructor : String} {arguments : List Pattern}
    (member : arguments ∈ builds state constructor) : constructor ∈ constructorsOf state := by
  obtain ⟨others, rfl, -⟩ := mem_builds member
  simp [constructorsOf]

/-- **The listed presentations are complete**: every presentation of an admitted canonical term by a constructor has
admitted arguments whose canonical forms are listed. -/
theorem builds_complete {state : Pattern} {constructor : String} {parts : List Pattern}
    (admitted : domain state = true) (canonState : canonicalizeSorted state = state)
    (built : (referenceStructure relEnv rhoCalc reading).built state constructor parts) :
    (∀ part ∈ parts, domain part = true) ∧ parts.map canonicalizeSorted ∈ builds state constructor := by
  rw [canonicalizeSorted_eq_fun] at canonState ⊢
  obtain ⟨-, equivalent⟩ := built
  have builtAdmitted := invariant admitted equivalent
  have same : canonicalize (.apply constructor parts) = state :=
    (canonicalize_eq_of_objectEquivalent equivalent).symm.trans canonState
  have ordinary : ¬ (constructor = "NQuote" ∧ ∃ quoted, parts = [quoted]) →
      parts.map canonicalize ∈ builds state constructor := by
    intro notQuote
    rw [← same, canonicalize_apply_general _ _ notQuote, ← canonicalizeList_eq_map]
    exact self_mem_builds _ _
  rcases apply_cases builtAdmitted with ⟨rfl, rfl⟩ | ⟨channel, rfl, rfl, channelName⟩ |
      ⟨quoted, rfl, rfl, quotedProcess⟩ | ⟨channel, payload, rfl, rfl, channelName, payloadProcess⟩ |
      ⟨channel, body, rfl, rfl, channelName, bodyContinuation⟩
  · exact ⟨(fun _ member => nomatch member), ordinary (by simp)⟩
  · exact ⟨by simp [domain, channelName], ordinary (by simp)⟩
  · refine ⟨by simp [domain_of_process quotedProcess], ?_⟩
    obtain ⟨quotedTyped, quotedObject, quotedSealed⟩ := process_iff.mp quotedProcess
    have quoteName : name (.apply "NQuote" [quoted]) = true :=
      name_iff.mpr ⟨rho_quote_hasSort quotedTyped, by simpa [isObjectPattern, isObjectPatternList] using quotedObject,
        sealed_quote.mpr quotedSealed⟩
    have stateName : name state = true := (kinds_of_equivalent equivalent).2.1.mpr quoteName
    obtain ⟨canonical, rfl, -⟩ := name_cases stateName
    change normalizeQuote (canonicalize quoted) = .apply "NQuote" [canonical] at same
    rw [List.map_singleton]
    by_cases isDrop : ∃ channel, canonicalize quoted = .apply "PDrop" [channel]
    · obtain ⟨channel, isDrop⟩ := isDrop
      rw [isDrop] at same
      simp only [normalizeQuote] at same
      subst same
      rw [isDrop]
      exact drop_mem_builds canonical
    · rw [normalizeQuote_eq_quote_of_not_drop (fun channel equal => isDrop ⟨channel, equal⟩)] at same
      simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
      rw [same]
      exact self_mem_builds _ _
  · exact ⟨by simp [domain, channelName, payloadProcess], ordinary (by simp)⟩
  · exact ⟨by simp [domain, channelName, bodyContinuation], ordinary (by simp)⟩

/-- **The listed presentations are sound**: each is the canonical form of a presentation with admitted
arguments. -/
theorem builds_sound {state : Pattern} {constructor : String} {arguments : List Pattern}
    (admitted : domain state = true) (canonState : canonicalizeSorted state = state)
    (member : arguments ∈ builds state constructor) :
    ∃ parts, (referenceStructure relEnv rhoCalc reading).built state constructor parts ∧
      (∀ part ∈ parts, domain part = true) ∧ parts.map canonicalizeSorted = arguments := by
  rw [canonicalizeSorted_eq_fun] at canonState ⊢
  have object : IsObject state := (canonical relEnv).object admitted
  obtain ⟨others, rfl, rfl | ⟨rfl, length, rfl⟩⟩ := mem_builds member
  · refine ⟨arguments, ⟨object, Relation.EqvGen.refl _⟩, ?_, ?_⟩
    · rcases apply_cases admitted with ⟨-, rfl⟩ | ⟨channel, -, rfl, channelName⟩ | ⟨quoted, -, rfl, quotedProcess⟩ |
          ⟨channel, payload, -, rfl, channelName, payloadProcess⟩ |
          ⟨channel, body, -, rfl, channelName, bodyContinuation⟩
      · exact fun _ member => nomatch member
      · simp [domain, channelName]
      · simp [domain_of_process quotedProcess]
      · simp [domain, channelName, payloadProcess]
      · simp [domain, channelName, bodyContinuation]
    · by_cases isQuote : constructor = "NQuote" ∧ ∃ quoted, arguments = [quoted]
      · obtain ⟨rfl, quoted, rfl⟩ := isQuote
        simp [(canonical_quoted canonState).1]
      · rw [canonicalize_apply_general _ _ isQuote, canonicalizeList_eq_map] at canonState
        exact (Pattern.apply.inj canonState).2
  · obtain ⟨quoted, rfl⟩ := List.length_eq_one_iff.mp length
    have stateName : name (.apply "NQuote" [quoted]) = true := by
      rcases apply_cases admitted with ⟨equal, -⟩ | ⟨_, equal, -⟩ | ⟨_, -, same, quotedProcess⟩ | ⟨_, _, equal, -⟩ |
          ⟨_, _, equal, -⟩
      · exact absurd equal (by decide)
      · exact absurd equal (by decide)
      · cases same
        obtain ⟨quotedTyped, quotedObject, quotedSealed⟩ := process_iff.mp quotedProcess
        exact name_iff.mpr ⟨rho_quote_hasSort quotedTyped,
          by simpa [isObjectPattern, isObjectPatternList] using quotedObject, sealed_quote.mpr quotedSealed⟩
      · exact absurd equal (by decide)
      · exact absurd equal (by decide)
    obtain ⟨nameTyped, nameObject, nameSealed⟩ := name_iff.mp stateName
    have dropProcess : process (.apply "PDrop" [.apply "NQuote" [quoted]]) = true :=
      process_iff.mpr ⟨rho_drop_hasSort nameTyped, by simpa [isObjectPattern, isObjectPatternList] using nameObject,
        (sealed_unary (by decide)).mpr nameSealed⟩
    obtain ⟨dropTyped, dropObject, dropSealed⟩ := process_iff.mp dropProcess
    have quoteDropName : name (.apply "NQuote" [.apply "PDrop" [.apply "NQuote" [quoted]]]) = true :=
      name_iff.mpr ⟨rho_quote_hasSort dropTyped, by simpa [isObjectPattern, isObjectPatternList] using dropObject,
        sealed_quote.mpr dropSealed⟩
    have dropCanon : canonicalize (.apply "PDrop" [.apply "NQuote" [quoted]]) =
        .apply "PDrop" [.apply "NQuote" [quoted]] := by
      rw [canonicalize_apply_general _ _ (by simp)]
      simp [canonicalizeList, canonState]
    refine ⟨[.apply "PDrop" [.apply "NQuote" [quoted]]], ⟨object, ?_⟩, by simp [domain_of_process dropProcess],
      by simp [dropCanon]⟩
    refine (objectEquivalent_iff admitted (by simp [domain, quoteDropName])).mpr ?_
    change canonicalize (.apply "NQuote" [quoted]) =
      normalizeQuote (canonicalize (.apply "PDrop" [.apply "NQuote" [quoted]]))
    rw [dropCanon, canonState]
    rfl

/-- **The types of an admitted canonical term are those of its kind.** -/
theorem typed_iff {state : Pattern} {type : TypeExpr} (admitted : domain state = true)
    (_ : canonicalizeSorted state = state) (admittedType : decide (type ∈ elementTypes) = true) :
    (typedAt state type = true ↔ (referenceStructure relEnv rhoCalc reading).typed state type) := by
  have member : type ∈ elementTypes := of_decide_eq_true admittedType
  have object : IsObject state := (canonical relEnv).object admitted
  simp only [elementTypes, List.mem_cons, List.not_mem_nil, or_false] at member
  constructor
  · intro typed
    refine ⟨object, state, Relation.EqvGen.refl _, carrierTyped_of_wellSorted ?_⟩
    rcases member with rfl | rfl | rfl <;>
      simp [typedAt, TypeExpr.proc, TypeExpr.name, TypeExpr.baseType] at typed
    · obtain ⟨typed, object, sealed⟩ := process_iff.mp typed
      exact ⟨typed, metadata_proc typed object, object, isWellScopedAt_of_binderSafeAt "NQuote" sealed⟩
    · obtain ⟨typed, object, sealed⟩ := name_iff.mp typed
      exact ⟨typed, metadata_name typed object, object, isWellScopedAt_of_binderSafeAt "NQuote" sealed⟩
    · obtain ⟨body, rfl, good⟩ := continuation_cases typed
      exact ⟨.lambda good.typed, by simpa [Pattern.hasCanonicalBinderMetadata] using metadata_proc good.typed good.object,
        by simpa [isObjectPattern] using good.object,
        by simpa [ScopeSafeAt, Pattern.isWellScopedAt] using isWellScopedAt_of_binderSafeAt "NQuote" good.formed⟩
  · rintro ⟨-, representative, equivalent, typedRepresentative⟩
    obtain ⟨typed, metadata, representativeObject, -⟩ := wellSorted_of_carrierTyped (by decide) typedRepresentative
    have representativeAdmitted := invariant admitted equivalent
    have sealed : Sealed 0 representative := by
      rcases formed_of_domain representativeAdmitted with formed | formed | formed <;> exact formed.formed
    obtain ⟨processes, names, continuations⟩ := kinds_of_equivalent equivalent
    rcases member with rfl | rfl | rfl
    · simp [typedAt, TypeExpr.proc, TypeExpr.name, TypeExpr.baseType,
        processes.mpr (process_iff.mpr ⟨typed, representativeObject, sealed⟩)]
    · simp [typedAt, TypeExpr.proc, TypeExpr.name, TypeExpr.baseType,
        names.mpr (name_iff.mpr ⟨typed, representativeObject, sealed⟩)]
    · obtain ⟨binder, body, rfl, good⟩ := lambda_of_arrow ⟨representativeObject, typed, sealed⟩
      cases binder with
      | none =>
        simp [typedAt, TypeExpr.proc, TypeExpr.name, TypeExpr.baseType,
          continuations.mpr (continuation_lambda_iff.mpr good)]
      | some _ => simp [Pattern.hasCanonicalBinderMetadata] at metadata

/-- **ρ's presentations, listed**, for its canonical forms. -/
def listing (relEnv : RelationEnv) : PresentationListing relEnv rhoCalc canonicalizeSorted domain reading where
  splits := splitsOf
  empty term kind := kind == .hashBag && term == .apply "PZero" []
  complete := splits_complete
  sound := splits_sound
  empty_iff := empty_iff
  constructors := constructorsOf
  builds := builds
  types type := decide (type ∈ elementTypes)
  typed := typedAt
  listed_constructor := listed_constructor
  builds_complete := builds_complete
  builds_sound := builds_sound
  typed_iff := typed_iff

/-- **ρ's presentation decider**: constructor formers, splits, emptiness and types modulo ρ's equations, over closed
presentation regions of its canonical forms. -/
def decider (relEnv : RelationEnv) (rounds : ℕ) : Decider relEnv rhoCalc reading :=
  presentedDecider (forms relEnv) (listing relEnv) rounds

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Rho
