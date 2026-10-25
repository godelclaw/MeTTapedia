import Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra

/-!
# Queries over annotated spaces: multiplicity policies, freezing, dictionaries
and key indexes

A space annotated in a semiring `K` (`Space K Atom`) answers a pattern by
binding each stored atom to what the matcher makes of it: the query is the
weighted bind of the space with the match (`query`). A matcher returns at
most one answer per stored atom, as syntactic matching of one pattern against
one atom does.

* **Multiplicity policy as an observation quotient.** A change of annotation
  along a semiring homomorphism commutes with every query (`mapK_query`).
  The set policy is the change `ℕ → Presence`: its observations of a bag space
  are exactly the presence of the bag observations (`setObservation_query`),
  and two bag spaces have the same set observations exactly when they store
  the same atoms (`setEquivalent_iff`). Bag observations are finer
  (`Controls.bag_observation_finer`).
* **`add-atom-nodup` realizes the set policy on bag spaces.** It has the set
  observations of `add-atom` (`setOf_addNodup`), keeps a space duplicate-free
  (`setShaped_addNodup`; `add-atom` does not, `Controls.add_breaks_setShaped`),
  and on duplicate-free bag spaces the set view is injective
  (`setOf_injective_on_setShaped`).
* **Freezing** a bag space to a bag value is exact (`toFinsupp_freezeBag`);
  freezing to a set value forgets counts and agrees with the set view
  (`freezeSet_eq`).
* **Dictionary spaces.** CeTTa's space API has several kinds (atom, stack,
  queue, hash) over several engines; a dict space is a kind whose key-value
  facility (`getValue`, `setValue`) sits beside the common operations. That
  facility agrees with the common `match` exactly when the space stores at
  most one value per key: a space of key-value pairs is functional when each
  key has at most one stored value. Lookup is
  the query of the pattern `(k, $v)` (`getValue`). A single-valued index
  describing the space exists exactly when the space is functional
  (`exists_describes_iff_functional`), and then indexed lookup equals the
  query (`getValue_eq_index`). `setValue` keeps a space functional; adding a
  second pair under a key does not (`Controls.two_values_one_key`).
* **A key index is an acceleration.** When a pattern's rigid key is sound for
  the matcher, querying only the atoms filed under that key gives the same
  answers as querying the whole space (`indexedQuery_eq_query`), and the
  filing is additive, so it is maintained under insertion
  (`keyFilter_add`). A key that the matcher does not respect loses answers
  (`Controls.unsound_key_loses_answers`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceQueryPolicy

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra

universe u

variable {K : Type u} {Atom Pat Res : Type*}

/-! ## Queries -/

section Query

variable [Semiring K] (matcher : Pat → Atom → Option Res)

/-- What one stored atom contributes to the answers of a pattern. -/
noncomputable def contribution (pattern : Pat) (atom : Atom) : Ans K Res :=
  match matcher pattern atom with
  | some result => Ans.pure result
  | none => 0

/-- The answers of a pattern: the space bound to the match. -/
noncomputable def query (space : Space K Atom) (pattern : Pat) : Ans K Res :=
  Ans.bind space (contribution matcher pattern)

theorem query_add (left right : Space K Atom) (pattern : Pat) :
    query matcher (left + right) pattern =
      query matcher left pattern + query matcher right pattern :=
  Ans.add_bind left right _

theorem query_single (atom : Atom) (weight : K) (pattern : Pat) :
    query matcher (Finsupp.single atom weight) pattern =
      weight • contribution matcher pattern atom :=
  Ans.single_bind atom weight _

theorem query_zero (pattern : Pat) : query matcher (0 : Space K Atom) pattern = 0 := by
  simp [query, Ans.bind]

/-- A change of annotation commutes with every query. -/
theorem mapK_query {L : Type*} [Semiring L] (φ : K →+* L) (space : Space K Atom)
    (pattern : Pat) :
    Ans.mapK φ (query matcher space pattern) =
      query matcher (Ans.mapK φ space) pattern := by
  unfold query
  rw [Ans.mapK_bind]
  congr 1
  funext atom
  unfold contribution
  cases matcher pattern atom with
  | some result => exact Ans.mapK_pure φ result
  | none => ext; simp

end Query

/-! ## The set policy as an observation quotient -/

section SetPolicy

variable (matcher : Pat → Atom → Option Res)

/-- The set view of a bag space: which atoms are stored. -/
noncomputable def setOf (space : Space ℕ Atom) : Space Presence Atom :=
  Ans.mapK supportOfCount space

theorem setOf_apply (space : Space ℕ Atom) (atom : Atom) :
    (setOf space atom).present = decide (space atom ≠ 0) := rfl

/-- Set observations of a bag space are the presence of its bag
observations. -/
theorem setObservation_query (space : Space ℕ Atom) (pattern : Pat) :
    Ans.mapK supportOfCount (query matcher space pattern) =
      query matcher (setOf space) pattern :=
  mapK_query matcher supportOfCount space pattern

theorem setOf_eq_iff (left right : Space ℕ Atom) :
    setOf left = setOf right ↔ left.support = right.support := by
  constructor
  · intro same
    ext atom
    have := congrArg (fun space : Space Presence Atom => (space atom).present) same
    simp only [setOf_apply, decide_eq_decide] at this
    simpa [Finsupp.mem_support_iff] using this
  · intro same
    ext atom
    have member := congrArg (atom ∈ ·) same
    simp only [Finsupp.mem_support_iff, eq_iff_iff] at member
    simp only [setOf_apply, member]

/-- A pattern matching every atom and answering it by `embed` reads the
space back, renamed. -/
theorem query_identity [Semiring K] (identity : Pat) (embed : Atom → Res)
    (matchesAll : ∀ atom, matcher identity atom = some (embed atom)) (space : Space K Atom) :
    query matcher space identity = Finsupp.mapDomain embed space := by
  unfold query Ans.bind
  simp only [contribution, matchesAll, Ans.pure, Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

/-- Set-observational equivalence: every pattern has the same set of
answers. -/
def SetEquivalent (left right : Space ℕ Atom) : Prop :=
  ∀ pattern, Ans.mapK supportOfCount (query matcher left pattern) =
    Ans.mapK supportOfCount (query matcher right pattern)

/-- With a pattern that matches every atom and answers it injectively (a
variable), set-observational equivalence identifies exactly the bag spaces
that store the same atoms: the set policy is this quotient. -/
theorem setEquivalent_iff (identity : Pat) (embed : Atom → Res)
    (injective : Function.Injective embed)
    (matchesAll : ∀ atom, matcher identity atom = some (embed atom))
    (left right : Space ℕ Atom) :
    SetEquivalent matcher left right ↔ left.support = right.support := by
  constructor
  · intro equivalent
    rw [← setOf_eq_iff]
    have observed := equivalent identity
    rw [setObservation_query, setObservation_query, query_identity matcher identity embed matchesAll,
      query_identity matcher identity embed matchesAll] at observed
    exact Finsupp.mapDomain_injective injective observed
  · intro same pattern
    rw [setObservation_query, setObservation_query, (setOf_eq_iff left right).mpr same]

/-- `add-atom-nodup`: insert an atom unless it is already stored. -/
noncomputable def addNodup [DecidableEq Atom] (space : Space ℕ Atom) (atom : Atom) :
    Space ℕ Atom :=
  if space atom = 0 then space + Finsupp.single atom 1 else space

theorem setOf_addNodup [DecidableEq Atom] (space : Space ℕ Atom) (atom : Atom) :
    setOf (addNodup space atom) = setOf (space + Finsupp.single atom 1) := by
  rw [setOf_eq_iff]
  unfold addNodup
  split_ifs with absent
  · rfl
  · ext stored
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply]
    by_cases same : atom = stored
    · subst same
      simp [absent]
    · simp [same]

/-- A bag space storing each atom at most once. -/
def SetShaped (space : Space ℕ Atom) : Prop := ∀ atom, space atom ≤ 1

theorem setShaped_addNodup [DecidableEq Atom] {space : Space ℕ Atom}
    (shaped : SetShaped space) (atom : Atom) : SetShaped (addNodup space atom) := by
  intro stored
  unfold addNodup
  split_ifs with absent
  · simp only [Finsupp.add_apply, Finsupp.single_apply]
    by_cases same : atom = stored
    · subst same
      simp [absent]
    · simpa [same] using shaped stored
  · exact shaped stored

/-- On duplicate-free bag spaces the set view loses nothing. -/
theorem setOf_injective_on_setShaped {left right : Space ℕ Atom}
    (leftShaped : SetShaped left) (rightShaped : SetShaped right)
    (same : setOf left = setOf right) : left = right := by
  rw [setOf_eq_iff] at same
  ext atom
  have member := congrArg (atom ∈ ·) same
  simp only [Finsupp.mem_support_iff, eq_iff_iff] at member
  have leftBound := leftShaped atom
  have rightBound := rightShaped atom
  omega

end SetPolicy

/-! ## Freezing a space into a collection value -/

section Freeze

/-- Freeze a bag space into a bag value. -/
noncomputable def freezeBag (space : Space ℕ Atom) : Multiset Atom := Finsupp.toMultiset space

/-- Freeze a space into a set value: the stored atoms. -/
def freezeSet (space : Space ℕ Atom) : Finset Atom := space.support

/-- Freezing a bag space loses nothing. -/
theorem toFinsupp_freezeBag [DecidableEq Atom] (space : Space ℕ Atom) :
    Multiset.toFinsupp (freezeBag space) = space :=
  Finsupp.toMultiset_toFinsupp space

/-- Freezing to a set forgets the counts of the frozen bag. -/
theorem freezeSet_eq [DecidableEq Atom] (space : Space ℕ Atom) :
    freezeSet space = (freezeBag space).toFinset :=
  (Finsupp.toFinset_toMultiset space).symm

end Freeze

/-! ## Dictionary spaces: the key-value facility and its conformance with `match` -/

section Dictionary

variable {Key Val : Type*} [DecidableEq Key]

/-- The matcher of the pattern `(key, $value)`. -/
def keyMatcher (key : Key) (pair : Key × Val) : Option Val :=
  if pair.1 = key then some pair.2 else none

/-- Lookup of a key: the query of `(key, $value)`. -/
noncomputable def getValue [Semiring K] (space : Space K (Key × Val)) (key : Key) : Ans K Val :=
  query keyMatcher space key

/-- Each key has at most one stored value. -/
def Functional [Zero K] (space : Space K (Key × Val)) : Prop :=
  ∀ key first second, space (key, first) ≠ 0 → space (key, second) ≠ 0 → first = second

/-- A single-valued index describes a space when it names exactly the stored
value of each key. -/
def Describes [Zero K] (index : Key → Option Val) (space : Space K (Key × Val)) : Prop :=
  ∀ key value, index key = some value ↔ space (key, value) ≠ 0

omit [DecidableEq Key] in
theorem exists_describes_iff_functional [Zero K] (space : Space K (Key × Val)) :
    (∃ index : Key → Option Val, Describes index space) ↔ Functional space := by
  constructor
  · rintro ⟨index, describes⟩ key first second firstStored secondStored
    have := ((describes key first).mpr firstStored).symm.trans ((describes key second).mpr secondStored)
    exact Option.some.inj this
  · intro functional
    classical
    refine ⟨fun key => if stored : ∃ value, space (key, value) ≠ 0 then some stored.choose
      else none, ?_⟩
    intro key value
    by_cases stored : ∃ value, space (key, value) ≠ 0
    · simp only [stored, dite_true, Option.some.injEq]
      constructor
      · rintro rfl
        exact stored.choose_spec
      · intro valueStored
        exact functional key _ _ stored.choose_spec valueStored
    · simp only [stored, dite_false]
      constructor
      · intro impossible
        cases impossible
      · intro valueStored
        exact absurd ⟨value, valueStored⟩ stored

theorem contribution_keyMatcher [Semiring K] (key : Key) (pair : Key × Val) :
    contribution (K := K) keyMatcher key pair = if pair.1 = key then Ans.pure pair.2 else 0 := by
  unfold contribution keyMatcher
  split_ifs <;> rfl

/-- Lookup answers each value with the annotation of its pair, for every
space. -/
theorem getValue_apply [Semiring K] (space : Space K (Key × Val)) (key : Key) (value : Val) :
    getValue space key value = space (key, value) := by
  classical
  simp only [getValue, query, Ans.bind_apply, contribution_keyMatcher]
  rw [Finsupp.sum, Finset.sum_eq_single (key, value)]
  · simp [Ans.pure]
  · rintro ⟨storedKey, storedValue⟩ _ different
    by_cases sameKey : storedKey = key
    · subst sameKey
      have : storedValue ≠ value := fun same => different (by rw [same])
      simp [Ans.pure, this]
    · simp [sameKey]
  · intro absent
    simp [Finsupp.notMem_support_iff.mp absent]

/-- Indexed lookup equals the query of `(key, $value)`. -/
theorem getValue_eq_index [Semiring K] (space : Space K (Key × Val)) (index : Key → Option Val)
    (describes : Describes index space) (key : Key) :
    getValue space key = match index key with
      | some value => Finsupp.single value (space (key, value))
      | none => 0 := by
  classical
  ext answer
  rw [getValue_apply]
  cases indexed : index key with
  | none =>
      by_contra stored
      exact absurd ((describes key answer).mpr stored) (by simp [indexed])
  | some value =>
      simp only [Finsupp.single_apply]
      split_ifs with same
      · rw [same]
      · by_contra stored
        have := (describes key answer).mpr stored
        rw [indexed, Option.some.injEq] at this
        exact same this

/-- Replace the value of a key. -/
noncomputable def setValue [DecidableEq Val] (space : Space ℕ (Key × Val)) (key : Key)
    (value : Val) : Space ℕ (Key × Val) :=
  space.filter (fun pair => pair.1 ≠ key) + Finsupp.single (key, value) 1

theorem functional_setValue [DecidableEq Val] {space : Space ℕ (Key × Val)}
    (functional : Functional space) (key : Key) (value : Val) :
    Functional (setValue space key value) := by
  intro stored first second firstStored secondStored
  by_cases same : stored = key
  · subst same
    have onlyValue : ∀ candidate, setValue space stored value (stored, candidate) ≠ 0 →
        candidate = value := by
      intro candidate isStored
      by_contra different
      apply isStored
      simp [setValue, Ne.symm different]
    rw [onlyValue first firstStored, onlyValue second secondStored]
  · have unchanged : ∀ candidate,
        setValue space key value (stored, candidate) = space (stored, candidate) := by
      intro candidate
      simp [setValue, same]
    rw [unchanged] at firstStored secondStored
    exact functional stored first second firstStored secondStored

end Dictionary

/-! ## Key indexes -/

section KeyIndex

variable [Semiring K] {κ : Type*} [DecidableEq κ] (matcher : Pat → Atom → Option Res)

/-- The atoms filed under a key. -/
noncomputable def keyFilter (keyOf : Atom → κ) (space : Space K Atom) (key : κ) : Space K Atom :=
  space.filter fun atom => keyOf atom = key

/-- Filing is additive, so an index is maintained under insertion. -/
theorem keyFilter_add (keyOf : Atom → κ) (left right : Space K Atom) (key : κ) :
    keyFilter keyOf (left + right) key = keyFilter keyOf left key + keyFilter keyOf right key :=
  Finsupp.filter_add

/-- A rigid key is sound when every atom the pattern matches is filed under it. -/
def KeySound (keyOf : Atom → κ) (patternKey : Pat → Option κ) : Prop :=
  ∀ pattern atom result key, matcher pattern atom = some result →
    patternKey pattern = some key → keyOf atom = key

/-- Query only the atoms filed under the pattern's rigid key, if it has one. -/
noncomputable def indexedQuery (keyOf : Atom → κ) (patternKey : Pat → Option κ)
    (space : Space K Atom) (pattern : Pat) : Ans K Res :=
  match patternKey pattern with
  | some key => query matcher (keyFilter keyOf space key) pattern
  | none => query matcher space pattern

/-- An index changes where answers are found, never which answers there are. -/
theorem indexedQuery_eq_query (keyOf : Atom → κ) (patternKey : Pat → Option κ)
    (sound : KeySound matcher keyOf patternKey) (space : Space K Atom) (pattern : Pat) :
    indexedQuery matcher keyOf patternKey space pattern = query matcher space pattern := by
  unfold indexedQuery
  cases rigid : patternKey pattern with
  | none => rfl
  | some key =>
      simp only
      conv_rhs => rw [← Finsupp.filter_add_filter_not space (fun atom => keyOf atom = key)]
      rw [query_add]
      suffices outside : query matcher (space.filter fun atom => ¬ keyOf atom = key) pattern = 0 by
        rw [outside, add_zero]
        rfl
      unfold query Ans.bind
      rw [Finsupp.sum, Finset.sum_eq_zero]
      intro atom member
      rw [Finsupp.support_filter, Finset.mem_filter] at member
      unfold contribution
      cases matched : matcher pattern atom with
      | none => simp
      | some result => exact absurd (sound pattern atom result key matched rigid) member.2

end KeyIndex

/-! ## Controls -/

namespace Controls

/-- The identity matcher: the pattern `$x`, answering each atom. -/
def identity (_ : Unit) (atom : ℕ) : Option ℕ := some atom

/-- Bag observations are finer than set observations: storing an atom once
or twice has the same set answers and different counts. -/
theorem bag_observation_finer :
    SetEquivalent identity (Finsupp.single 7 1 : Space ℕ ℕ) (Finsupp.single 7 2) ∧
      query identity (Finsupp.single 7 1 : Space ℕ ℕ) () ≠
        query identity (Finsupp.single 7 2 : Space ℕ ℕ) () := by
  constructor
  · rw [setEquivalent_iff identity () id Function.injective_id (fun _ => rfl)]
    simp [Finsupp.support_single]
  · intro same
    have := congrArg (fun answers : Ans ℕ ℕ => answers 7) same
    simp [query_single, contribution, identity, Ans.pure] at this

/-- `add-atom` breaks duplicate-freedom; `add-atom-nodup` keeps it. -/
theorem add_breaks_setShaped :
    ¬ SetShaped ((Finsupp.single 7 1 : Space ℕ ℕ) + Finsupp.single 7 1) ∧
      SetShaped (addNodup (Finsupp.single 7 1 : Space ℕ ℕ) 7) := by
  constructor
  · intro shaped
    have := shaped 7
    simp at this
  · apply setShaped_addNodup
    intro atom
    simp only [Finsupp.single_apply]
    split_ifs <;> omega

/-- Two values under one key: lookup answers both, and no single-valued
index describes the space. -/
theorem two_values_one_key :
    let space : Space ℕ (ℕ × ℕ) := Finsupp.single (0, 1) 1 + Finsupp.single (0, 2) 1
    ¬ Functional space ∧ (getValue space 0 1 = 1 ∧ getValue space 0 2 = 1) := by
  intro space
  refine ⟨fun functional => by
    have := functional 0 1 2 (by simp [space]) (by simp [space])
    omega, ?_⟩
  simp [space, getValue_apply]

/-- A key the matcher does not respect: the pattern `(k, $v)` claims key `0`
while it also matches atoms filed under `1`, so the index loses an answer. -/
theorem unsound_key_loses_answers :
    let matcher : Unit → ℕ × ℕ → Option ℕ := fun _ pair => some pair.2
    let space : Space ℕ (ℕ × ℕ) := Finsupp.single (1, 5) 1
    indexedQuery matcher Prod.fst (fun _ => some 0) space () ≠ query matcher space () := by
  intro matcher space same
  have := congrArg (fun answers : Ans ℕ ℕ => answers 5) same
  rw [show indexedQuery matcher Prod.fst (fun _ => some 0) space () =
      query matcher (keyFilter Prod.fst space 0) () from rfl,
    show keyFilter Prod.fst space 0 = 0 from
      Finsupp.filter_single_of_neg (p := fun pair : ℕ × ℕ => pair.1 = 0) (by simp),
    query_zero] at this
  simp [space, query_single, contribution, matcher, Ans.pure] at this

end Controls

end Mettapedia.Languages.MeTTa.SpaceQueryPolicy
