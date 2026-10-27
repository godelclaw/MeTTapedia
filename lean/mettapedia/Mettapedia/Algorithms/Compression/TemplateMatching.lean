import Mettapedia.GSLT.LanguageDef.Gauthier.CanonicalPatternSchema

/-!
# Recovering arguments for canonical program templates

The existing role-indexed schema is the representation. Matching threads one
partial environment through all siblings (or both sides of a rule); a repeated
hole must agree with its first assignment. Operator and role admission belongs
to the signature checker. This layer does not turn a code hole into a value hole
and does not interpret an operator or execute the source program.

These are first-order ranked templates. Contextual binder templates use the
separate scoped matcher, not this representation with erased variable scope.
-/

namespace Mettapedia.Algorithms.Compression.TemplateMatching

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierRoleAntiUnification
open Mettapedia.GSLT.LanguageDef.GauthierCanonicalSchema

abbrev Environment := SchemaHole → Option Prog

def empty : Environment := fun _ => none

/-- Extending an environment may fill holes, but cannot replace assignments. -/
def Extends (after before : Environment) : Prop :=
  ∀ key value, before key = some value → after key = some value

theorem Extends.refl (env : Environment) : Extends env env := fun _ _ h => h

theorem Extends.trans {first second third : Environment}
    (h₁ : Extends second first) (h₂ : Extends third second) : Extends third first :=
  fun key value h => h₂ key value (h₁ key value h)

def assign (env : Environment) (key : SchemaHole) (value : Prog) : Option Environment :=
  match env key with
  | none => some (fun other => if other = key then some value else env other)
  | some old => if old = value then some env else none

theorem assign_sound {env next : Environment} {key : SchemaHole} {value : Prog}
    (found : assign env key value = some next) :
    Extends next env ∧ next key = some value := by
  unfold assign at found
  cases old : env key with
  | none =>
      simp only [old, Option.some.injEq] at found
      subst next
      constructor
      · intro other previous present
        by_cases same : other = key
        · subst other; simp [old] at present
        · simp [same, present]
      · simp
  | some previous =>
      simp only [old] at found
      split at found
      · rename_i same
        cases Option.some.inj found
        exact ⟨Extends.refl _, by simpa [same] using old⟩
      · cases found

mutual

def expand (env : Environment) : SchemaPattern → Option Prog
  | .hole role index => env (role, index)
  | .node op children => (expandList env children).map (.node op)

def expandList (env : Environment) : List SchemaPattern → Option (List Prog)
  | [] => some []
  | head :: tail => do
      let value ← expand env head
      let rest ← expandList env tail
      pure (value :: rest)

end

mutual

/-- One shared environment also serves a rewrite's left and right sides. -/
def matchPattern (env : Environment) : SchemaPattern → Prog → Option Environment
  | .hole role index, value => assign env (role, index) value
  | .node op children, .node actual values =>
      if op = actual then matchList env children values else none

def matchList (env : Environment) : List SchemaPattern → List Prog → Option Environment
  | [], [] => some env
  | head :: tail, value :: values => do
      let next ← matchPattern env head value
      matchList next tail values
  | _, _ => none

end

mutual

theorem expand_mono {before after : Environment} (extended : Extends after before) :
    ∀ (pattern : SchemaPattern) (value : Prog),
      expand before pattern = some value → expand after pattern = some value
  | .hole role index, value, found => extended _ value found
  | .node op children, value, found => by
      cases h : expandList before children with
      | none => simp [expand, h] at found
      | some values =>
          simp only [expand, h, Option.map_some, Option.some.injEq] at found
          subst value
          simp only [expand, expandList_mono extended children values h, Option.map_some]

theorem expandList_mono {before after : Environment} (extended : Extends after before) :
    ∀ (patterns : List SchemaPattern) (values : List Prog),
      expandList before patterns = some values → expandList after patterns = some values
  | [], values, found => found
  | head :: tail, values, found => by
      cases hh : expand before head with
      | none => simp [expandList, hh] at found
      | some value =>
          cases ht : expandList before tail with
          | none => simp [expandList, hh, ht] at found
          | some rest =>
              simp [expandList, hh, ht] at found
              subst values
              simp [expandList, expand_mono extended head value hh,
                expandList_mono extended tail rest ht]

end

mutual

/-- The actual matcher constructs a reconstructing environment and preserves
every assignment present at entry. No reconstruction premise is required. -/
theorem matchPattern_sound : ∀ (env next : Environment) (pattern : SchemaPattern)
    (value : Prog), matchPattern env pattern value = some next →
      Extends next env ∧ expand next pattern = some value
  | env, next, .hole role index, value, found => assign_sound found
  | env, next, .node op children, .node actual values, found => by
      simp only [matchPattern] at found
      by_cases same : op = actual
      · subst actual
        simp at found
        obtain ⟨extended, reconstructed⟩ := matchList_sound env next children values found
        exact ⟨extended, by simp [expand, reconstructed]⟩
      · simp [same] at found

theorem matchList_sound : ∀ (env next : Environment) (patterns : List SchemaPattern)
    (values : List Prog), matchList env patterns values = some next →
      Extends next env ∧ expandList next patterns = some values
  | env, next, [], [], found => by
      cases Option.some.inj found
      exact ⟨Extends.refl _, rfl⟩
  | _, _, [], _ :: _, found => by cases found
  | _, _, _ :: _, [], found => by cases found
  | env, next, head :: tail, value :: values, found => by
      cases hm : matchPattern env head value with
      | none => simp [matchList, hm] at found
      | some middle =>
          simp [matchList, hm] at found
          obtain ⟨first, headResult⟩ := matchPattern_sound env middle head value hm
          obtain ⟨second, tailResult⟩ := matchList_sound middle next tail values found
          exact ⟨first.trans second, by
            simp [expandList, expand_mono second head value headResult, tailResult]⟩

end

/-- Supplying an already consistent assignment succeeds without rebinding it. -/
theorem assign_existing (env : Environment) (key : SchemaHole) (value : Prog)
    (present : env key = some value) : assign env key value = some env := by
  simp [assign, present]

mutual

theorem matchPattern_existing (env : Environment) :
    ∀ (pattern : SchemaPattern) (value : Prog), expand env pattern = some value →
      matchPattern env pattern value = some env
  | .hole role index, value, found => assign_existing env _ value found
  | .node op children, value, found => by
      cases h : expandList env children with
      | none => simp [expand, h] at found
      | some values =>
          simp only [expand, h, Option.map_some, Option.some.injEq] at found
          subst value
          simp [matchPattern, matchList_existing env children values h]

theorem matchList_existing (env : Environment) :
    ∀ (patterns : List SchemaPattern) (values : List Prog),
      expandList env patterns = some values → matchList env patterns values = some env
  | [], values, found => by cases Option.some.inj found; rfl
  | head :: tail, values, found => by
      cases hh : expand env head with
      | none => simp [expandList, hh] at found
      | some value =>
          cases ht : expandList env tail with
          | none => simp [expandList, hh, ht] at found
          | some rest =>
              simp [expandList, hh, ht] at found
              subst values
              simp [matchList, matchPattern_existing env head value hh,
                matchList_existing env tail rest ht]

end

/-- Matching can discover a consistent assignment, not merely recheck an
environment that already contains every answer. -/
theorem assign_complete {env witness : Environment} (consistent : Extends witness env)
    (key : SchemaHole) (value : Prog) (present : witness key = some value) :
    ∃ next, assign env key value = some next ∧ Extends witness next := by
  cases old : env key with
  | none =>
      refine ⟨fun other => if other = key then some value else env other, ?_, ?_⟩
      · simp [assign, old]
      · intro other result found
        by_cases same : other = key
        · subst other
          simp at found
          simpa [← found] using present
        · simp only [if_neg same] at found
          exact consistent other result found
  | some result =>
      have equal : result = value := Option.some.inj ((consistent key result old).symm.trans present)
      subst result
      exact ⟨env, assign_existing env key value old, consistent⟩

mutual

theorem matchPattern_complete : ∀ (env witness : Environment), Extends witness env →
    ∀ (pattern : SchemaPattern) (value : Prog), expand witness pattern = some value →
      ∃ next, matchPattern env pattern value = some next ∧ Extends witness next
  | env, witness, consistent, .hole role index, value, found =>
      assign_complete consistent _ value found
  | env, witness, consistent, .node op children, value, found => by
      cases expanded : expandList witness children with
      | none => simp [expand, expanded] at found
      | some values =>
          simp only [expand, expanded, Option.map_some, Option.some.injEq] at found
          subst value
          obtain ⟨next, matched, agrees⟩ :=
            matchList_complete env witness consistent children values expanded
          exact ⟨next, by simpa [matchPattern] using matched, agrees⟩

theorem matchList_complete : ∀ (env witness : Environment), Extends witness env →
    ∀ (patterns : List SchemaPattern) (values : List Prog),
      expandList witness patterns = some values →
      ∃ next, matchList env patterns values = some next ∧ Extends witness next
  | env, _, consistent, [], values, found => by
      cases Option.some.inj found
      exact ⟨env, rfl, consistent⟩
  | env, witness, consistent, head :: tail, values, found => by
      cases hh : expand witness head with
      | none => simp [expandList, hh] at found
      | some value =>
          cases ht : expandList witness tail with
          | none => simp [expandList, hh, ht] at found
          | some rest =>
              simp [expandList, hh, ht] at found
              subst values
              obtain ⟨middle, matchedHead, middleAgrees⟩ :=
                matchPattern_complete env witness consistent head value hh
              obtain ⟨next, matchedTail, nextAgrees⟩ :=
                matchList_complete middle witness middleAgrees tail rest ht
              exact ⟨next, by simp [matchList, matchedHead, matchedTail], nextAgrees⟩

end

theorem match_from_empty_iff (pattern : SchemaPattern) (value : Prog) :
    (∃ next, matchPattern empty pattern value = some next) ↔
      ∃ witness, expand witness pattern = some value := by
  constructor
  · rintro ⟨next, found⟩
    exact ⟨next, (matchPattern_sound empty next pattern value found).2⟩
  · rintro ⟨witness, reconstructed⟩
    have consistent : Extends witness empty := by
      intro key previous found
      cases found
    obtain ⟨next, found, _⟩ :=
      matchPattern_complete empty witness consistent pattern value reconstructed
    exact ⟨next, found⟩

/-- A canonical occurrence coordinate reads a projected disagreement pair.
Role checking is retained even though the index was generated canonically. -/
def occurrenceEnvironment (substitution : TermSubstitution)
    (occurrences : List HoleKey) : Environment := fun (role, index) =>
  match occurrences[index]? with
  | none => none
  | some key => if key.role = role then some (substitution key) else none

mutual

theorem expand_occurrenceEnvironment (substitution : TermSubstitution)
    (occurrences : List HoleKey) : ∀ pattern,
    expand (occurrenceEnvironment substitution occurrences) pattern =
      (reconstructWith occurrences pattern).map (instantiate substitution)
  | .hole role index => by
      cases read : occurrences[index]? with
      | none => simp [expand, occurrenceEnvironment, reconstructWith, read]
      | some key =>
          by_cases same : key.role = role <;>
            simp [expand, occurrenceEnvironment, reconstructWith, read, same, instantiate]
  | .node op children => by
      simp only [expand, reconstructWith, expandList_occurrenceEnvironment]
      cases read : reconstructListWith occurrences children <;> simp [instantiate]

theorem expandList_occurrenceEnvironment (substitution : TermSubstitution)
    (occurrences : List HoleKey) : ∀ patterns,
    expandList (occurrenceEnvironment substitution occurrences) patterns =
      (reconstructListWith occurrences patterns).map (List.map (instantiate substitution))
  | [] => rfl
  | head :: tail => by
      simp only [expandList, reconstructListWith, expand_occurrenceEnvironment,
        expandList_occurrenceEnvironment]
      cases hh : reconstructWith occurrences head <;>
        cases ht : reconstructListWith occurrences tail <;> simp

end

theorem canonical_reconstructs (substitution : TermSubstitution) (pattern : Pattern) :
    expand (occurrenceEnvironment substitution (holeOccurrences pattern))
      (canonicalSchema pattern) = some (instantiate substitution pattern) := by
  rw [expand_occurrenceEnvironment, reconstructWith_canonicalSchema]
  rfl

/-- Pairwise generalization is a sound source of seeds for this matcher.
This theorem makes no assertion that pairwise seeds exhaust useful templates. -/
theorem pairwise_seed_matches (sig : Mettapedia.GSLT.LanguageDef.GauthierE1.Signature σ)
    (role : HoleRole) (left right : Prog) :
    (∃ env, matchPattern empty (canonicalSchema (lgg sig role left right)) left = some env) ∧
    (∃ env, matchPattern empty (canonicalSchema (lgg sig role left right)) right = some env) := by
  constructor
  · apply (match_from_empty_iff _ _).mpr
    refine ⟨occurrenceEnvironment leftSubstitution (holeOccurrences (lgg sig role left right)), ?_⟩
    rw [canonical_reconstructs, instantiate_left_lgg]
  · apply (match_from_empty_iff _ _).mpr
    refine ⟨occurrenceEnvironment rightSubstitution (holeOccurrences (lgg sig role left right)), ?_⟩
    rw [canonical_reconstructs, instantiate_right_lgg]

/-- A successful shared-hole match cannot hide unequal source occurrences. -/
theorem repeated_hole_equal {env next : Environment} {key : SchemaHole} {left right : Prog}
    (found : matchList env [.hole key.1 key.2, .hole key.1 key.2] [left, right] = some next) :
    left = right := by
  have reconstructed := (matchList_sound env next _ _ found).2
  cases bound : next key with
  | none => simp [expandList, expand, bound] at reconstructed
  | some value =>
      have equal : value = left ∧ value = right := by
        simpa [expandList, expand, bound] using reconstructed
      exact equal.1.symm.trans equal.2

/-! Positive and negative executable controls. -/

def repeated : SchemaPattern := .node 2 [.hole .value 0, .hole .value 0]

example : (matchPattern empty repeated (.node 2 [.node 0 [], .node 0 []])).isSome = true := by
  simp [matchPattern, matchList, assign, empty, repeated]

example : (matchPattern empty repeated (.node 2 [.node 0 [], .node 1 []])).isSome = false := by
  simp [matchPattern, matchList, assign, empty, repeated]

example : (matchList empty [.hole .code 0, .hole .value 0] [.node 0 [], .node 1 []]).isSome = true := by
  simp [matchPattern, matchList, assign, empty]

example : (matchList empty [.hole .value 0, .hole .value 0] [.node 0 [], .node 1 []]).isSome = false := by
  simp [matchPattern, matchList, assign, empty]

example : (matchPattern empty (.node 2 [.hole .value 0]) (.node 2 [])).isSome = false := by
  simp [matchPattern, matchList]

end Mettapedia.Algorithms.Compression.TemplateMatching
