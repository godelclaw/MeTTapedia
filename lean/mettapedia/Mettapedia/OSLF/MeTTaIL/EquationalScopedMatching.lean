import Mettapedia.OSLF.MeTTaIL.ScopedCollectionMatching

/-!
# Recursive scoped matching with collection equality

Every unordered collection uses the finite bag/set allocator. Vectors remain
positional. Captures use the original authored occurrence and binder metadata;
the repeated-body comparison is an explicit policy.

The independent meaning quantifies over collection decompositions satisfying
`Presents`. It does not refer to the finite allocator. Collection equality here
is permutation or membership equality, not arbitrary authored equations,
flattening, scope extrusion, or a normalization-coherence certificate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EquationalScopedMatching

open Syntax RuleBinding ScopedRuleMatching CanonicalBags CollectionSelection

abbrev Comparison := String → Pattern → Pattern → Bool

def finish (compare : Comparison) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth index : Nat)
    (rest : Option String) (kind : CollType) (initial : Assignment)
    (targets : List Pattern) : List Assignment :=
  match rest with
  | none => if targets.isEmpty then [initial] else []
  | some name =>
      (captureRestWith? compare rule spec ambient depth site (path ++ [index])
        initial name kind targets).toList

def Finished (compare : Comparison) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth index : Nat)
    (rest : Option String) (kind : CollType) (initial : Assignment)
    (targets : List Pattern) (final : Assignment) : Prop :=
  match rest with
  | none => targets = [] ∧ final = initial
  | some name =>
      captureRestWith? compare rule spec ambient depth site (path ++ [index])
        initial name kind targets = some final

theorem finish_exact (compare : Comparison) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth index : Nat)
    (rest : Option String) (kind : CollType) (initial final : Assignment) (targets : List Pattern) :
    final ∈ finish compare rule spec ambient site path depth index rest kind initial targets ↔
      Finished compare rule spec ambient site path depth index rest kind initial targets final := by
  cases rest <;> simp [finish, Finished]

mutual
def runAt (compare : Comparison) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (initial : Assignment) : Pattern → Pattern → List Assignment
  | .fvar name, target =>
      (captureWith? compare rule spec ambient depth site path initial name target).toList
  | .bvar expected, .bvar actual => if expected = actual then [initial] else []
  | .apply label schemas, .apply actual targets =>
      if label = actual then runArguments compare rule spec ambient site path depth initial 0 schemas targets else []
  | .lambda _ body, .lambda _ target =>
      runAt compare rule spec ambient site (path ++ [0]) (depth + 1) initial body target
  | .multiLambda arity _ body, .multiLambda actual _ target =>
      if arity = actual then
        runAt compare rule spec ambient site (path ++ [0]) (depth + arity) initial body target
      else []
  | .subst body replacement, .subst targetBody targetReplacement =>
      (runAt compare rule spec ambient site (path ++ [0]) (depth + 1) initial body targetBody).flatMap
        fun middle => runAt compare rule spec ambient site (path ++ [1]) depth middle replacement targetReplacement
  | .collection kind schemas rest, .collection actualKind targets actualRest =>
      if kind = actualKind ∧ actualRest = none then
        if kind = .vec then
          match rest with
          | none => runArguments compare rule spec ambient site path depth initial 0 schemas targets
          | some name =>
              (runArguments compare rule spec ambient site path depth initial 0 schemas
                (targets.take schemas.length)).filterMap fun middle =>
                  captureRestWith? compare rule spec ambient depth site (path ++ [schemas.length])
                    middle name kind (targets.drop schemas.length)
        else
          (kindAllocations kind schemas.length (arrange kind targets)).flatMap fun (values, residual) =>
            (runArguments compare rule spec ambient site path depth initial 0 schemas values).flatMap
              fun middle => finish compare rule spec ambient site path depth schemas.length rest kind
                middle (arrange kind residual)
      else []
  | _, _ => []
termination_by schema _ => sizeOf schema
decreasing_by all_goals sizeOf_pattern_dec

def runArguments (compare : Comparison) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (initial : Assignment) (index : Nat) : List Pattern → List Pattern → List Assignment
  | [], [] => [initial]
  | schema :: schemas, target :: targets =>
      (runAt compare rule spec ambient site (path ++ [index]) depth initial schema target).flatMap
        fun middle => runArguments compare rule spec ambient site path depth middle (index + 1) schemas targets
  | _, _ => []
termination_by schemas _ => sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec
end

mutual
def Meaning (compare : Comparison) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (initial : Assignment) : Pattern → Pattern → Assignment → Prop
  | .fvar name, target, final =>
      captureWith? compare rule spec ambient depth site path initial name target = some final
  | .bvar expected, .bvar actual, final => expected = actual ∧ final = initial
  | .apply label schemas, .apply actual targets, final =>
      label = actual ∧ ArgumentsMeaning compare rule spec ambient site path depth initial 0 schemas targets final
  | .lambda _ body, .lambda _ target, final =>
      Meaning compare rule spec ambient site (path ++ [0]) (depth + 1) initial body target final
  | .multiLambda arity _ body, .multiLambda actual _ target, final =>
      arity = actual ∧
        Meaning compare rule spec ambient site (path ++ [0]) (depth + arity) initial body target final
  | .subst body replacement, .subst targetBody targetReplacement, final =>
      ∃ middle, Meaning compare rule spec ambient site (path ++ [0]) (depth + 1) initial body targetBody middle ∧
        Meaning compare rule spec ambient site (path ++ [1]) depth middle replacement targetReplacement final
  | .collection kind schemas rest, .collection actualKind targets actualRest, final =>
      kind = actualKind ∧ actualRest = none ∧
        if kind = .vec then
          match rest with
          | none => ArgumentsMeaning compare rule spec ambient site path depth initial 0 schemas targets final
          | some name =>
              ∃ middle, ArgumentsMeaning compare rule spec ambient site path depth initial 0 schemas
                (targets.take schemas.length) middle ∧
                captureRestWith? compare rule spec ambient depth site (path ++ [schemas.length])
                  middle name kind (targets.drop schemas.length) = some final
        else
          ∃ values residual middle, Presents kind targets (values ++ residual) ∧
            ArgumentsMeaning compare rule spec ambient site path depth initial 0 schemas values middle ∧
            Finished compare rule spec ambient site path depth schemas.length rest kind middle
              (arrange kind residual) final
  | _, _, _ => False
termination_by schema _ _ => sizeOf schema
decreasing_by all_goals sizeOf_pattern_dec

def ArgumentsMeaning (compare : Comparison) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (initial : Assignment) (index : Nat) : List Pattern → List Pattern → Assignment → Prop
  | [], [], final => final = initial
  | schema :: schemas, target :: targets, final =>
      ∃ middle, Meaning compare rule spec ambient site (path ++ [index]) depth initial schema target middle ∧
        ArgumentsMeaning compare rule spec ambient site path depth middle (index + 1) schemas targets final
  | _, _, _ => False
termination_by schemas _ _ => sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec
end

theorem arguments_length {compare : Comparison} {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth index : Nat}
    {initial final : Assignment} {schemas targets : List Pattern}
    (matched : ArgumentsMeaning compare rule spec ambient site path depth initial index schemas targets final) :
    schemas.length = targets.length := by
  induction schemas generalizing targets initial index with
  | nil =>
      cases targets <;> simp_all [ArgumentsMeaning]
  | cons schema schemas ih =>
      cases targets with
      | nil => simp [ArgumentsMeaning] at matched
      | cons target targets =>
          simp only [ArgumentsMeaning] at matched
          obtain ⟨middle, _, tail⟩ := matched
          simpa using congrArg Nat.succ (ih tail)

theorem arranged_presents (kind : CollType) (targets others : List Pattern) :
    Presents kind (arrange kind targets) others ↔ Presents kind targets others := by
  cases kind with
  | vec => rfl
  | hashBag =>
      exact ⟨fun same => (PatternLexOrder.sortLex_perm targets).symm.trans same,
        fun same => (PatternLexOrder.sortLex_perm targets).trans same⟩
  | hashSet =>
      constructor <;> intro same item
      · exact (arrange_mem item).symm.trans (same item)
      · exact (arrange_mem item).trans (same item)

/-- A whole collection row uses semantic decomposition, independently of the
finite physical-index enumeration used by execution. -/
theorem collection_exact (compare : Comparison) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (initial final : Assignment) (schemas targets : List Pattern) (rest : Option String) (kind : CollType)
    (unordered : kind ≠ .vec)
    (rows : ∀ values middle,
      middle ∈ runArguments compare rule spec ambient site path depth initial 0 schemas values ↔
        ArgumentsMeaning compare rule spec ambient site path depth initial 0 schemas values middle) :
    final ∈ (kindAllocations kind schemas.length (arrange kind targets)).flatMap (fun (values, residual) =>
      (runArguments compare rule spec ambient site path depth initial 0 schemas values).flatMap
        fun middle => finish compare rule spec ambient site path depth schemas.length rest kind
          middle (arrange kind residual)) ↔
    ∃ values residual middle, Presents kind targets (values ++ residual) ∧
      ArgumentsMeaning compare rule spec ambient site path depth initial 0 schemas values middle ∧
      Finished compare rule spec ambient site path depth schemas.length rest kind middle
        (arrange kind residual) final := by
  have distinct : kind = .hashSet → (arrange kind targets).Nodup := by
    rintro rfl
    exact canonical_set_distinct targets
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨⟨values, residual⟩, allocated, middle, matched, finished⟩
    have matched' := (rows values middle).mp matched
    have length := arguments_length matched'
    have presented := (allocations_present_exact unordered distinct).mp
      ⟨residual, by simpa only [length] using allocated, Presents.of_eq rfl⟩
    exact ⟨values, residual, middle, (arranged_presents ..).mp presented, matched',
      (finish_exact ..).mp finished⟩
  · rintro ⟨values, residual, middle, presented, matched, finished⟩
    have length := arguments_length matched
    obtain ⟨actual, allocated, same⟩ :=
      (allocations_present_exact unordered distinct).mpr ((arranged_presents ..).mpr presented)
    refine ⟨(values, actual), ?_, middle, (rows values middle).mpr matched, ?_⟩
    · simpa only [length] using allocated
    · apply (finish_exact ..).mpr
      simpa only [arrange_eq_of_presents same] using finished

mutual
/-- Recursive execution is exact for the independent collection-decomposition
meaning, at every authored path and binder depth. -/
theorem runAt_exact (compare : Comparison) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (initial : Assignment) (schema target : Pattern) (final : Assignment) :
    final ∈ runAt compare rule spec ambient site path depth initial schema target ↔
      Meaning compare rule spec ambient site path depth initial schema target final := by
  cases schema with
  | fvar name => simp [runAt, Meaning]
  | bvar index =>
      cases target <;> simp [runAt, Meaning]
  | apply label schemas =>
      cases target <;> simp only [runAt, Meaning, List.not_mem_nil]
      next actual targets =>
        by_cases same : label = actual
        · simp only [same, ↓reduceIte, true_and]
          exact runArguments_exact compare rule spec ambient site path depth initial 0 schemas targets final
        · simp [same]
  | lambda display body =>
      cases target <;> simp only [runAt, Meaning, List.not_mem_nil]
      next actual target =>
        exact runAt_exact compare rule spec ambient site (path ++ [0]) (depth + 1) initial body target final
  | multiLambda arity displays body =>
      cases target <;> simp only [runAt, Meaning, List.not_mem_nil]
      next actual actualDisplays target =>
        by_cases same : arity = actual
        · simp only [same, ↓reduceIte, true_and]
          exact runAt_exact compare rule spec ambient site (path ++ [0]) (depth + actual) initial body target final
        · simp [same]
  | subst body replacement =>
      cases target <;> simp only [runAt, Meaning, List.not_mem_nil]
      next targetBody targetReplacement =>
        simp only [List.mem_flatMap]
        apply exists_congr
        intro middle
        exact and_congr
          (runAt_exact compare rule spec ambient site (path ++ [0]) (depth + 1) initial body targetBody middle)
          (runAt_exact compare rule spec ambient site (path ++ [1]) depth middle replacement targetReplacement final)
  | collection kind schemas rest =>
      cases target <;> simp only [runAt.eq_def, Meaning.eq_def, List.not_mem_nil]
      next actual targets actualRest =>
        by_cases accepted : kind = actual ∧ actualRest = none
        · rcases accepted with ⟨rfl, rfl⟩
          simp only [true_and, and_true, ↓reduceIte]
          by_cases vector : kind = .vec
          · subst kind
            simp only [↓reduceIte]
            cases rest with
            | none =>
                exact runArguments_exact compare rule spec ambient site path depth initial 0 schemas targets final
            | some name =>
                simp only [List.mem_filterMap]
                apply exists_congr
                intro middle
                exact and_congr
                  (runArguments_exact compare rule spec ambient site path depth initial 0 schemas
                    (targets.take schemas.length) middle) Iff.rfl
          · simp only [vector, ↓reduceIte]
            exact collection_exact compare rule spec ambient site path depth initial final schemas targets rest kind
              vector (fun values middle =>
                runArguments_exact compare rule spec ambient site path depth initial 0 schemas values middle)
        · simp only [accepted, ↓reduceIte, List.not_mem_nil]
          tauto
termination_by sizeOf schema
decreasing_by all_goals sizeOf_pattern_dec

theorem runArguments_exact (compare : Comparison) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (initial : Assignment) (index : Nat) (schemas targets : List Pattern) (final : Assignment) :
    final ∈ runArguments compare rule spec ambient site path depth initial index schemas targets ↔
      ArgumentsMeaning compare rule spec ambient site path depth initial index schemas targets final := by
  cases schemas with
  | nil => cases targets <;> simp [runArguments, ArgumentsMeaning]
  | cons schema schemas =>
      cases targets with
      | nil => simp [runArguments, ArgumentsMeaning]
      | cons target targets =>
          simp only [runArguments, ArgumentsMeaning, List.mem_flatMap]
          apply exists_congr
          intro middle
          exact and_congr
            (runAt_exact compare rule spec ambient site (path ++ [index]) depth initial schema target middle)
            (runArguments_exact compare rule spec ambient site path depth middle (index + 1) schemas targets final)
termination_by sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec
end

end Mettapedia.OSLF.MeTTaIL.EquationalScopedMatching
