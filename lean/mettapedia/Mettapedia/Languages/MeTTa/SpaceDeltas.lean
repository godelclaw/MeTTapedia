import Mettapedia.Languages.MeTTa.TensorSpaces
import Mettapedia.GSLT.Dynamics.IncrementalSpaceInvariants

/-!
# Deltas, versions and incremental maintenance of answers

A change to a space is a delta: a space whose annotations may be negative, a
Z-set (the representation of DBSP, Budiu, McSherry, Ryzhyk and Tannen).
Inserting an atom adds a positive delta and deleting it a negative one, and a
version of a space is the sum of the deltas logged so far.

* **Queries are linear** (`queryHom`): the answers of a sum are the sum of the
  answers, and over a ring of annotations the answers of a difference are the
  difference (`query_sub`, `query_neg`). A cached answer is therefore kept
  current by adding the answers of each delta, insertions and deletions alike
  (`query_version_succ`), and the answers of a version are the sum of its
  deltas' answers (`query_version`).
* **A version is a snapshot**: logging later deltas does not change it
  (`version_append`).
* **Joins are bilinear**: the change of a contraction is the sum of three
  contractions (`contract_delta`, `contract_delta_sub`).
* **Bags embed into Z-sets without loss** (`castBag_injective`), every query
  commutes with the embedding (`castBag_query`), and a Z-set is a bag exactly
  when no count is negative (`isBag_iff`). So answers maintained on Z-sets
  read back as bag answers whenever the version is a bag.
* **Deleting what is present needs only counts.** Over counts, removing a
  batch that the space contains subtracts exactly its answers
  (`query_tsub_of_le`), the query form of retracting a known batch
  (`EvidenceSpaces.retract_revision`). Truncated subtraction of a batch that is
  not contained does not commute with queries (`Controls.monus_not_linear`).
  Signed counts are needed when deltas arrive out of order or must compose
  freely: a deletion logged before its insertion shows as a negative count,
  which no bag has (`Controls.early_delete_negative`). Signed annotations pay
  for this: no nontrivial ring is positive, so the presence of answers no
  longer composes (`AnnotationCapabilities.not_positive_of_ring`). Over
  idempotent (set) annotations no subtraction undoes a merge at all
  (`WeightedAnswerAlgebra.no_space_sub_undoes_merge`): a cache of answer sets
  cannot be maintained under deletion, a counted one can.
* **Fragment revision.** The answers of a query are an additive summary of the
  stored bag (`answerSummary`), so the fragment-only cache revision of
  `GSLT.Dynamics.IncrementalSpaceInvariants` applies to them: a local rewrite
  updates cached answers from its removed and inserted fragments alone
  (`answers_reviseCached`).

Related modules: `HE.CacheCorrectness` invalidates cached answers on a
revision change, where the laws here update them instead;
`HE.IncrementalTableSemantics` accumulates answers monotonically, the
insertion-only case of `query_version_succ`; `HE.SnapshotPreservation` proves
snapshot isolation for HE's list spaces, the counterpart of `version_append`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceDeltas

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra
open Mettapedia.Languages.MeTTa.SpaceQueryPolicy
open Mettapedia.Languages.MeTTa.TensorSpaces

universe u

variable {K : Type u} {Atom Pat Res I J L : Type*}

/-! ## Queries are linear -/

section Linear

variable [Semiring K] (matcher : Pat → Atom → Option Res)

/-- `query` as an additive map of spaces. -/
noncomputable def queryHom (pattern : Pat) : Space K Atom →+ Ans K Res where
  toFun space := query matcher space pattern
  map_zero' := query_zero matcher pattern
  map_add' left right := query_add matcher left right pattern

end Linear

section Ring

variable [Ring K] (matcher : Pat → Atom → Option Res)

/-- **Deleting is subtracting answers.** -/
theorem query_sub (left right : Space K Atom) (pattern : Pat) :
    query matcher (left - right) pattern = query matcher left pattern - query matcher right pattern :=
  map_sub (queryHom matcher pattern) left right

theorem query_neg (space : Space K Atom) (pattern : Pat) :
    query matcher (-space) pattern = -query matcher space pattern :=
  map_neg (queryHom matcher pattern) space

end Ring

section Monus

variable (matcher : Pat → Atom → Option Res)

/-- **Over counts, deleting a batch the space contains subtracts its
answers.** -/
theorem query_tsub_of_le {space removed : Space ℕ Atom} (contained : removed ≤ space)
    (pattern : Pat) :
    query matcher (space - removed) pattern =
      query matcher space pattern - query matcher removed pattern := by
  conv_rhs => rw [← tsub_add_cancel_of_le contained, query_add]
  rw [add_tsub_cancel_right]

end Monus

/-! ## Fragment revision of cached answers -/

section Summary

open Mettapedia.GSLT.Dynamics.IncrementalSpaceInvariants

variable [Ring K] [DecidableEq Atom] (matcher : Pat → Atom → Option Res)

/-- The answers of a query, counted in a ring, as an additive summary of the
stored bag. -/
noncomputable def answerSummary (pattern : Pat) : Multiset Atom →+ Ans K Res :=
  (queryHom matcher pattern).comp
    ((Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom K)).comp
      (Multiset.toFinsupp (α := Atom)).toAddMonoidHom)

theorem answerSummary_apply (pattern : Pat) (stored : Multiset Atom) :
    answerSummary matcher pattern stored =
      query matcher (Ans.mapK (Nat.castRingHom K) (Multiset.toFinsupp stored)) pattern := rfl

/-- **A local rewrite updates cached answers from its fragment alone**: the
answers are an additive summary, so the fragment-only revision applies. -/
theorem answers_reviseCached (pattern : Pat) (update : FramedUpdate Atom) (cached : Ans K Res)
    (exact : cached = answerSummary matcher pattern update.source) :
    reviseCached (answerSummary matcher pattern) cached update.fragment =
      answerSummary matcher pattern update.target :=
  reviseCached_eq_targetSummary _ cached update exact

end Summary

/-! ## Versions -/

section Versions

variable {S : Type*} [AddCommMonoid S]

/-- The space after the first `count` deltas of a log. -/
def version (log : List S) (count : ℕ) : S := (log.take count).sum

/-- **A version does not change when later deltas are logged.** -/
theorem version_append (log later : List S) {count : ℕ} (within : count ≤ log.length) :
    version (log ++ later) count = version log count := by
  rw [version, version, List.take_append_of_le_length within]

theorem version_succ (log : List S) {count : ℕ} (within : count < log.length) :
    version log (count + 1) = version log count + log[count] := by
  rw [version, version, List.take_add_one, List.getElem?_eq_getElem within, Option.toList_some,
    List.sum_append, List.sum_singleton]

variable [Semiring K] (matcher : Pat → Atom → Option Res)

/-- The answers of a version are the sum of its deltas' answers. -/
theorem query_version (log : List (Space K Atom)) (count : ℕ) (pattern : Pat) :
    query matcher (version log count) pattern =
      ((log.take count).map fun delta => query matcher delta pattern).sum :=
  map_list_sum (queryHom matcher pattern) (log.take count)

/-- **Incremental maintenance**: the answers of the next version are the
cached answers plus the answers of the new delta. -/
theorem query_version_succ (log : List (Space K Atom)) {count : ℕ} (within : count < log.length)
    (pattern : Pat) :
    query matcher (version log (count + 1)) pattern =
      query matcher (version log count) pattern + query matcher log[count] pattern := by
  rw [version_succ log within, query_add]

end Versions

/-! ## Joins are bilinear -/

section Joins

variable [Semiring K]

/-- **The change of a join**: contracting changed tensors adds three
contractions to the old result. -/
theorem contract_delta (left leftDelta : Space K (I × J)) (right rightDelta : Space K (J × L)) :
    contract (left + leftDelta) (right + rightDelta) =
      contract left right +
        (contract leftDelta right + contract left rightDelta + contract leftDelta rightDelta) := by
  rw [contract_add_left, contract_add_right, contract_add_right]
  abel

theorem contract_delta_sub {R : Type u} [Ring R] (left leftDelta : Space R (I × J))
    (right rightDelta : Space R (J × L)) :
    contract (left + leftDelta) (right + rightDelta) - contract left right =
      contract leftDelta right + contract left rightDelta + contract leftDelta rightDelta := by
  rw [contract_delta]
  abel

end Joins

/-! ## Bags inside Z-sets -/

section Bags

/-- A bag space read as a Z-set. -/
noncomputable def castBag (space : Space ℕ Atom) : Space ℤ Atom :=
  Ans.mapK (Nat.castRingHom ℤ) space

@[simp] theorem castBag_apply (space : Space ℕ Atom) (atom : Atom) :
    castBag space atom = (space atom : ℤ) := rfl

theorem castBag_injective : Function.Injective (castBag (Atom := Atom)) := by
  intro first second same
  ext atom
  have := congrArg (fun space : Space ℤ Atom => space atom) same
  simp only [castBag_apply, Nat.cast_inj] at this
  exact this

theorem castBag_add (first second : Space ℕ Atom) :
    castBag (first + second) = castBag first + castBag second :=
  Ans.mapK_add _ first second

/-- Every query commutes with reading bags as Z-sets. -/
theorem castBag_query (matcher : Pat → Atom → Option Res) (space : Space ℕ Atom) (pattern : Pat) :
    Ans.mapK (Nat.castRingHom ℤ) (query matcher space pattern) =
      query matcher (castBag space) pattern :=
  mapK_query matcher (Nat.castRingHom ℤ) space pattern

/-- **A Z-set is a bag exactly when no count is negative.** -/
theorem isBag_iff (space : Space ℤ Atom) :
    (∃ bag : Space ℕ Atom, castBag bag = space) ↔ ∀ atom, 0 ≤ space atom := by
  constructor
  · rintro ⟨bag, rfl⟩ atom
    rw [castBag_apply]
    exact Int.natCast_nonneg _
  · intro nonnegative
    refine ⟨Finsupp.mapRange Int.toNat Int.toNat_zero space, ?_⟩
    ext atom
    rw [castBag_apply, Finsupp.mapRange_apply, Int.toNat_of_nonneg (nonnegative atom)]

end Bags

/-! ## Controls -/

namespace Controls

/-- **Truncated subtraction does not commute with queries**: the pattern
matches both `0` and `1`; deleting `1` from the space `{0}` leaves `{0}`, one
answer, while subtracting the answers leaves none. -/
theorem monus_not_linear :
    let matcher : Unit → ℕ → Option Unit := fun _ _ => some ()
    query matcher ((Finsupp.single 0 1 : Space ℕ ℕ) - Finsupp.single 1 1) () ≠
      query matcher (Finsupp.single 0 1 : Space ℕ ℕ) () - query matcher (Finsupp.single 1 1) () := by
  intro matcher
  have difference : ((Finsupp.single 0 1 : Space ℕ ℕ) - Finsupp.single 1 1) = Finsupp.single 0 1 := by
    ext atom
    rw [Finsupp.coe_tsub, Pi.sub_apply]
    by_cases zero : atom = 0
    · subst zero
      simp
    · by_cases one : atom = 1
      · subst one
        simp
      · simp [Ne.symm zero, Ne.symm one]
  have answered : ∀ atom : ℕ, contribution (K := ℕ) matcher () atom = Ans.pure () :=
    fun _ => rfl
  rw [difference, query_single, query_single, one_smul, one_smul, answered, answered, tsub_self]
  intro same
  have := congrArg (fun answers : Ans ℕ Unit => answers ()) same
  simp [Ans.pure] at this

/-- **A deletion before its insertion shows as a negative count**: the
version after the deletion alone is no bag; after both deltas it is the empty
bag. -/
theorem early_delete_negative :
    let log : List (Space ℤ ℕ) := [-Finsupp.single 7 1, Finsupp.single 7 1]
    ¬ (∃ bag : Space ℕ ℕ, castBag bag = version log 1) ∧ version log 2 = 0 := by
  intro log
  constructor
  · rw [isBag_iff]
    intro nonnegative
    have := nonnegative 7
    simp [log, version] at this
  · simp [log, version]

/-- Maintaining answers through a deletion: the space `{0, 1}` with `1`
deleted answers the pattern `1` with nothing, computed from the cached answers
and the delta's. -/
theorem deletion_maintained :
    let matcher : ℕ → ℕ → Option ℕ := fun pattern atom => if atom = pattern then some atom else none
    let log : List (Space ℤ ℕ) := [Finsupp.single 0 1 + Finsupp.single 1 1, -Finsupp.single 1 1]
    query matcher (version log 2) 1 = query matcher (version log 1) 1 + query matcher log[1] 1 ∧
      query matcher (version log 2) 1 = 0 := by
  intro matcher log
  refine ⟨query_version_succ matcher log (by simp [log]) 1, ?_⟩
  have collapsed : version log 2 = Finsupp.single 0 1 := by
    simp [log, version]
  rw [collapsed, query_single, one_smul]
  simp [contribution, matcher]

end Controls

end Mettapedia.Languages.MeTTa.SpaceDeltas
