import Mettapedia.Algorithms.Retrieval.RetrievalContract
import Mettapedia.Algorithms.Retrieval.SelectorContract
import Mathlib.Data.Fintype.Fin

/-!
# Identity-bound screening certificates

A numerical bounds array is meaningful only for the exact source and compact
views from which it was derived.  Equal shape is insufficient: a same-shaped
array of forged bounds can discard the true top result.  This module specifies
the minimum identity check for a public screening boundary.  Admission does
not itself prove the bounds sound; a producer must separately establish
`Valid` before the general screened-reranking theorem applies.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Retrieval.ScreeningCertificate

open Mettapedia.Algorithms.Retrieval
open SelectorContract
open RetrievalContract

structure Certificate (I Score : Type*) where
  source : View
  compact : View
  lower : I → Score
  upper : I → Score

def Certificate.Valid {I Score : Type*} [Preorder Score]
    (score : I → Score) (rows : Finset I) (certificate : Certificate I Score) : Prop :=
  ∀ row ∈ rows,
    certificate.lower row ≤ score row ∧ score row ≤ certificate.upper row

def checkViews {I Score : Type*} (source compact : View)
    (certificate : Certificate I Score) : Option (Certificate I Score) :=
  if certificate.source = source ∧ certificate.compact = compact
  then some certificate else none

theorem matching_views_admitted {I Score : Type*} (source compact : View)
    (lower upper : I → Score) :
    checkViews source compact ⟨source, compact, lower, upper⟩ =
      some ⟨source, compact, lower, upper⟩ := by
  simp [checkViews]

theorem wrong_source_refused {I Score : Type*} (expected compact actual : View)
    (lower upper : I → Score) (different : actual ≠ expected) :
    checkViews expected compact ⟨actual, compact, lower, upper⟩ = none := by
  simp [checkViews, different]

theorem wrong_compact_refused {I Score : Type*} (source expected actual : View)
    (lower upper : I → Score) (different : actual ≠ expected) :
    checkViews source expected ⟨source, actual, lower, upper⟩ = none := by
  simp [checkViews, different]

theorem checkViews_some_iff {I Score : Type*} (source compact : View)
    (certificate : Certificate I Score) :
    checkViews source compact certificate = some certificate ↔
      certificate.source = source ∧ certificate.compact = compact := by
  simp [checkViews]

def twoRows : Finset (Fin 2) := Finset.univ

def trueScore (row : Fin 2) : Int := if row = 1 then 1 else 0

def forgedUpper (row : Fin 2) : Int := if row = 0 then 1 else 0

/-- A same-domain, same-shaped forged bounds vector ranks row zero above row
one, although row one is the unique true top result. -/
theorem shape_only_screening_is_unsound :
    IsTopK trueScore 1 twoRows {1} ∧
      (1 : Fin 2) ∉ screen forgedUpper 1 twoRows := by
  have one_ne_zero : (1 : Fin 2) ≠ 0 := by decide
  constructor
  · simp [IsTopK, twoRows, trueScore]
  · simp only [screen, Finset.mem_filter]
    simp [forgedUpper, one_ne_zero]

theorem valid_certificate_supplies_bounds {I Score : Type*} [Preorder Score]
    (score : I → Score) (rows : Finset I) (certificate : Certificate I Score)
    (valid : certificate.Valid score rows) :
    (∀ row ∈ rows, certificate.lower row ≤ score row) ∧
      (∀ row ∈ rows, score row ≤ certificate.upper row) := by
  constructor
  · intro row member
    exact (valid row member).1
  · intro row member
    exact (valid row member).2

/-- Identity admission and numerical validity are distinct obligations.  Once
both hold, inclusive screening followed by exact reranking preserves the
source top-k and the result carries the admitted source/compact identities. -/
theorem checked_valid_screening_preserves_identity_and_exactness
    {I Score : Type*} [DecidableEq I] [LinearOrder Score]
    (sourceView compactView : View) (score : I → Score)
    (certificate : Certificate I Score) (threshold : Score)
    {k : Nat} {source witnesses original result : Finset I}
    (checked : checkViews sourceView compactView certificate = some certificate)
    (valid : certificate.Valid score source)
    (originalTop : IsTopK score k source original)
    (witnessesInSource : witnesses ⊆ source)
    (enoughWitnesses : min k source.card ≤ witnesses.card)
    (witnessesReachThreshold :
      ∀ row ∈ witnesses, threshold ≤ certificate.lower row)
    (resultTop :
      IsTopK score k (screen certificate.upper threshold source) result) :
    (certificate.source = sourceView ∧ certificate.compact = compactView) ∧
      IsTopK score k source result := by
  constructor
  · exact (checkViews_some_iff sourceView compactView certificate).mp checked
  · exact screened_rerank_exact score certificate.lower certificate.upper threshold
      originalTop witnessesInSource enoughWitnesses
      (fun row member => (valid row member).1)
      (fun row member => (valid row member).2)
      witnessesReachThreshold resultTop

end Mettapedia.Algorithms.Retrieval.ScreeningCertificate
