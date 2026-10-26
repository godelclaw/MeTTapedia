import Mettapedia.Computability.RegularLanguages.Regex
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Powerset

/-!
# Regular languages from finite derivative-closed families

Myhill–Nerode identifies regularity with finitely many left quotients. A finite
family closed under letter derivatives contains every quotient of its members.
For `L * M`, use `A * M + ⋃ S`, where `A` is a quotient of `L` and `S` is a
set of quotients of `M`. For `L∗`, use `L∗` and `(⋃ S) * L∗` for sets of
quotients of `L`. Derivatives commute with unions, so both families are closed.

These constructions prove regularity of literal/wildcard expressions over any
alphabet and of Mathlib's expressions. Balanced Boolean words separate these
languages from a nonregular language with infinitely many distinct residuals.
-/

set_option autoImplicit false

open scoped Computability

namespace Mettapedia.Computability.RegularLanguages

universe u
variable {α : Type u}

/-- The left quotient by a word with one more letter at its end. -/
theorem leftQuotient_concat (L : Language α) (word : List α) (a : α) :
    L.leftQuotient (word ++ [a]) = leftDerivative a (L.leftQuotient word) :=
  Language.leftQuotient_append L word [a]

/-- Removing a first letter from a left quotient gives a left quotient. -/
theorem leftDerivative_mem_range_leftQuotient (L : Language α) (a : α) {K : Language α}
    (member : K ∈ Set.range L.leftQuotient) :
    leftDerivative a K ∈ Set.range L.leftQuotient := by
  obtain ⟨word, rfl⟩ := member
  exact ⟨word ++ [a], leftQuotient_concat L word a⟩

/-- **A finite family of languages closed under removing a first letter
consists of regular languages.** -/
theorem isRegular_of_finite_closed {family : Set (Language α)} (finite : family.Finite)
    (closed : ∀ K ∈ family, ∀ a, leftDerivative a K ∈ family) {L : Language α}
    (member : L ∈ family) : L.IsRegular := by
  refine Language.IsRegular.of_finite_range_leftQuotient (finite.subset ?_)
  rintro _ ⟨word, rfl⟩
  induction word using List.reverseRecOn with
  | nil => exact member
  | append_singleton word a ih =>
      simpa only [leftQuotient_concat] using closed _ ih a

/-- A word of a union of languages is a word of one of them. -/
theorem mem_sSup_iff (S : Set (Language α)) (w : List α) :
    w ∈ sSup S ↔ ∃ K ∈ S, w ∈ K :=
  Set.mem_sUnion

/-- A word of a union of languages followed by a language. -/
theorem mem_sSup_mul_iff (S : Set (Language α)) (M : Language α) (w : List α) :
    w ∈ sSup S * M ↔ ∃ K ∈ S, w ∈ K * M := by
  rw [sSup_eq_iSup, Language.iSup_mul]
  simp_rw [Language.iSup_mul]
  simp [Language.mem_iSup]

theorem isRegular_zero : (0 : Language α).IsRegular :=
  isRegular_of_finite_closed (family := {0}) (Set.finite_singleton _)
    (by rintro K rfl a; exact leftDerivative_zero a) rfl

theorem isRegular_one : (1 : Language α).IsRegular :=
  isRegular_of_finite_closed (family := {1, 0}) (Set.toFinite _)
    (by
      rintro K (rfl | rfl) a <;> simp)
    (Or.inl rfl)

/-- The language of a literal and the language of the wildcard are regular,
whatever the alphabet. -/
theorem isRegular_atomLanguage (atom : Atom α) : (atomLanguage atom).IsRegular := by
  classical
  refine isRegular_of_finite_closed (family := {atomLanguage atom, 1, 0}) (Set.toFinite _) ?_
    (Or.inl rfl)
  rintro K (rfl | rfl | rfl) a <;>
    simp only [leftDerivative_atomLanguage, leftDerivative_one, leftDerivative_zero]
  all_goals first | (split_ifs <;> simp) | simp

/-- The family for a product. -/
def productFamily (L M : Language α) : Set (Language α) :=
  Set.image2 (fun A S => A * M + sSup S) (Set.range L.leftQuotient)
    (𝒫 (Set.range M.leftQuotient))

theorem productFamily_finite {L M : Language α}
    (left : (Set.range L.leftQuotient).Finite) (right : (Set.range M.leftQuotient).Finite) :
    (productFamily L M).Finite :=
  Set.Finite.image2 _ left right.powerset

theorem mem_productFamily (L M : Language α) : L * M ∈ productFamily L M := by
  refine ⟨L, ⟨[], rfl⟩, ∅, Set.empty_subset _, ?_⟩
  ext w
  simp

theorem productFamily_closed (L M : Language α) (K : Language α)
    (member : K ∈ productFamily L M) (a : α) : leftDerivative a K ∈ productFamily L M := by
  obtain ⟨A, inLeft, S, inRight, rfl⟩ := member
  refine ⟨leftDerivative a A, leftDerivative_mem_range_leftQuotient L a inLeft,
    leftDerivative a '' S ∪ {B | B = leftDerivative a M ∧ [] ∈ A}, ?_, ?_⟩
  · rintro B (⟨C, inS, rfl⟩ | ⟨rfl, _⟩)
    · exact leftDerivative_mem_range_leftQuotient M a (inRight inS)
    · exact ⟨[a], rfl⟩
  · classical
    rw [leftDerivative_add, leftDerivative_mul, leftDerivative_sSup]
    by_cases empty : [] ∈ A <;> simp [empty, sup_comm]
    exact sup_assoc _ _ _

/-- **The regular languages are closed under concatenation.** -/
theorem isRegular_mul {L M : Language α} (left : L.IsRegular) (right : M.IsRegular) :
    (L * M).IsRegular :=
  isRegular_of_finite_closed
    (productFamily_finite left.finite_range_leftQuotient right.finite_range_leftQuotient)
    (productFamily_closed L M) (mem_productFamily L M)

/-- The family for a star. -/
def starFamily (L : Language α) : Set (Language α) :=
  insert (L∗) ((fun S => sSup S * L∗) '' 𝒫 (Set.range L.leftQuotient))

theorem starFamily_finite {L : Language α} (finite : (Set.range L.leftQuotient).Finite) :
    (starFamily L).Finite :=
  (finite.powerset.image _).insert _

theorem starFamily_closed (L : Language α) (K : Language α)
    (member : K ∈ starFamily L) (a : α) : leftDerivative a K ∈ starFamily L := by
  rcases member with rfl | ⟨S, inRange, rfl⟩
  · refine Or.inr ⟨{leftDerivative a L}, ?_, ?_⟩
    · rintro B rfl
      exact ⟨[a], rfl⟩
    · show sSup {leftDerivative a L} * L∗ = leftDerivative a (L∗)
      rw [sSup_singleton, leftDerivative_kstar]
  · refine Or.inr
      ⟨leftDerivative a '' S ∪ {B | B = leftDerivative a L ∧ ∃ C ∈ S, [] ∈ C}, ?_, ?_⟩
    · rintro B (⟨C, inS, rfl⟩ | ⟨rfl, _⟩)
      · exact leftDerivative_mem_range_leftQuotient L a (inRange inS)
      · exact ⟨[a], rfl⟩
    · classical
      show sSup _ * L∗ = leftDerivative a (sSup S * L∗)
      rw [leftDerivative_mul, leftDerivative_sSup, leftDerivative_kstar]
      by_cases empty : ∃ C ∈ S, [] ∈ C <;> simp [mem_sSup_iff, empty]
      exact (add_mul (leftDerivative a L) (sSup (leftDerivative a '' S)) (L∗)).trans (add_comm _ _)

/-- **The regular languages are closed under star.** -/
theorem isRegular_kstar {L : Language α} (regular : L.IsRegular) : (L∗).IsRegular :=
  isRegular_of_finite_closed (starFamily_finite regular.finite_range_leftQuotient)
    (starFamily_closed L) (Or.inl rfl)

/-- **The language of a regular expression is regular.** -/
theorem language_isRegular (p : Regex α) : (language p).IsRegular := by
  induction p with
  | plus p q hp hq => exact hp.add hq
  | _ => simp_all [language, isRegular_zero, isRegular_one, isRegular_atomLanguage,
      isRegular_mul, isRegular_kstar]

/-- An expression has finitely many derivatives up to their languages. -/
theorem finite_derivative_languages [DecidableEq α] (p : Regex α) :
    (Set.range fun word => language (derivatives p word)).Finite := by
  simpa only [derivatives_language] using (language_isRegular p).finite_range_leftQuotient

/-- The language Mathlib assigns to one of its regular expressions is
regular. -/
theorem matches'_isRegular (p : RegularExpression α) : p.matches'.IsRegular :=
  ofRegular_language p ▸ language_isRegular (ofRegular p)

namespace RegularityControls

/-- Regular over an infinite alphabet, with the wildcard. -/
example : (language ((any : Regex ℕ).star * literal 0)).IsRegular := language_isRegular _

/-- The words with as many zeros as ones are not the language of an
expression: removing `n` leading zeros gives a different language for each
`n`. -/
def balanced : Language Bool := {w | w.count false = w.count true}

theorem balanced_quotients_differ {first second : ℕ} (different : first ≠ second) :
    balanced.leftQuotient (List.replicate first false) ≠
      balanced.leftQuotient (List.replicate second false) := by
  intro same
  have member := congrArg (fun L : Language Bool => List.replicate first true ∈ L) same
  change ((List.replicate first false ++ List.replicate first true).count false =
    (List.replicate first false ++ List.replicate first true).count true) =
    ((List.replicate second false ++ List.replicate first true).count false =
    (List.replicate second false ++ List.replicate first true).count true) at member
  simp [List.count_append, List.count_replicate] at member
  exact different member.symm

theorem balanced_not_regular : ¬ balanced.IsRegular := by
  intro regular
  exact Set.infinite_range_of_injective
    (f := fun n : ℕ => balanced.leftQuotient (List.replicate n false))
    (fun _ _ => not_imp_not.mp balanced_quotients_differ)
    (regular.finite_range_leftQuotient.subset
      (Set.range_comp_subset_range (fun n : ℕ => List.replicate n false) balanced.leftQuotient))

/-- So no expression denotes it. -/
theorem balanced_not_expressible (p : Regex Bool) : language p ≠ balanced :=
  fun same => balanced_not_regular (same ▸ language_isRegular p)

end RegularityControls

end Mettapedia.Computability.RegularLanguages
