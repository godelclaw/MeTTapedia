import Mettapedia.Computability.RegularLanguages.Regularity
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.Dedup
import Mathlib.Logic.Function.Iterate

/-!
# Recognition-preserving normalization and residual execution

Union simplification flattens alternatives, removes the empty language and
keeps each authored alternative once. Concatenation removes units and zeros;
star removes zero, unit and nested stars. These operations preserve language
and never add constructors. They do not canonicalize language equivalence.

The `(a*)*` controls exhibit unsimplified derivative growth and normalized
stabilization. In general only the residual-language observations are proved
finite, not the expression states. The normalized machine's continuation
readout commutes with Mathlib's residual automaton. Captures and priority
require their own observations and are outside this recognition contract.
-/

set_option autoImplicit false

open scoped Computability

namespace Mettapedia.Computability.RegularLanguages

universe u
variable {α : Type u}

deriving instance DecidableEq for RegularExpression

/-- Ordered leaves of the union tree, omitting the empty language. -/
def alternatives : Regex α → List (Regex α)
  | .zero => []
  | .plus p q => alternatives p ++ alternatives q
  | p => [p]

/-- Union of ordered alternatives; the empty list denotes the empty language. -/
def unionOf : List (Regex α) → Regex α
  | [] => 0
  | [p] => p
  | p :: q :: rest => p + unionOf (q :: rest)

theorem mem_language_unionOf (list : List (Regex α)) (w : List α) :
    w ∈ language (unionOf list) ↔ ∃ p ∈ list, w ∈ language p := by
  induction list with
  | nil => simp [unionOf]
  | cons p rest ih =>
      cases rest with
      | nil => simp [unionOf]
      | cons q rest =>
          change w ∈ language p + language (unionOf (q :: rest)) ↔ _
          rw [Language.mem_add, ih]
          simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left]

/-- A word is accepted exactly when one of the alternatives accepts it. -/
theorem mem_language_iff_alternatives (p : Regex α) (w : List α) :
    w ∈ language p ↔ ∃ q ∈ alternatives p, w ∈ language q := by
  induction p with
  | plus p q hp hq =>
    change (w ∈ language p ∨ w ∈ language q) ↔ _
    rw [hp, hq]
    simp only [alternatives, List.mem_append, or_and_right, exists_or]
  | _ => simp [alternatives]

/-- Number of authored syntax constructors, independently of language equivalence. -/
def nodeCount : Regex α → Nat
  | .zero | .epsilon | .char _ => 1
  | .plus p q | .comp p q => nodeCount p + nodeCount q + 1
  | .star p => nodeCount p + 1

theorem nodeCount_pos (p : Regex α) : 0 < nodeCount p := by
  cases p <;> simp [nodeCount]

/-- Constructor counts plus one union per alternative. -/
def alternativesWeight (list : List (Regex α)) : Nat :=
  (list.map fun p => nodeCount p + 1).sum

theorem alternativesWeight_append (first second : List (Regex α)) :
    alternativesWeight (first ++ second) = alternativesWeight first + alternativesWeight second := by
  simp [alternativesWeight]

theorem alternativesWeight_le_of_sublist {first second : List (Regex α)}
    (sublist : first.Sublist second) :
    alternativesWeight first ≤ alternativesWeight second :=
  (sublist.map _).sum_le_sum fun _ _ => Nat.zero_le _

/-- A union of alternatives has one constructor fewer than their weight. -/
theorem nodeCount_unionOf (list : List (Regex α)) (nonempty : list ≠ []) :
    nodeCount (unionOf list) + 1 = alternativesWeight list := by
  induction list with
  | nil => contradiction
  | cons p rest ih =>
    cases rest <;> simp_all [unionOf, nodeCount, alternativesWeight]
    omega

/-- Taking an expression apart into its alternatives adds no constructor. -/
theorem alternativesWeight_alternatives_le (p : Regex α) :
    alternativesWeight (alternatives p) ≤ nodeCount p + 1 := by
  induction p <;> simp_all [alternatives, alternativesWeight, nodeCount]
  omega

def smartConcat : Regex α → Regex α → Regex α
  | .zero, _ => 0
  | _, .zero => 0
  | .epsilon, q => q
  | p, .epsilon => p
  | p, q => p * q

/-- Simplify the star of the empty language, the empty word, or another star. -/
def smartStar : Regex α → Regex α
  | .zero => 1
  | .epsilon => 1
  | .star p => p.star
  | p => p.star

@[simp] theorem language_smartConcat (p q : Regex α) :
    language (smartConcat p q) = language p * language q := by
  cases p <;> cases q <;> simp [smartConcat]

@[simp] theorem language_smartStar (p : Regex α) :
    language (smartStar p) = (language p)∗ := by
  cases p <;> simp [smartStar]

theorem smartConcat_nodeCount_le (p q : Regex α) :
    nodeCount (smartConcat p q) ≤ nodeCount p + nodeCount q + 1 := by
  cases p <;> cases q <;> simp [smartConcat, nodeCount] <;> omega

theorem smartStar_nodeCount_le (p : Regex α) :
    nodeCount (smartStar p) ≤ nodeCount p + 1 := by
  cases p <;> simp [smartStar, nodeCount]

section Simplification
variable [DecidableEq α]

/-- Flatten the union and deduplicate authored alternatives. -/
def smartUnion (p q : Regex α) : Regex α :=
  unionOf (alternatives p ++ alternatives q).dedup

@[simp] theorem language_smartUnion (p q : Regex α) :
    language (smartUnion p q) = language p + language q := by
  ext w
  rw [smartUnion, mem_language_unionOf, Language.mem_add,
    mem_language_iff_alternatives p, mem_language_iff_alternatives q]
  simp only [List.mem_dedup, List.mem_append, or_and_right, exists_or]

theorem smartUnion_nodeCount_le (p q : Regex α) :
    nodeCount (smartUnion p q) ≤ nodeCount p + nodeCount q + 1 := by
  have total := add_le_add (alternativesWeight_alternatives_le p) (alternativesWeight_alternatives_le q)
  have weight := alternativesWeight_le_of_sublist (List.dedup_sublist (alternatives p ++ alternatives q))
  rw [alternativesWeight_append] at weight
  unfold smartUnion
  by_cases empty : (alternatives p ++ alternatives q).dedup = []
  · rw [empty]; simp [unionOf, nodeCount]
  · have size := nodeCount_unionOf _ empty; omega

/-- A structural simplifier, with language equality as its contract. -/
def normalize : Regex α → Regex α
  | .zero => 0
  | .epsilon => 1
  | .char atom => .char atom
  | .plus p q => smartUnion (normalize p) (normalize q)
  | .comp p q => smartConcat (normalize p) (normalize q)
  | .star p => smartStar (normalize p)

@[simp] theorem normalize_language (p : Regex α) :
    language (normalize p) = language p := by
  induction p <;> simp_all [normalize]

theorem normalize_nodeCount_le (p : Regex α) : nodeCount (normalize p) ≤ nodeCount p := by
  induction p <;> simp only [normalize, nodeCount]
  all_goals first
    | exact le_rfl
    | exact (smartUnion_nodeCount_le _ _).trans (by omega)
    | exact (smartConcat_nodeCount_le _ _).trans (by omega)
    | exact (smartStar_nodeCount_le _).trans (by omega)

def normalizedDerivative (a : α) (p : Regex α) : Regex α := normalize (derivative a p)

theorem normalizedDerivative_language (a : α) (p : Regex α) :
    language (normalizedDerivative a p) = leftDerivative a (language p) := by
  rw [normalizedDerivative, normalize_language, derivative_language]

/-- Consume each letter once, simplifying its derivative before continuing. -/
def matchNormalized : Regex α → List α → Bool
  | p, [] => p.matchEpsilon
  | p, a :: rest => matchNormalized (normalizedDerivative a p) rest

theorem matchNormalized_correct (p : Regex α) (word : List α) :
    matchNormalized p word = true ↔ word ∈ language p := by
  induction word generalizing p with
  | nil => exact nullable_correct p
  | cons a rest ih =>
      rw [matchNormalized, ih, normalizedDerivative_language, mem_leftDerivative]

theorem matchNormalized_eq_fullMatch (p : Regex α) (word : List α) :
    matchNormalized p word = fullMatch p word := by
  exact Bool.eq_iff_iff.mpr ((matchNormalized_correct p word).trans (fullMatch_correct p word).symm)

/-- Normalized transitions as a Mathlib DFA; the syntax state type need not be finite. -/
def normalizedDFA (p : Regex α) : DFA α (Regex α) where
  step q a := normalizedDerivative a q
  start := p
  accept := {q | q.matchEpsilon = true}

/-- A state's continuation language agrees with the independent language semantics. -/
theorem normalizedDFA_acceptsFrom (p q : Regex α) :
    (normalizedDFA p).acceptsFrom q = language q := by
  have comparison := acceptsFrom_eq_of_bisimulation (normalizedDFA p) (language q).toDFA
    (fun r s => language r = s.val)
    (by intro r s same; change r.matchEpsilon = true ↔ [] ∈ s.val; rw [nullable_correct, same])
    (by intro r s same a; change language (normalizedDerivative a r) = leftDerivative a s.val
        rw [normalizedDerivative_language, same])
    q (language q).toDFA.start rfl
  exact comparison.trans (Language.accepts_toDFA _)

/-- The machine and the independently recursive matcher agree on complete words. -/
theorem normalizedDFA_accepts_iff (p : Regex α) (word : List α) :
    word ∈ (normalizedDFA p).accepts ↔ matchNormalized p word = true := by
  change word ∈ (normalizedDFA p).acceptsFrom p ↔ _
  rw [normalizedDFA_acceptsFrom, matchNormalized_correct]

theorem normalizedDFA_eval_language (p : Regex α) (word : List α) :
    language ((normalizedDFA p).eval word) = (language p).leftQuotient word := by
  rw [← normalizedDFA_acceptsFrom p ((normalizedDFA p).eval word),
    ← Language.leftQuotient_accepts_apply]
  exact congrArg (fun L => L.leftQuotient word) (normalizedDFA_acceptsFrom p p)

/-- Execution commutes with observation in Mathlib's canonical residual automaton. -/
theorem normalizedDFA_eval_toDFA (p : Regex α) (word : List α) :
    language ((normalizedDFA p).eval word) = ((language p).toDFA.eval word).val := by
  rw [normalizedDFA_eval_language]
  induction word using List.reverseRecOn <;>
    simp_all only [Language.leftQuotient_nil, DFA.eval_nil, Language.start_toDFA,
      Language.leftQuotient_append, DFA.eval_append_singleton, Language.step_toDFA]

/-- Finiteness concerns residual languages, not the expressions representing them. -/
theorem normalizedDFA_finite_languages (p : Regex α) :
    (Set.range fun word => language ((normalizedDFA p).eval word)).Finite := by
  simpa only [normalizedDFA_eval_language] using (language_isRegular p).finite_range_leftQuotient

theorem language_eq_iff_fullMatch {p q : Regex α} :
    language p = language q ↔ ∀ word, fullMatch p word = fullMatch q word := by
  constructor
  · intro same word; exact fullMatch_congr same word
  · intro same; ext word; rw [← fullMatch_correct, ← fullMatch_correct, same word]

end Simplification

namespace ResidualControls

/-- Recognition equivalence does not make normalized syntax canonical. -/
theorem different_normal_forms_same_language :
    normalize (literal true + literal false) ≠ normalize (literal false + literal true) ∧
      language (literal true + literal false) = language (literal false + literal true) :=
  ⟨by decide, add_comm _ _⟩

/-- Equal current acceptance does not imply equal future behavior. -/
theorem nullability_does_not_determine_continuations :
    (literal true).matchEpsilon = (literal false).matchEpsilon ∧
      fullMatch (literal true) [true] ≠ fullMatch (literal false) [true] := by decide

end ResidualControls

namespace NormalizationControls

theorem removes_empty_branch : normalize (0 + literal 'λ') = literal 'λ' := by decide

theorem removes_unit_factor : normalize (1 * literal 'λ') = literal 'λ' := by decide

/-- A repeated alternative is kept once, wherever it sits in the union. -/
theorem removes_repeated_alternative :
    normalize (literal 'λ' + (literal 'β' + literal 'λ')) = literal 'β' + literal 'λ' := by
  decide

theorem removes_star_of_star :
    normalize (literal 'λ').star.star = (literal 'λ').star := by decide

/-- Distinct alternatives are all kept. -/
theorem keeps_distinct_alternatives :
    normalize (literal 'λ' + literal 'β') = literal 'λ' + literal 'β' := by decide

/-- Language simplification does not claim the original source was identical. -/
theorem different_source_same_language :
    (0 + literal 'λ' : Regex Char) ≠ literal 'λ' ∧
      language (0 + literal 'λ') = language (literal 'λ') := by
  constructor
  · intro h
    cases h
  · simp

theorem normalized_nullable_concat :
    matchNormalized ((1 + literal 'λ') * literal 'β') ['β'] = true := by decide

theorem normalized_wrong_letter : matchNormalized (literal 'λ') ['β'] = false := by decide

/-- The star of a star of a letter. -/
def starOfStar : Regex Char := (literal 'a').star.star

/-- Without simplification every further letter about doubles the derivative. -/
theorem unsimplified_derivatives_grow :
    (List.range 6).map (fun count =>
        nodeCount (derivatives starOfStar (List.replicate count 'a'))) =
      [3, 8, 22, 50, 106, 218] := by decide

/-- With simplification the derivative by three letters is the derivative by
two. -/
theorem simplified_derivative_fixed :
    normalizedDerivative 'a'
        (normalizedDerivative 'a' (normalizedDerivative 'a' starOfStar)) =
      normalizedDerivative 'a' (normalizedDerivative 'a' starOfStar) := by decide

/-- So the simplifying matcher meets the same expression at every letter
after the second, however long the word. -/
theorem simplified_derivatives_stabilize (count : Nat) :
    (normalizedDerivative 'a')^[count + 2] starOfStar =
      (normalizedDerivative 'a')^[2] starOfStar := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (normalizedDerivative 'a')^[(count + 2).succ] starOfStar = _
      rw [Function.iterate_succ_apply', ih]
      exact simplified_derivative_fixed

theorem simplified_derivative_size :
    nodeCount ((normalizedDerivative 'a')^[2] starOfStar) = 8 := by decide

end NormalizationControls

end Mettapedia.Computability.RegularLanguages
