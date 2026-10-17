import Mettapedia.Languages.Megalodon.ConversionElaboration
import Mettapedia.Computability.FuelledConversionEvidence

/-!
# Bounded observations of the actual Mathdata normalization profile

The program here invokes the existing delta normalizer and beta/eta pass
normalizer. Its partial completion algorithm retries that exact program at
increasing bounds. Soundness is to the existing checked conversion calculus,
through the existing executable article elaborator. It is not a verification
of Megalodon's lazy converter, Proofgold's resource counters or Lean's kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.FuelledConversionProfile
open MathdataKernel
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open ConversionElaboration

theorem beta_mono_succ (fuel : Nat) (term normal : Tm)
    (normalized : Tm.normalize fuel term = some normal) :
    Tm.normalize (fuel + 1) term = some normal := by
  induction fuel generalizing term normal with
  | zero =>
      cases pass : Tm.normalizeOne term with
      | mk result stable =>
          cases stable <;> simp [Tm.normalize, pass] at normalized ⊢
          exact normalized
  | succ fuel ih =>
      cases pass : Tm.normalizeOne term with
      | mk result stable =>
          cases stable
          · simp only [Tm.normalize, pass, Bool.false_eq_true, if_false] at normalized ⊢
            exact ih result normal normalized
          · simpa only [Tm.normalize, pass, if_true] using normalized

theorem delta_mono_succ (environment : Environment) : ∀ (fuel : Nat) (term normal : Tm),
    deltaNormalize environment fuel term = some normal →
      deltaNormalize environment (fuel + 1) term = some normal
  | 0, .named name, normal, normalized => by
      cases lookup : environment.lookupTerm? name with
      | none => simpa only [deltaNormalize, lookup] using normalized
      | some declaration =>
          rcases declaration with ⟨found, type, body⟩
          cases body with
          | none => simpa only [deltaNormalize, lookup] using normalized
          | some body =>
              simp only [deltaNormalize, lookup] at normalized
              cases normalized
  | fuel + 1, .named name, normal, normalized => by
      cases lookup : environment.lookupTerm? name with
      | none => simpa only [deltaNormalize, lookup] using normalized
      | some declaration =>
          rcases declaration with ⟨found, type, body⟩
          cases body with
          | none => simpa only [deltaNormalize, lookup] using normalized
          | some body =>
              simp only [deltaNormalize, lookup] at normalized ⊢
              exact delta_mono_succ environment fuel body normal normalized
  | fuel, .app function argument, normal, normalized => by
      cases left : deltaNormalize environment fuel function with
      | none => simp [deltaNormalize, left] at normalized
      | some first =>
          cases right : deltaNormalize environment fuel argument with
          | none => simp [deltaNormalize, left, right] at normalized
          | some second =>
              have leftMore := delta_mono_succ environment fuel function first left
              have rightMore := delta_mono_succ environment fuel argument second right
              simpa only [deltaNormalize, left, right, leftMore, rightMore,
                Option.bind_some, Option.pure_def] using normalized
  | fuel, .lam type body, normal, normalized => by
      cases child : deltaNormalize environment fuel body with
      | none => simp [deltaNormalize, child] at normalized
      | some result =>
          have more := delta_mono_succ environment fuel body result child
          simpa only [deltaNormalize, child, more, Option.bind_some, Option.pure_def] using normalized
  | fuel, .imp domain codomain, normal, normalized => by
      cases left : deltaNormalize environment fuel domain with
      | none => simp [deltaNormalize, left] at normalized
      | some first =>
          cases right : deltaNormalize environment fuel codomain with
          | none => simp [deltaNormalize, left, right] at normalized
          | some second =>
              have leftMore := delta_mono_succ environment fuel domain first left
              have rightMore := delta_mono_succ environment fuel codomain second right
              simpa only [deltaNormalize, left, right, leftMore, rightMore,
                Option.bind_some, Option.pure_def] using normalized
  | fuel, .all type body, normal, normalized => by
      cases child : deltaNormalize environment fuel body with
      | none => simp [deltaNormalize, child] at normalized
      | some result =>
          have more := delta_mono_succ environment fuel body result child
          simpa only [deltaNormalize, child, more, Option.bind_some, Option.pure_def] using normalized
  | fuel, .typeApp function type, normal, normalized => by
      cases child : deltaNormalize environment fuel function with
      | none => simp [deltaNormalize, child] at normalized
      | some result =>
          have more := delta_mono_succ environment fuel function result child
          simpa only [deltaNormalize, child, more, Option.bind_some, Option.pure_def] using normalized
  | fuel, .typeLam body, normal, normalized => by
      cases child : deltaNormalize environment fuel body with
      | none => simp [deltaNormalize, child] at normalized
      | some result =>
          have more := delta_mono_succ environment fuel body result child
          simpa only [deltaNormalize, child, more, Option.bind_some, Option.pure_def] using normalized
  | fuel, .typeAll body, normal, normalized => by
      cases child : deltaNormalize environment fuel body with
      | none => simp [deltaNormalize, child] at normalized
      | some result =>
          have more := delta_mono_succ environment fuel body result child
          simpa only [deltaNormalize, child, more, Option.bind_some, Option.pure_def] using normalized
  | fuel, .db index, normal, normalized => by
      cases fuel <;> simpa only [deltaNormalize] using normalized
  | fuel, .prim index, normal, normalized => by
      cases fuel <;> simpa only [deltaNormalize] using normalized
termination_by fuel term => (fuel, sizeOf term)

theorem normalize_mono_succ (environment : Environment) (fuel : Nat) (term normal : Tm)
    (normalized : MathdataKernel.normalize environment fuel term = some normal) :
    MathdataKernel.normalize environment (fuel + 1) term = some normal := by
  cases unfolded : deltaNormalize environment fuel term with
  | none => simp [MathdataKernel.normalize, unfolded] at normalized
  | some intermediate =>
      have more := delta_mono_succ environment fuel term intermediate unfolded
      simp only [MathdataKernel.normalize, unfolded] at normalized
      simp only [MathdataKernel.normalize, more]
      exact beta_mono_succ fuel intermediate normal normalized

theorem normalize_mono (environment : Environment) (term normal : Tm) {first second : Nat}
    (increased : first ≤ second) (normalized : MathdataKernel.normalize environment first term = some normal) :
    MathdataKernel.normalize environment second term = some normal := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le increased
  clear increased
  induction extra with
  | zero => simpa using normalized
  | succ extra ih => exact normalize_mono_succ environment (first + extra) term normal ih

inductive Outcome where
  | exhausted
  | equivalent (normal : Tm)
  | different (leftNormal rightNormal : Tm)
  deriving DecidableEq, Repr

def observe (environment : Environment) (fuel : Nat) (left right : Tm) : Outcome :=
  match MathdataKernel.normalize environment fuel left, MathdataKernel.normalize environment fuel right with
  | some first, some second => if first = second then .equivalent first else .different first second
  | _, _ => .exhausted

theorem equivalent_iff (environment : Environment) (fuel : Nat) (left right normal : Tm) :
    observe environment fuel left right = .equivalent normal ↔
      MathdataKernel.normalize environment fuel left = some normal ∧
        MathdataKernel.normalize environment fuel right = some normal := by
  cases first : MathdataKernel.normalize environment fuel left with
  | none => simp [observe, first]
  | some l =>
      cases second : MathdataKernel.normalize environment fuel right with
      | none => simp [observe, first, second]
      | some r =>
          by_cases same : l = r <;> simp [observe, first, second, same]
          intro leftSame rightSame
          exact same (leftSame.trans rightSame.symm)

theorem equivalent_mono (environment : Environment) (left right normal : Tm) {first second : Nat}
    (increased : first ≤ second) (accepted : observe environment first left right = .equivalent normal) :
    observe environment second left right = .equivalent normal := by
  obtain ⟨l, r⟩ := (equivalent_iff environment first left right normal).mp accepted
  exact (equivalent_iff environment second left right normal).mpr
    ⟨normalize_mono environment left normal increased l, normalize_mono environment right normal increased r⟩

theorem different_iff (environment : Environment) (fuel : Nat) (left right l r : Tm) :
    observe environment fuel left right = .different l r ↔ l ≠ r ∧
      MathdataKernel.normalize environment fuel left = some l ∧
        MathdataKernel.normalize environment fuel right = some r := by
  cases first : MathdataKernel.normalize environment fuel left with
  | none => simp [observe, first]
  | some a =>
      cases second : MathdataKernel.normalize environment fuel right with
      | none => simp [observe, first, second]
      | some b =>
          by_cases same : a = b
          · subst b
            simp only [observe, first, second, ↓reduceIte, reduceCtorEq, Option.some.injEq]
            constructor
            · intro impossible
              cases impossible
            · rintro ⟨different, al, ar⟩
              exact different (al.symm.trans ar)
          · simp only [observe, first, second, if_neg same, Outcome.different.injEq, Option.some.injEq]
            constructor
            · rintro ⟨rfl, rfl⟩
              exact ⟨same, rfl, rfl⟩
            · exact fun evidence => evidence.2

theorem different_mono (environment : Environment) (left right l r : Tm) {first second : Nat}
    (increased : first ≤ second) (refused : observe environment first left right = .different l r) :
    observe environment second left right = .different l r := by
  obtain ⟨different, leftNormal, rightNormal⟩ := (different_iff environment first left right l r).mp refused
  exact (different_iff environment second left right l r).mpr
    ⟨different, normalize_mono environment left l increased leftNormal,
      normalize_mono environment right r increased rightNormal⟩

theorem native_iff (environment : Environment) (fuel : Nat) (left right : Tm) :
    nativeConverts environment fuel left right = true ↔ ∃ normal, observe environment fuel left right = .equivalent normal := by
  cases first : MathdataKernel.normalize environment fuel left with
  | none => simp [nativeConverts, observe, first]
  | some l =>
      cases second : MathdataKernel.normalize environment fuel right with
      | none => simp [nativeConverts, observe, first, second]
      | some r => by_cases same : l = r <;> simp [nativeConverts, observe, first, second, same]

theorem article_sound (environment : Environment) (fuel : Nat) (left right normal : Tm)
    (accepted : observe environment fuel left right = .equivalent normal) :
    ∃ article, conversionArticle environment fuel left right = some article ∧
      checkRaw DefinitionConversionKernel.validated
        (DefinitionConversionKernel.converts (encoded environment.terms) (ETm left) (ETm right)) article = true := by
  obtain ⟨article, built⟩ := conversionArticle_complete environment ((native_iff environment fuel left right).mpr ⟨normal, accepted⟩)
  exact ⟨article, built, conversionArticle_checked environment built⟩

theorem native_mono (environment : Environment) (left right : Tm) {first second : Nat}
    (increased : first ≤ second) (accepted : nativeConverts environment first left right = true) :
    nativeConverts environment second left right = true := by
  obtain ⟨normal, observed⟩ := (native_iff environment first left right).mp accepted
  exact (native_iff environment second left right).mpr
    ⟨normal, equivalent_mono environment left right normal increased observed⟩

/-- This particular fixed-pass recognizer is transitive on successful inputs.
Resource-bounded recognition is not declared nontransitive without a counterexample. -/
theorem native_trans (environment : Environment) (fuel : Nat) (left middle right : Tm)
    (first : nativeConverts environment fuel left middle = true)
    (second : nativeConverts environment fuel middle right = true) :
    nativeConverts environment fuel left right = true := by
  obtain ⟨a, first⟩ := (native_iff environment fuel left middle).mp first
  obtain ⟨b, second⟩ := (native_iff environment fuel middle right).mp second
  obtain ⟨leftNormal, middleFirst⟩ := (equivalent_iff environment fuel left middle a).mp first
  obtain ⟨middleSecond, rightNormal⟩ := (equivalent_iff environment fuel middle right b).mp second
  have same : a = b := Option.some.inj (middleFirst.symm.trans middleSecond)
  exact (native_iff environment fuel left right).mpr ⟨a,
    (equivalent_iff environment fuel left right a).mpr ⟨leftNormal, by simpa only [same] using rightNormal⟩⟩

def finished (environment : Environment) (left right : Tm) (fuel : Nat) : Option Bool :=
  match observe environment fuel left right with
  | .exhausted => none
  | .equivalent _ => some true
  | .different _ _ => some false

/-- Retry the exact normalizer, returning its first completed comparison.
This does not enumerate explicit proofs or decide all conversion witnesses. -/
def partialComparison (environment : Environment) (left right : Tm) : Part Bool :=
  Nat.rfindOpt (finished environment left right)

theorem finished_true_iff (environment : Environment) (left right : Tm) (fuel : Nat) :
    finished environment left right fuel = some true ↔ nativeConverts environment fuel left right = true := by
  rw [native_iff]
  cases result : observe environment fuel left right <;> simp [finished, result]

theorem finished_mono (environment : Environment) (left right : Tm) {first second : Nat} {value : Bool}
    (increased : first ≤ second) (completed : finished environment left right first = some value) :
    finished environment left right second = some value := by
  cases result : observe environment first left right with
  | exhausted => simp [finished, result] at completed
  | equivalent normal =>
      have more := equivalent_mono environment left right normal increased result
      simpa only [finished, result, more] using completed
  | different l r =>
      have more := different_mono environment left right l r increased result
      simpa only [finished, result, more] using completed

/-- Eventual completeness for completed comparisons of this exact partial
algorithm, including completed unequal normal forms. -/
theorem partial_result_iff (environment : Environment) (left right : Tm) (value : Bool) :
    value ∈ partialComparison environment left right ↔
      ∃ fuel, finished environment left right fuel = some value := by
  constructor
  · intro result
    obtain ⟨fuel, completed⟩ := Nat.rfindOpt_spec result
    exact ⟨fuel, by simpa only [Option.mem_def] using completed⟩
  · rintro ⟨fuel, completed⟩
    have domain : (partialComparison environment left right).Dom := by
      rw [partialComparison, Nat.rfindOpt_dom]
      exact ⟨fuel, value, by simpa only [Option.mem_def] using completed⟩
    obtain ⟨actual, result⟩ := Part.dom_iff_mem.mp domain
    obtain ⟨first, observed⟩ := Nat.rfindOpt_spec result
    have observedEq : finished environment left right first = some actual := by
      simpa only [Option.mem_def] using observed
    have firstMore := finished_mono environment left right (le_max_left first fuel) observedEq
    have fuelMore := finished_mono environment left right (le_max_right first fuel) completed
    have same : actual = value := Option.some.inj (firstMore.symm.trans fuelMore)
    simpa only [same] using result

theorem partial_accepted_iff (environment : Environment) (left right : Tm) :
    true ∈ partialComparison environment left right ↔
      ∃ fuel, nativeConverts environment fuel left right = true := by
  simp only [partial_result_iff, finished_true_iff]

/-- Successful completion of the exact partial algorithm eventually supplies
an independently accepted original-kernel article at every larger bound. -/
theorem partial_accepted_articles (environment : Environment) (left right : Tm)
    (accepted : true ∈ partialComparison environment left right) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∃ article,
      conversionArticle environment fuel left right = some article ∧
        checkRaw DefinitionConversionKernel.validated
          (DefinitionConversionKernel.converts (encoded environment.terms) (ETm left) (ETm right)) article = true := by
  obtain ⟨bound, completed⟩ := (partial_accepted_iff environment left right).mp accepted
  obtain ⟨normal, observed⟩ := (native_iff environment bound left right).mp completed
  exact ⟨bound, fun fuel increased => article_sound environment fuel left right normal
    (equivalent_mono environment left right normal increased observed)⟩

/-- Strict pass accounting mirrors the inspected Proofgold loop's zero-budget
resource failure, using the existing Mathdata pass. No source-wide refinement
for Proofgold's additional term constructors is asserted. -/
def strictPassNormalize : Nat → Tm → Option Tm
  | 0, _ => none
  | fuel + 1, term =>
      let (result, stable) := Tm.normalizeOne term
      if stable then some result else strictPassNormalize fuel result

theorem strictPass_offset (fuel : Nat) (term : Tm) :
    strictPassNormalize (fuel + 1) term = Tm.normalize fuel term := by
  induction fuel generalizing term with
  | zero =>
      cases pass : Tm.normalizeOne term with
      | mk result stable => cases stable <;> simp [strictPassNormalize, Tm.normalize, pass]
  | succ fuel ih =>
      cases pass : Tm.normalizeOne term with
      | mk result stable =>
          rw [strictPassNormalize, Tm.normalize]
          simp only [pass]
          cases stable
          · exact ih result
          · rfl

namespace Controls

def betaTerm : Tm := .app (.lam .prop (.db 0)) (.prim 0)

theorem beta_zero_exhausted : observe {} 0 betaTerm (.prim 0) = .exhausted := by
  simp [observe, MathdataKernel.normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne,
    betaTerm, Tm.instantiate, Tm.instantiateAt, Tm.shift]
theorem beta_one_accepted : observe {} 1 betaTerm (.prim 0) = .equivalent (.prim 0) := by
  simp [observe, MathdataKernel.normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne,
    betaTerm, Tm.instantiate, Tm.instantiateAt, Tm.shift]
theorem stable_wrong_normal_forms : observe {} 0 (.prim 0) (.prim 1) = .different (.prim 0) (.prim 1) := by
  simp [observe, MathdataKernel.normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne]
theorem stable_reflexivity_without_fuel : observe {} 0 (.prim 0) (.prim 0) = .equivalent (.prim 0) := by
  simp [observe, MathdataKernel.normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne]
theorem strict_zero_exhaustion : strictPassNormalize 0 (.prim 0) = none := rfl
theorem strict_one_completion : strictPassNormalize 1 (.prim 0) = some (.prim 0) := rfl

/-- A concrete recursive definition makes this selected partial algorithm
remain unfinished at every finite unfolding depth. -/
def loopEnvironment : Environment := { terms := [⟨"loop", .prop, some (.named "loop")⟩] }

theorem loop_delta_exhausted (fuel : Nat) :
    deltaNormalize loopEnvironment fuel (.named "loop") = none := by
  induction fuel with
  | zero => simp [deltaNormalize, loopEnvironment, Environment.lookupTerm?, lookupTermList?]
  | succ fuel ih =>
      simpa [deltaNormalize, loopEnvironment, Environment.lookupTerm?, lookupTermList?] using ih

theorem loop_observation_exhausted (fuel : Nat) :
    observe loopEnvironment fuel (.named "loop") (.named "loop") = .exhausted := by
  simp [observe, MathdataKernel.normalize, loop_delta_exhausted]

theorem loop_partial_undefined :
    ¬ (partialComparison loopEnvironment (.named "loop") (.named "loop")).Dom := by
  rw [partialComparison, Nat.rfindOpt_dom]
  rintro ⟨fuel, result, completed⟩
  simp only [finished, loop_observation_exhausted, Option.not_mem_none] at completed

end Controls

end Mettapedia.Languages.Megalodon.FuelledConversionProfile
