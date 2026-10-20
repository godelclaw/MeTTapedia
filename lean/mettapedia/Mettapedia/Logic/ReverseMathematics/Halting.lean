import Mettapedia.Logic.ReverseMathematics.RCA0Models

/-!
# The halting set separates ACA₀ from RCA₀ in ω-models

Over the signature of primitive recursive functions, the halting set
`K = {e | φ_e(0)↓}` is defined by the `Σ⁰₁` formula `∃s h(e, s) = 1`, where
`h(e, s) = 1` exactly when code `e` halts on input `0` within `s` steps
(Mathlib's `Nat.Partrec.Code.evaln`, primitive recursive by
`Nat.Partrec.Code.primrec_evaln`).

* `holds_haltingFormula`: the formula defines `K`.
* `haltingSet_not_recursive`: `K` is not recursive (Mathlib's
  `ComputablePred.halting_problem`).
* `recursiveSets_not_satisfies_haltingComprehension`: the recursive sets fail
  one `Σ⁰₁` comprehension instance; hence `recursiveSets_not_models_ACA0`.
  Together with `recursiveSets_models_RCA0` this separates the ω-model
  classes of RCA₀ and ACA₀ (Simpson §VIII.1).
* `Models.haltingSet_mem`: every ω-model of ACA₀ contains `K`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ReverseMathematics

open Formula Term Nat.Partrec Encodable

/-- The halting set at input `0`, indexed by Mathlib's numbering of codes. -/
def haltingSet : Set ℕ :=
  {e | (Code.eval (Denumerable.ofNat Code e) 0).Dom}

/-- One if code `e` halts on input `0` within `s` steps, else zero. -/
def haltStep (e s : ℕ) : ℕ :=
  bif (Code.evaln s (Denumerable.ofNat Code e) 0).isSome then 1 else 0

theorem haltStep_primrec : Primrec₂ haltStep :=
  Primrec.cond (Primrec.option_isSome.comp
      (Code.primrec_evaln.comp
        (Primrec.pair (Primrec.pair Primrec.snd ((Primrec.ofNat Code).comp Primrec.fst))
          (Primrec.const 0))))
    (Primrec.const 1) (Primrec.const 0)

theorem mem_haltingSet_iff (e : ℕ) : e ∈ haltingSet ↔ ∃ s, haltStep e s = 1 := by
  simp only [haltingSet, Set.mem_ofPred_eq, haltStep]
  constructor
  · intro dom
    obtain ⟨k, hk⟩ := Code.evaln_complete.mp (Part.get_mem dom)
    refine ⟨k, ?_⟩
    rw [Option.mem_def] at hk
    simp [hk]
  · rintro ⟨s, hs⟩
    cases h : Code.evaln s (Denumerable.ofNat Code e) 0 with
    | none => simp [h] at hs
    | some x => exact Part.dom_iff_mem.mpr ⟨x, Code.evaln_sound h⟩

/-- The halting-step function as a primitive recursive symbol. -/
def haltSymbol : Signature.primrec.Fn := ⟨haltStep, haltStep_primrec⟩

/-- `∃s h(e, s) = 1`, with `e` the number variable `0`. -/
def haltingFormula : Formula Signature.primrec :=
  ex (eq (app haltSymbol (var 1) (var 0)) one)

theorem haltingFormula_isSigma : IsSigma 1 haltingFormula :=
  isSigma_one_iff.mpr ⟨_, .eq _ _, rfl⟩

theorem holds_haltingFormula (S : Set (Set ℕ)) (e : ℕ) (v : ℕ → ℕ) (V : ℕ → Set ℕ) :
    Holds S haltingFormula (Env.cons e v) V ↔ e ∈ haltingSet := by
  rw [mem_haltingSet_iff]
  simp [haltingFormula, Holds, Term.eval, haltSymbol, Signature.primrec]

/-- **The halting set is not recursive.** -/
theorem haltingSet_not_recursive : ¬ IsRecursiveSet haltingSet := by
  classical
  intro h
  apply ComputablePred.halting_problem 0
  refine ⟨inferInstance, ?_⟩
  have composed := (ComputablePred.decide h).comp (Computable.encode (α := Code))
  refine composed.of_eq fun c => ?_
  rw [Bool.eq_iff_iff]
  simp [haltingSet, Denumerable.ofNat_encode]

/-- **The recursive sets fail `Σ⁰₁` comprehension for the halting set.** -/
theorem recursiveSets_not_satisfies_haltingComprehension :
    ¬ Satisfies recursiveSets (comprehension haltingFormula) := by
  intro h
  obtain ⟨X, member, spec⟩ := (holds_comprehension _ _ (fun _ => 0) (fun _ => ∅)).mp
    (h (fun _ => 0) (fun _ => ∅) (fun _ => isRecursiveSet_empty))
  have same : X = haltingSet := by
    ext e
    rw [spec e, holds_haltingFormula]
  exact haltingSet_not_recursive (same ▸ member)

/-- **The recursive sets are not an ω-model of `Σ⁰₁` comprehension.** -/
theorem recursiveSets_not_satisfies_sigma1Comprehension :
    ¬ ∀ φ ∈ (sigma1Comprehension : Set (Formula Signature.primrec)),
      Satisfies recursiveSets φ :=
  fun h => recursiveSets_not_satisfies_haltingComprehension
    (h _ ⟨haltingFormula, haltingFormula_isSigma, rfl⟩)

/-- **The recursive sets are not an ω-model of ACA₀.** -/
theorem recursiveSets_not_models_ACA0 :
    ¬ Models recursiveSets (ACA0 : Set (Formula Signature.primrec)) := by
  intro h
  exact recursiveSets_not_satisfies_haltingComprehension
    (h.2 _ (Or.inr ⟨haltingFormula, haltingFormula_isSigma.isArithmetical, rfl⟩))

/-- **Every ω-model of ACA₀ contains the halting set.** -/
theorem Models.haltingSet_mem {S : Set (Set ℕ)}
    (h : Models S (ACA0 : Set (Formula Signature.primrec))) : haltingSet ∈ S := by
  obtain ⟨⟨A, hA⟩, closed⟩ := (models_ACA0_iff S).mp h
  obtain ⟨X, member, spec⟩ := closed haltingFormula haltingFormula_isSigma.isArithmetical
    (fun _ => 0) (fun _ => A) (fun _ => hA)
  have same : X = haltingSet := by
    ext e
    rw [spec e, holds_haltingFormula]
  exact same ▸ member

/-- Positive example: the sets computable from the halting set satisfy the
halting comprehension instance. -/
theorem principal_halting_satisfies_haltingComprehension :
    Satisfies (principal haltingSet) (comprehension haltingFormula) := by
  intro v V _
  rw [holds_comprehension]
  exact ⟨haltingSet, SetTuringLE.refl _, fun e => (holds_haltingFormula _ e v V).symm⟩

#print axioms haltingSet_not_recursive
#print axioms recursiveSets_not_models_ACA0
#print axioms Models.haltingSet_mem

end Mettapedia.Logic.ReverseMathematics
