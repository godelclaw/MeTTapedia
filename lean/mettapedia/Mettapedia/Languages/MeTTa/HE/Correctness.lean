import Mettapedia.Languages.MeTTa.HE.ExecutableBoundary

/-!
# Historical certificates and actual HE result filtering

`EvalSpec` is the maintained historical implementation-facing relation. Its
ordinary-call grammar does not cover the retained invocation worker's function
completion. Consequently executable membership or stable completion alone does
not imply that relation. Independent selected-frame invocation laws live in
`RecursiveSemanticSoundness`; first-success source admission is a distinct policy.

This owner keeps the actual filter theorem and the sound algebra of certificates
which explicitly contain both historical evidence and executable stability.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

def EvalAtomFilteredAtFuel (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (n : Nat) (r : ResultPair)
    (live : List Atom := []) : Prop :=
  EvalAtom space dispatch (live := live) atom type_ b r ∧
  (isErrorAtom r.1 = true →
    isEmptyOrError atom = false →
    ∀ r' ∈ interpretExpression space dispatch atom type_ b n live,
      isErrorAtom r'.1 = true)

/-- For non-expression atoms, `interpretExpression` returns `[]` at any fuel. -/
private theorem interpretExpression_nil_of_not_expr (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (fuel : Nat) (live : List Atom)
    (h : ∀ op args, atom ≠ .expression (op :: args)) :
    interpretExpression space dispatch atom type_ b fuel live = [] := by
  cases fuel with
  | zero => simp [interpretExpression]
  | succ n => simp only [interpretExpression]

/-- The actual success-priority filter returns an error only if the complete
expression result list at its reached subfuel contains no success. This law
does not infer a historical declarative derivation from execution. -/
theorem evalAtom_filter_preserves_priority (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (n : Nat) {live : List Atom} (r : ResultPair)
    (hr : r ∈ evalAtom space dispatch atom type_ b (n + 1) live) :
    isErrorAtom r.1 = true → isEmptyOrError atom = false →
      ∀ r' ∈ interpretExpression space dispatch atom type_ b n live, isErrorAtom r'.1 = true := by
  intro h_is_err h_not_ee r' h_r'_mem
  -- Case 1: atom is not a proper expression → interpretExpression returns []
  by_cases h_proper : ∃ op args, atom = .expression (op :: args)
  · -- Case 2: atom IS a proper expression
    obtain ⟨op, args, rfl⟩ := h_proper
    -- Navigate evalAtom's if-chain for .expression (op :: args)
    simp only [evalAtom] at hr
    split at hr  -- isEmptyOrError
    · -- isEmptyOrError = true contradicts h_not_ee
      rename_i h_ee; simp [h_not_ee] at h_ee
    · split at hr  -- type pass: type_ == atomType ∨ type_ == getMetaType ∨ variableType
      · -- In this branch r = (atom, b), so isErrorAtom r.1 = isErrorAtom atom.
        -- Since isEmptyOrError atom = false, isErrorAtom atom = false.
        rename_i h_tp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        -- isEmptyOrError false means isErrorAtom atom = false
        simp [isEmptyOrError] at h_not_ee
        obtain ⟨_, h_ne⟩ := h_not_ee
        simp [h_ne] at h_is_err
      · split at hr  -- symbol/grounded/unit → typeCast
        · -- Unreachable for .expression (op :: args):
          -- getMetaType (.expression (op :: args)) = expressionType ≠ symbolType/groundedType
          -- and .expression (op :: args) ≠ unit (unit = .expression [])
          rename_i h_cast
          simp [getMetaType, Atom.symbolType, Atom.groundedType, Atom.expressionType,
                Atom.unit] at h_cast
        · split at hr  -- expression branch (getMetaType == expressionType)
          · -- THE expression branch: r ∈ filter of interpretExpression results
            split at hr  -- successes non-empty?
            · -- Successes non-empty: r is a success → contradicts h_is_err
              rw [List.mem_filter] at hr
              obtain ⟨_, h_not_err⟩ := hr
              simp at h_not_err
              simp [h_not_err] at h_is_err
            · -- Successes empty: ALL interpretExpression results are errors
              rename_i h_succ_empty
              -- h_succ_empty : ¬(!successes.isEmpty) = true, i.e. successes.isEmpty = true
              rw [List.mem_filter] at hr
              obtain ⟨h_r_mem, _⟩ := hr
              -- r' ∈ interpretExpression ... n. Show isErrorAtom r'.1 = true.
              -- The success filter is empty, so no element has !isErrorAtom = true.
              by_contra h_not_err_r'
              push Not at h_succ_empty
              -- h_succ_empty says the success filter is empty
              -- Convert: ¬(!(filter ...).isEmpty) = true means (filter ...).isEmpty = true
              have h_filt_empty : (List.filter (fun x => !isErrorAtom x.1)
                  (interpretExpression space dispatch
                    (.expression (op :: args)) type_ b n live)).isEmpty = true := by
                cases h : (List.filter (fun x => !isErrorAtom x.1)
                  (interpretExpression space dispatch
                    (.expression (op :: args)) type_ b n live)).isEmpty <;> simp_all
              rw [List.isEmpty_iff] at h_filt_empty
              have h_ne : isErrorAtom r'.1 = false := by
                cases h : isErrorAtom r'.1 <;> simp_all
              have h_mem_filt : r' ∈ (interpretExpression space dispatch
                  (.expression (op :: args)) type_ b n live).filter
                  (fun x => !isErrorAtom x.1) := by
                rw [List.mem_filter]
                exact ⟨h_r'_mem, by simp [h_ne]⟩
              rw [h_filt_empty] at h_mem_filt
              simp at h_mem_filt
          · -- Unreachable: getMetaType (.expression (op :: args)) = expressionType
            rename_i h_not_expr
            simp [getMetaType, Atom.expressionType] at h_not_expr
  · -- Case 1: not a proper expression → interpretExpression returns []
    push Not at h_proper
    rw [interpretExpression_nil_of_not_expr _ _ _ _ _ _ _ h_proper] at h_r'_mem
    simp at h_r'_mem


/-- A historical derivation and actual execution jointly earn the historical
filtered certificate. The filter condition is proved from the actual run. -/
theorem evalAtom_filtered_sound (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (n : Nat) {live : List Atom} (r : ResultPair)
    (meaning : EvalAtom space dispatch (live := live) atom type_ b r)
    (returned : r ∈ evalAtom space dispatch atom type_ b (n + 1) live) :
    EvalAtomFilteredAtFuel space dispatch atom type_ b n r live :=
  ⟨meaning, evalAtom_filter_preserves_priority space dispatch atom type_ b n r returned⟩

theorem evalAtom_reaches_filtered_sound
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) {live : List Atom} (r : ResultPair)
    (meaning : EvalAtom space dispatch (live := live) atom type_ b r) :
    (∃ n, r ∈ evalAtom space dispatch atom type_ b (n + 1) live) →
      ∃ n, EvalAtomFilteredAtFuel space dispatch atom type_ b n r live := by
  rintro ⟨n, returned⟩
  exact ⟨n, evalAtom_filtered_sound space dispatch atom type_ b n r meaning returned⟩

/-- Projection of the historical evidence explicitly contained in a certificate. -/
theorem evalAtomCertified_to_EvalAtom
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) (live : List Atom := []) :
    EvalAtomCertified space dispatch atom type_ b r live →
      EvalAtom space dispatch (live := live) atom type_ b r := fun certified => certified.1

/-- Stable support is retained independently of the historical evidence. -/
theorem evalAtomCertified_to_stably_reaches
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) (live : List Atom := []) :
    EvalAtomCertified space dispatch atom type_ b r live →
      EvalAtomStablyReaches space dispatch atom type_ b r live := fun certified => certified.2

/-- Every historical certificate has an actual filtered witness. -/
theorem evalAtomCertified_to_filtered_witness
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) (live : List Atom := []) :
    EvalAtomCertified space dispatch atom type_ b r live →
      ∃ n, EvalAtomFilteredAtFuel space dispatch atom type_ b n r live := by
  intro certified
  obtain ⟨fuel, eventual⟩ := certified.2
  exact evalAtom_reaches_filtered_sound space dispatch atom type_ b r certified.1
    ⟨fuel, eventual (fuel + 1) (Nat.le_succ fuel)⟩

theorem evalAtomCertified_eventually_filtered
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) (live : List Atom := []) :
    EvalAtomCertified space dispatch atom type_ b r live →
      ∃ n0, ∀ n, n ≥ n0 → EvalAtomFilteredAtFuel space dispatch atom type_ b n r live := by
  intro certified
  obtain ⟨fuel, eventual⟩ := certified.2
  refine ⟨fuel, fun n enough => ?_⟩
  exact evalAtom_filtered_sound space dispatch atom type_ b n r certified.1
    (eventual (n + 1) (Nat.le_succ_of_le enough))

/-- Historical meaning conjoined with stable support at the default entry. -/
def EvalCertified (space : Space) (atom : Atom) (r : ResultPair) : Prop :=
  EvalAtomCertified space GroundedDispatch.none atom Atom.undefinedType Bindings.empty r

end Mettapedia.Languages.MeTTa.HE
