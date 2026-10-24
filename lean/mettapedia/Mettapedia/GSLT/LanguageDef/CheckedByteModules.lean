import Mettapedia.GSLT.LanguageDef.CheckedByteSafety

/-!
# Separate byte-buffer interfaces

Existing permission plans survive an extension that preserves their resolved
signatures. Allocated ownership crosses a call only within the declared
allocator/release family. Returned views retain their source lifetime.

These are interface and permission laws. They do not identify a linked native
object with its source or prove that a foreign implementation obeys its table.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CheckedBytes

def Supports (before after : List Signature) : Prop :=
  ∀ name signature, before.find? (fun entry => entry.name == name) = some signature →
    after.find? (fun entry => entry.name == name) = some signature

theorem supports_append (before added : List Signature) : Supports before (before ++ added) := by
  intro name signature found
  simp [List.find?_append, found]

theorem transition_extension {before after : List Signature} {caller : Signature}
    {first last : State} {action : Action} (extension : Supports before after)
    (enabled : transition before caller first action = some last) :
    transition after caller first action = some last := by
  cases action <;> try exact enabled
  case invoke name arguments =>
    obtain ⟨witness, ready, remaining⟩ := Option.bind_eq_some_iff.mp enabled
    obtain ⟨target, found, rest⟩ := Option.bind_eq_some_iff.mp remaining
    exact Option.bind_eq_some_iff.mpr ⟨witness, ready,
      Option.bind_eq_some_iff.mpr ⟨target, extension name target found, rest⟩⟩

theorem apply_extension {before after : List Signature} {caller : Signature}
    {first last : State} {action : Action} (extension : Supports before after)
    (enabled : apply before caller first action = some last) :
    apply after caller first action = some last := by
  obtain ⟨witness, valid, remaining⟩ := Option.bind_eq_some_iff.mp enabled
  obtain ⟨next, stepped, rest⟩ := Option.bind_eq_some_iff.mp remaining
  exact Option.bind_eq_some_iff.mpr ⟨witness, valid,
    Option.bind_eq_some_iff.mpr ⟨next, transition_extension extension stepped, rest⟩⟩

theorem continueExits_extension {before after : State → Option (List Exit)}
    (extension : ∀ state exits, before state = some exits → after state = some exits)
    {inputs outputs : List Exit} (accepted : continueExits before inputs = some outputs) :
    continueExits after inputs = some outputs := by
  induction inputs generalizing outputs with
  | nil => exact accepted
  | cons first rest ih =>
      obtain ⟨initial, remaining, hfirst, hrest, rfl⟩ := continueExits_cons accepted
      have newFirst : (if first.kind == .normal then after first.state else some [first]) = some initial := by
        by_cases normal : first.kind = .normal
        · simpa [normal] using extension first.state initial (by simpa [normal] using hfirst)
        · simpa [normal] using hfirst
      exact Option.bind_eq_some_iff.mpr ⟨initial, newFirst,
        Option.bind_eq_some_iff.mpr ⟨remaining, ih hrest, rfl⟩⟩

/-- No admitted path changes when already-resolved interfaces stay current. -/
theorem check_extension {before after : List Signature} {caller : Signature}
    {body : Plan} {state : State} {outcomes : List Exit}
    (extension : Supports before after)
    (accepted : check before caller body state = some outcomes) :
    check after caller body state = some outcomes := by
  induction body generalizing state outcomes with
  | done | ret | breakLoop | continueLoop => exact accepted
  | step action next ih =>
      obtain ⟨nextState, enabled, rest⟩ := check_step accepted
      exact Option.bind_eq_some_iff.mpr ⟨nextState, apply_extension extension enabled, ih rest⟩
  | branch yes no next ihyes ihno ihnext =>
      obtain ⟨left, right, hleft, hright, remaining⟩ := check_branch accepted
      refine Option.bind_eq_some_iff.mpr ⟨left, ihyes hleft, ?_⟩
      refine Option.bind_eq_some_iff.mpr ⟨right, ihno hright, ?_⟩
      exact continueExits_extension (fun _ _ checked => ihnext checked) remaining
  | loop body next ihbody ihnext =>
      obtain ⟨iterations, endState, hbody, invariant, hnext, rfl⟩ := check_loop accepted
      have passed : (iterations.all fun exit => exit.kind == .returned || exit.state == state) = true := by
        simpa only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq] using invariant
      refine Option.bind_eq_some_iff.mpr ⟨iterations, ihbody hbody, ?_⟩
      refine Option.bind_eq_some_iff.mpr ⟨(), by simp [require, passed], ?_⟩
      exact Option.bind_eq_some_iff.mpr ⟨endState, ihnext hnext, rfl⟩

theorem checked_function_extension {before after : List Signature} {f : Function}
    (extension : Supports before after) (accepted : checkFunction before f = true) :
    checkFunction after f = true := by
  unfold checkFunction at accepted ⊢
  cases checked : check before f.signature f.body (initial f.signature) with
  | none => simp [checked] at accepted
  | some outcomes =>
      have extended := check_extension extension checked
      simpa [checked, extended] using accepted

theorem require_passed {condition : Bool} (accepted : require condition = some ()) :
    condition = true := by
  unfold require at accepted
  split at accepted
  · assumption
  · simp at accepted

/-- Matching allocator names is enforced for owned inputs and owned outputs,
not inferred from a shared C pointer representation. -/
theorem owned_invocation_allocator_agreement {environment : List Signature}
    {caller target : Signature} {first last : State} {arguments : List (Nat × Kind)}
    (found : environment.find? (fun signature => signature.name == target.name) = some target)
    (owned : transfersOwner target = true)
    (enabled : transition environment caller first (.invoke target.name arguments) = some last) :
    target.allocator = caller.allocator := by
  obtain ⟨witness, _, remaining⟩ := Option.bind_eq_some_iff.mp enabled
  obtain ⟨selected, selectedFound, remaining⟩ := Option.bind_eq_some_iff.mp remaining
  have same : selected = target := Option.some.inj (selectedFound.symm.trans found)
  subst selected
  obtain ⟨witness, _, remaining⟩ := Option.bind_eq_some_iff.mp remaining
  obtain ⟨witness, _, remaining⟩ := Option.bind_eq_some_iff.mp remaining
  obtain ⟨witness, brand, _⟩ := Option.bind_eq_some_iff.mp remaining
  cases witness
  simpa [owned] using require_passed brand

theorem checked_owned_return {environment : List Signature} {f : Function} {outcome : Exit}
    (accepted : checkFunction environment f = true) (result : f.signature.result = .own)
    (execution : Execution environment f.signature f.body (initial f.signature) outcome) :
    outcome.state.ownedResult = true ∧ outcome.state.borrowedResult = none := by
  have contract := (checked_function_return accepted execution).2
  simp only [returnAllowed, result, BEq.rfl, ↓reduceIte, Bool.and_eq_true,
    Option.isNone_iff_eq_none] at contract
  exact contract.2

theorem checked_borrowed_return {environment : List Signature} {f : Function}
    {outcome : Exit} {root : Nat} {kind : Kind}
    (accepted : checkFunction environment f = true)
    (result : f.signature.result.permission = some kind) (borrowed : kind.loan = true)
    (source : f.signature.sourceParameter = some root)
    (execution : Execution environment f.signature f.body (initial f.signature) outcome) :
    outcome.state.ownedResult = false ∧ outcome.state.borrowedResult = some (root, kind) := by
  have contract := (checked_function_return accepted execution).2
  have notOwned : f.signature.result ≠ .own := by
    intro same
    simp only [same, Slot.permission, Option.some.injEq] at result
    subst kind
    simp [Kind.loan] at borrowed
  simpa only [returnAllowed, beq_eq_false_iff_ne.mpr notOwned, Bool.false_eq_true,
    ↓reduceIte, result, source, Option.map_some, Bool.and_eq_true, Bool.not_eq_true, Bool.not_eq_true',
    beq_iff_eq] using (Bool.and_eq_true_iff.mp contract).2

end Mettapedia.GSLT.LanguageDef.CheckedBytes
