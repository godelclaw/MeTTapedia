import Mettapedia.GSLT.LanguageDef.CheckedBytePlans

/-!
# Control-flow safety of byte-buffer permission plans

Execution permits either branch and any finite number of loop iterations.
Admission covers all such executions, not one sampled path or a loop-unroll
bound. Native calls are interpreted by their declared permission transitions.
This does not claim that arbitrary native implementations meet those contracts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CheckedBytes

inductive Execution (environment : List Signature) (signature : Signature) :
    Plan → State → Exit → Prop where
  | done (s : State) : Execution environment signature .done s ⟨.normal, s⟩
  | step {s after : State} {action : Action} {next : Plan} {outcome : Exit}
      (enabled : apply environment signature s action = some after)
      (rest : Execution environment signature next after outcome) :
      Execution environment signature (.step action next) s outcome
  | ret (s : State) : Execution environment signature .ret s ⟨.returned, s⟩
  | breakLoop (s : State) : Execution environment signature .breakLoop s ⟨.broke, s⟩
  | continueLoop (s : State) : Execution environment signature .continueLoop s ⟨.continued, s⟩
  | branchNormal {yes no next : Plan} {s after : State} {outcome : Exit}
      (choice : Bool)
      (branch : Execution environment signature (if choice then yes else no) s ⟨.normal, after⟩)
      (rest : Execution environment signature next after outcome) :
      Execution environment signature (.branch yes no next) s outcome
  | branchAbrupt {yes no next : Plan} {s : State} {outcome : Exit}
      (choice : Bool)
      (branch : Execution environment signature (if choice then yes else no) s outcome)
      (abrupt : outcome.kind ≠ .normal) :
      Execution environment signature (.branch yes no next) s outcome
  | loopStop {body next : Plan} {s : State} {outcome : Exit}
      (rest : Execution environment signature next s outcome) :
      Execution environment signature (.loop body next) s outcome
  | loopBreak {body next : Plan} {s after : State} {outcome : Exit}
      (iteration : Execution environment signature body s ⟨.broke, after⟩)
      (rest : Execution environment signature next after outcome) :
      Execution environment signature (.loop body next) s outcome
  | loopReturn {body next : Plan} {s after : State}
      (iteration : Execution environment signature body s ⟨.returned, after⟩) :
      Execution environment signature (.loop body next) s ⟨.returned, after⟩
  | loopAgain {body next : Plan} {s : State} {iterationExit outcome : Exit}
      (iteration : Execution environment signature body s iterationExit)
      (repeats : iterationExit.kind = .normal ∨ iterationExit.kind = .continued)
      (rest : Execution environment signature (.loop body next) iterationExit.state outcome) :
      Execution environment signature (.loop body next) s outcome

theorem continueExits_cons {run : State → Option (List Exit)}
    {first : Exit} {rest outputs : List Exit}
    (accepted : continueExits run (first :: rest) = some outputs) :
    ∃ initial remaining,
      (if first.kind == .normal then run first.state else some [first]) = some initial ∧
      continueExits run rest = some remaining ∧ outputs = initial ++ remaining := by
  obtain ⟨initial, hfirst, tail⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨remaining, hrest, same⟩ := Option.bind_eq_some_iff.mp tail
  exact ⟨initial, remaining, hfirst, hrest, (Option.some.inj same).symm⟩

theorem continueExits_normal {run : State → Option (List Exit)} {inputs outputs : List Exit}
    (accepted : continueExits run inputs = some outputs)
    {state : State} (member : Exit.mk .normal state ∈ inputs) :
    ∃ next, run state = some next ∧ ∀ exit ∈ next, exit ∈ outputs := by
  induction inputs generalizing outputs with
  | nil => simp at member
  | cons first rest ih =>
      obtain ⟨initial, remaining, hfirst, hrest, rfl⟩ := continueExits_cons accepted
      rcases List.mem_cons.mp member with same | later
      · subst first
        exact ⟨initial, by simpa using hfirst,
          fun _ present => List.mem_append_left _ present⟩
      · obtain ⟨next, checked, included⟩ := ih hrest later
        exact ⟨next, checked, fun exit present =>
          List.mem_append_right _ (included exit present)⟩

theorem continueExits_abrupt {run : State → Option (List Exit)} {inputs outputs : List Exit}
    (accepted : continueExits run inputs = some outputs) {exit : Exit}
    (member : exit ∈ inputs) (abrupt : exit.kind ≠ .normal) : exit ∈ outputs := by
  induction inputs generalizing outputs with
  | nil => simp at member
  | cons first rest ih =>
      obtain ⟨initial, remaining, hfirst, hrest, rfl⟩ := continueExits_cons accepted
      rcases List.mem_cons.mp member with same | later
      · subst first
        have singleton : initial = [exit] := by simpa [abrupt] using hfirst.symm
        subst initial
        exact List.mem_append_left _ (by simp)
      · exact List.mem_append_right _ (ih hrest later)

theorem check_step {environment : List Signature} {signature : Signature}
    {action : Action} {next : Plan} {state : State} {outputs : List Exit}
    (accepted : check environment signature (.step action next) state = some outputs) :
    ∃ after, apply environment signature state action = some after ∧
      check environment signature next after = some outputs := by
  exact Option.bind_eq_some_iff.mp accepted

theorem check_branch {environment : List Signature} {signature : Signature}
    {yes no next : Plan} {state : State} {outputs : List Exit}
    (accepted : check environment signature (.branch yes no next) state = some outputs) :
    ∃ left right, check environment signature yes state = some left ∧
      check environment signature no state = some right ∧
      continueExits (check environment signature next) (left ++ right) = some outputs := by
  obtain ⟨left, hleft, rest⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨right, hright, combined⟩ := Option.bind_eq_some_iff.mp rest
  exact ⟨left, right, hleft, hright, combined⟩

theorem check_loop {environment : List Signature} {signature : Signature}
    {body next : Plan} {state : State} {outputs : List Exit}
    (accepted : check environment signature (.loop body next) state = some outputs) :
    ∃ iterations after, check environment signature body state = some iterations ∧
      (∀ exit ∈ iterations, exit.kind = .returned ∨ exit.state = state) ∧
      check environment signature next state = some after ∧
      outputs = iterations.filter (fun exit => exit.kind == .returned) ++ after := by
  obtain ⟨iterations, hbody, rest⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨guard, invariant, rest⟩ := Option.bind_eq_some_iff.mp rest
  cases guard
  have passed : (iterations.all fun exit => exit.kind == .returned || exit.state == state) = true := by
    unfold require at invariant
    split at invariant
    · assumption
    · simp at invariant
  obtain ⟨after, hnext, same⟩ := Option.bind_eq_some_iff.mp rest
  refine ⟨iterations, after, hbody, ?_, hnext, (Option.some.inj same).symm⟩
  simpa only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq] using passed

/-- Every finite execution, including arbitrary loop repetition, is covered
by the checker. Branch tests and loop conditions are erased to nondeterminism. -/
theorem check_covers_execution {environment : List Signature} {signature : Signature}
    {plan : Plan} {state : State} {outcome : Exit}
    (execution : Execution environment signature plan state outcome)
    {outputs : List Exit}
    (accepted : check environment signature plan state = some outputs) : outcome ∈ outputs := by
  induction execution generalizing outputs with
  | done => simp only [check, Option.some.injEq] at accepted; subst outputs; simp
  | step enabled rest ih =>
      obtain ⟨after, enabled', checked⟩ := check_step accepted
      have same := Option.some.inj (enabled.symm.trans enabled')
      subst after
      exact ih checked
  | ret =>
      simp only [check, require] at accepted
      split at accepted
      · simp only [bind, Option.bind, pure, Option.some.injEq] at accepted
        subst outputs
        simp
      · simp at accepted
  | breakLoop => simp only [check, Option.some.injEq] at accepted; subst outputs; simp
  | continueLoop => simp only [check, Option.some.injEq] at accepted; subst outputs; simp
  | @branchNormal yes no next s after outcome choice branch rest ihbranch ihrest =>
      obtain ⟨left, right, hleft, hright, combined⟩ := check_branch accepted
      have member : Exit.mk .normal after ∈ left ++ right := by
        cases choice with
        | false => exact List.mem_append_right _ (ihbranch hright)
        | true => exact List.mem_append_left _ (ihbranch hleft)
      obtain ⟨next, checked, included⟩ := continueExits_normal combined member
      exact included _ (ihrest checked)
  | branchAbrupt choice branch abrupt ihbranch =>
      obtain ⟨left, right, hleft, hright, combined⟩ := check_branch accepted
      apply continueExits_abrupt combined _ abrupt
      cases choice with
      | false => exact List.mem_append_right _ (ihbranch hright)
      | true => exact List.mem_append_left _ (ihbranch hleft)
  | loopStop rest ih =>
      obtain ⟨iterations, after, _, _, hnext, same⟩ := check_loop accepted
      rw [same]
      exact List.mem_append_right _ (ih hnext)
  | loopBreak iteration rest ihiteration ihrest =>
      obtain ⟨iterations, after, hbody, invariant, hnext, same⟩ := check_loop accepted
      have member := ihiteration hbody
      have equal : _ = _ := (invariant _ member).resolve_left (by simp)
      subst equal
      rw [same]
      exact List.mem_append_right _ (ihrest hnext)
  | loopReturn iteration ih =>
      obtain ⟨iterations, after, hbody, _, _, same⟩ := check_loop accepted
      rw [same]
      exact List.mem_append_left _ (List.mem_filter.mpr ⟨ih hbody, by simp⟩)
  | @loopAgain body next s iterationExit outcome iteration repeats rest ihiteration ihrest =>
      obtain ⟨iterations, after, hbody, invariant, hnext, same⟩ := check_loop accepted
      have member := ihiteration hbody
      have different : iterationExit.kind ≠ ExitKind.returned := by rcases repeats with h | h <;> simp [h]
      have equal := (invariant _ member).resolve_left different
      exact ihrest (by simpa [equal] using accepted)

theorem Execution.valid {environment : List Signature} {signature : Signature}
    {plan : Plan} {first : State} {outcome : Exit}
    (execution : Execution environment signature plan first outcome)
    (valid : Valid first) : Valid outcome.state := by
  induction execution with
  | done | ret | breakLoop | continueLoop => exact valid
  | step enabled rest ih => exact ih (apply_valid enabled)
  | branchNormal choice branch rest ihbranch ihrest => exact ihrest (ihbranch valid)
  | branchAbrupt choice branch abrupt ih => exact ih valid
  | loopStop rest ih => exact ih valid
  | loopBreak iteration rest ihiteration ihrest => exact ihrest (ihiteration valid)
  | loopReturn iteration ih => exact ih valid
  | loopAgain iteration repeats rest ihiteration ihrest => exact ihrest (ihiteration valid)

theorem continueExits_property {run : State → Option (List Exit)}
    {inputs outputs : List Exit} {property : Exit → Prop}
    (accepted : continueExits run inputs = some outputs)
    (initial : ∀ exit ∈ inputs, property exit)
    (continuation : ∀ state next, run state = some next → ∀ exit ∈ next, property exit) :
    ∀ exit ∈ outputs, property exit := by
  induction inputs generalizing outputs with
  | nil => simp [continueExits] at accepted; subst outputs; simp
  | cons first rest ih =>
      obtain ⟨before, after, hfirst, hrest, rfl⟩ := continueExits_cons accepted
      intro exit member
      rcases List.mem_append.mp member with early | late
      · by_cases normal : first.kind = .normal
        · exact continuation first.state before (by simpa [normal] using hfirst) exit early
        · have same : before = [first] := by simpa [normal] using hfirst.symm
          rw [same] at early
          have equal := List.mem_singleton.mp early
          subst exit
          exact initial first (by simp)
      · exact ih hrest (fun outcome present => initial outcome (by simp [present])) exit late

/-- Every checked return has completed cleanup and recorded the declared
transfer or borrowed origin. The assertion is independent of termination. -/
theorem check_return_contract {environment : List Signature} {signature : Signature}
    {plan : Plan} {state : State} {outputs : List Exit}
    (accepted : check environment signature plan state = some outputs) :
    ∀ exit ∈ outputs, exit.kind = .returned → returnAllowed signature exit.state = true := by
  induction plan generalizing state outputs with
  | done => simp [check] at accepted; subst outputs; simp
  | step action next ih =>
      obtain ⟨after, _, checked⟩ := check_step accepted
      exact ih checked
  | ret =>
      unfold check at accepted
      obtain ⟨guard, hguard, same⟩ := Option.bind_eq_some_iff.mp accepted
      cases guard
      have allowed : returnAllowed signature state = true := by
        unfold require at hguard
        split at hguard
        · assumption
        · simp at hguard
      have equal : outputs = [⟨.returned, state⟩] := (Option.some.inj same).symm
      subst outputs
      simpa using allowed
  | breakLoop => simp [check] at accepted; subst outputs; simp
  | continueLoop => simp [check] at accepted; subst outputs; simp
  | branch yes no next ihyes ihno ihnext =>
      obtain ⟨left, right, hleft, hright, joined⟩ := check_branch accepted
      apply continueExits_property (property := fun exit =>
        exit.kind = .returned → returnAllowed signature exit.state = true) joined
      · intro exit member
        rcases List.mem_append.mp member with before | after
        · exact ihyes hleft exit before
        · exact ihno hright exit after
      · intro after exits checked
        exact ihnext checked
  | loop body next ihbody ihnext =>
      obtain ⟨iterations, after, hbody, _, hnext, rfl⟩ := check_loop accepted
      intro exit member
      rcases List.mem_append.mp member with before | later
      · exact ihbody hbody exit (List.mem_filter.mp before).1
      · exact ihnext hnext exit later

theorem checked_function_return {environment : List Signature} {f : Function}
    {outcome : Exit} (accepted : checkFunction environment f = true)
    (execution : Execution environment f.signature f.body (initial f.signature) outcome) :
    outcome.kind = .returned ∧ returnAllowed f.signature outcome.state = true := by
  have result := (Bool.and_eq_true_iff.mp accepted).2
  cases checked : check environment f.signature f.body (initial f.signature) with
  | none => simp [checked] at result
  | some outputs =>
      simp only [checked] at result
      have member := check_covers_execution execution checked
      have all : ∀ exit ∈ outputs, exit.kind = .returned := by
        simpa only [List.all_eq_true, beq_iff_eq] using (Bool.and_eq_true_iff.mp result).2
      exact ⟨all outcome member, check_return_contract checked outcome member (all outcome member)⟩

theorem checked_function_no_local_leak {environment : List Signature} {f : Function}
    {outcome : Exit} (accepted : checkFunction environment f = true)
    (execution : Execution environment f.signature f.body (initial f.signature) outcome) :
    outcome.state.cells = [] := by
  have contract := (checked_function_return accepted execution).2
  unfold returnAllowed at contract
  exact List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp contract).1

end Mettapedia.GSLT.LanguageDef.CheckedBytes
