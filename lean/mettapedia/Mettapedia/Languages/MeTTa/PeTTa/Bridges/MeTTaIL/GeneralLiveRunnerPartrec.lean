import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralLiveRunnerExecution
import Mettapedia.OSLF.NativeTypes.Instances.Partrec.Comparison
import Mettapedia.Languages.PartrecMachine.Adequacy

/-!
# The universal machine through the live runner

The partial-recursive machine of `Languages/PartrecMachine` is an admitted plan, so the authored
live runner runs it on PeTTa. Started at the pending evaluation of a code `c` on an input `v`:

- `run_reaches`: every state the runner reaches is reached by the machine's own reductions;
- `halts_of_done`: if the runner ends normally, it ends at `Halt w` with `w ∈ c.eval v`;
- `running_of_diverges`: if `c` has no value on `v`, the runner runs for ever: after every number of
  ticks it is still running;
- `done_of_halts`: if `w ∈ c.eval v`, then with any positive quantum the runner ends normally at
  `Halt w` after finitely many ticks.

Together with `GeneralLiveRunnerExecution.advance_returns`, the actual PeTTa execution of the
authored runner computes Mathlib's partial recursive functions, and diverges exactly where they do.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralLiveRunnerPartrec

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.PartrecMachine
open Turing.ToPartrec
open GeneralLiveRunnerExecution

/-! ## The plan -/

/-- Partrec's admitted plan, on closed configurations. -/
def spec : Spec := ⟨Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan, [], .base "Cfg"⟩

theorem stratified : GeneralPremise.checkStepStratification
    (GeneralPlanEnvironment.environment spec.plan).language = true := by
  cbv

theorem static : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment spec.plan) = true := by
  cbv

theorem finiteProvider : spec.plan.snapshot.provider.dynamicRelations = [] := rfl

/-- A valid receipt is a reduction of the original machine. -/
theorem valid_reduces {state : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid spec.plan spec.bound spec.expected state) : Reduces state receipt.target :=
  reduces_iff_mem_rootReducts.mpr
    (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Comparison.primitive_to_original [] valid)

/-- On well-sorted states the plan's step is the machine's reduction. -/
theorem step_iff {state target : Pattern} (typed : spec.Typed state) :
    spec.Step state target ↔ Reduces state target :=
  Mettapedia.OSLF.NativeTypes.Instances.Partrec.Comparison.generated_step_iff_original [] typed

/-! ## Encoded configurations are well-sorted -/

private abbrev language : LanguageDef := spec.plan.snapshot.language
private abbrev free : FreeTypeContext := spec.plan.snapshot.free

private theorem rule_typed (index : Nat) (bounded : index < terms.length) {arguments : List Pattern}
    (notBare : ¬ UsesBareCollection terms[index])
    (typed : ArgumentsHaveTypes language free [] arguments terms[index].params) :
    HasType language free [] (.apply terms[index].label arguments) (.base terms[index].category) :=
  HasType.constructor (List.getElem_mem bounded) notBare typed

private theorem not_bare (index : Nat) (bounded : index < terms.length) : ¬ UsesBareCollection terms[index] := by
  rintro ⟨_, _, _, same⟩
  have length : terms.length = 19 := rfl
  rw [length] at bounded
  interval_cases index <;> simp [terms] at same

private theorem argument {argument : Pattern} {arguments : List Pattern} {name : String} {sort : String}
    {parameters : List TermParam} (typed : HasType language free [] argument (.base sort))
    (rest : ArgumentsHaveTypes language free [] arguments parameters) :
    ArgumentsHaveTypes language free [] (argument :: arguments) (.simple name (.base sort) :: parameters) :=
  .cons trivial rfl typed rest

theorem encNat_typed (n : ℕ) : HasType language free [] (encNat n) (.base "Nat") := by
  induction n with
  | zero => exact rule_typed 0 (by decide) (not_bare 0 (by decide)) .nil
  | succ n ih => exact rule_typed 1 (by decide) (not_bare 1 (by decide)) (argument ih .nil)

theorem encNats_typed (v : List ℕ) : HasType language free [] (encNats v) (.base "Nats") := by
  induction v with
  | nil => exact rule_typed 2 (by decide) (not_bare 2 (by decide)) .nil
  | cons n v ih => exact rule_typed 3 (by decide) (not_bare 3 (by decide)) (argument (encNat_typed n) (argument ih .nil))

theorem encCode_typed (c : Code) : HasType language free [] (encCode c) (.base "Code") := by
  induction c with
  | zero' => exact rule_typed 4 (by decide) (not_bare 4 (by decide)) .nil
  | succ => exact rule_typed 5 (by decide) (not_bare 5 (by decide)) .nil
  | tail => exact rule_typed 6 (by decide) (not_bare 6 (by decide)) .nil
  | cons f fs hf hfs => exact rule_typed 7 (by decide) (not_bare 7 (by decide)) (argument hf (argument hfs .nil))
  | comp f g hf hg => exact rule_typed 8 (by decide) (not_bare 8 (by decide)) (argument hf (argument hg .nil))
  | case f g hf hg => exact rule_typed 9 (by decide) (not_bare 9 (by decide)) (argument hf (argument hg .nil))
  | fix f hf => exact rule_typed 10 (by decide) (not_bare 10 (by decide)) (argument hf .nil)

theorem halt_cont_typed : HasType language free [] (encCont .halt) (.base "Cont") :=
  rule_typed 11 (by decide) (not_bare 11 (by decide)) .nil

theorem normalTerm_has_type (c : Code) (v : List ℕ) :
    HasType language free [] (normalTerm c .halt v) (.base "Cfg") :=
  rule_typed 18 (by decide) (not_bare 18 (by decide))
    (argument (encCode_typed c) (argument halt_cont_typed (argument (encNats_typed v) .nil)))

private theorem first_order_nat (n : ℕ) :
    (encNat n).hasCanonicalBinderMetadata = true ∧ isObjectPattern (encNat n) = true ∧
      (encNat n).isWellScopedAt 0 = true := by
  induction n with
  | zero => simp [encNat, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
      isObjectPattern, isObjectPatternList, Pattern.isWellScopedAt, Pattern.isWellScopedListAt]
  | succ n ih => simp_all [encNat, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
      isObjectPattern, isObjectPatternList, Pattern.isWellScopedAt, Pattern.isWellScopedListAt]

private theorem first_order_nats (v : List ℕ) :
    (encNats v).hasCanonicalBinderMetadata = true ∧ isObjectPattern (encNats v) = true ∧
      (encNats v).isWellScopedAt 0 = true := by
  induction v with
  | nil => simp [encNats, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
      isObjectPattern, isObjectPatternList, Pattern.isWellScopedAt, Pattern.isWellScopedListAt]
  | cons n v ih =>
    have head := first_order_nat n
    simp_all [encNats, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
      isObjectPattern, isObjectPatternList, Pattern.isWellScopedAt, Pattern.isWellScopedListAt]

private theorem first_order_code (c : Code) :
    (encCode c).hasCanonicalBinderMetadata = true ∧ isObjectPattern (encCode c) = true ∧
      (encCode c).isWellScopedAt 0 = true := by
  induction c <;> simp_all [encCode, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
      isObjectPattern, isObjectPatternList, Pattern.isWellScopedAt, Pattern.isWellScopedListAt]

/-- The pending evaluation of a code on an input is a well-sorted configuration. -/
theorem normalTerm_typed (c : Code) (v : List ℕ) : spec.Typed (normalTerm c .halt v) := by
  have code := first_order_code c
  have input := first_order_nats v
  refine ⟨normalTerm_has_type c v, ?_, ?_, ?_⟩ <;>
    simp_all [spec, normalTerm, encCont, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
      isObjectPattern, isObjectPatternList, ScopeSafeAt, Pattern.isWellScopedAt, Pattern.isWellScopedListAt]

/-! ## Runs -/

/-- The run from the pending evaluation of `c` on `v`. -/
def run (c : Code) (v : List ℕ) (ticks quantum : Nat) : Machine :=
  Machine.advance spec ticks quantum (Machine.begin spec (normalTerm c .halt v))

theorem run_reached (c : Code) (v : List ℕ) (ticks quantum : Nat) : spec.Reached (run c v ticks quantum) :=
  spec.run_reached _ ticks quantum

/-- **Every state is the machine's.** -/
theorem run_reaches (c : Code) (v : List ℕ) (ticks quantum : Nat) :
    Relation.ReflTransGen Reduces (normalTerm c .halt v) (run c v ticks quantum).state :=
  spec.advance_reaches valid_reduces quantum ticks (spec.begin_reached _)

theorem run_typed (c : Code) (v : List ℕ) (ticks quantum : Nat) : spec.Typed (run c v ticks quantum).state :=
  spec.advance_typed quantum ticks (spec.begin_reached _) (normalTerm_typed c v)

theorem inImage_of_reaches {source target : Pattern} (image : InImage source)
    (reaches : Relation.ReflTransGen Reduces source target) : InImage target := by
  induction reaches with
  | refl => exact image
  | tail _ step ih => exact reduct_inImage ih step

theorem run_inImage (c : Code) (v : List ℕ) (ticks quantum : Nat) : InImage (run c v ticks quantum).state :=
  inImage_of_reaches (.inl ⟨c, .halt, v, rfl⟩) (run_reaches c v ticks quantum)

/-- An image term that is not halted has a reduction. -/
theorem halted_or_reduces {term : Pattern} (image : InImage term) :
    (∃ w, term = encCfg (.halt w)) ∨ ∃ target, Reduces term target := by
  rcases image with ⟨c, k, v, rfl⟩ | ⟨cfg, rfl⟩
  · exact .inr ⟨_, reduces_normal_iff.mpr rfl⟩
  · cases cfg with
    | halt w => exact .inl ⟨w, rfl⟩
    | ret k v => exact .inr ⟨_, reduces_ret_iff.mpr rfl⟩

/-- **A normal ending is a halt with the evaluation's value.** -/
theorem halts_of_done {c : Code} {v : List ℕ} {ticks quantum : Nat}
    (done : (run c v ticks quantum).phase = .done) :
    ∃ w, (run c v ticks quantum).state = encCfg (.halt w) ∧ w ∈ c.eval v := by
  rcases halted_or_reduces (run_inImage c v ticks quantum) with ⟨w, halted⟩ | ⟨target, reduces⟩
  · refine ⟨w, halted, (adequacy c v w).mp ?_⟩
    rw [← halted]
    exact run_reaches c v ticks quantum
  · exact absurd ((step_iff (run_typed c v ticks quantum)).mpr reduces)
      (spec.done_no_step rfl stratified (run_reached c v ticks quantum) done target)

/-- The runner is never blocked on this machine. -/
theorem run_not_blocked (c : Code) (v : List ℕ) (ticks quantum : Nat) :
    (run c v ticks quantum).phase ≠ .blocked :=
  spec.not_blocked_of_static static finiteProvider (run_reached c v ticks quantum) (run_typed c v ticks quantum).2.1

/-- **Divergence is never mistaken for an ending.** If `c` has no value on `v`, the runner is
still running after every number of ticks, whatever the quantum. -/
theorem running_of_diverges {c : Code} {v : List ℕ} (diverges : ∀ w, w ∉ c.eval v) (ticks quantum : Nat) :
    (run c v ticks quantum).phase = .running := by
  cases phase : (run c v ticks quantum).phase with
  | running => rfl
  | done =>
    obtain ⟨w, _, member⟩ := halts_of_done phase
    exact absurd member (diverges w)
  | blocked => exact absurd phase (run_not_blocked c v ticks quantum)

/-- A reached machine at a well-sorted state with a reduction is not done, and never blocked. -/
private theorem running_of_reduces {machine : Machine} (reached : spec.Reached machine)
    (typed : spec.Typed machine.state) {target : Pattern} (reduces : Reduces machine.state target) :
    machine.phase = .running := by
  cases phase : machine.phase with
  | running => rfl
  | done => exact absurd ((step_iff typed).mpr reduces) (spec.done_no_step rfl stratified reached phase target)
  | blocked => exact absurd phase (spec.not_blocked_of_static static finiteProvider reached typed.2.1)

/-- From a reached machine whose state reduces to `Halt w`, some page ends normally there. -/
theorem done_of_reaches {w : List ℕ} {quantum : Nat} (positive : 0 < quantum) {state : Pattern}
    (reaches : Relation.ReflTransGen Reduces state (encCfg (.halt w))) :
    ∀ {machine : Machine}, spec.Reached machine → machine.state = state → spec.Typed state → InImage state →
    ∃ ticks, (Machine.advance spec ticks quantum machine).phase = .done ∧
      (Machine.advance spec ticks quantum machine).state = encCfg (.halt w) := by
  induction reaches using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro machine reached atState typed _
    cases phase : machine.phase with
    | done => exact ⟨0, phase, atState⟩
    | blocked => exact absurd phase (spec.not_blocked_of_static static finiteProvider reached (atState ▸ typed.2.1))
    | running =>
      rcases spec.stop_or_commit reached phase positive with ⟨ticks, stopped, kept⟩ |
          ⟨_, receipt, valid, _⟩
      · have later := spec.advance_reached ticks quantum reached
        refine ⟨ticks, ?_, kept.trans atState⟩
        cases final : (Machine.advance spec ticks quantum machine).phase with
        | done => rfl
        | running => exact absurd final stopped
        | blocked =>
          exact absurd final (spec.not_blocked_of_static static finiteProvider later (by rw [kept, atState]; exact typed.2.1))
      · rw [atState] at valid
        exact absurd (valid_reduces valid) (halt_irreducible w _)
  | @head current next first _ ih =>
    intro machine reached atState typed image
    have running := running_of_reduces reached (atState ▸ typed) (atState ▸ first)
    rcases spec.stop_or_commit reached running positive with ⟨ticks, stopped, kept⟩ |
        ⟨ticks, receipt, valid, committed⟩
    · have later := spec.advance_reached ticks quantum reached
      have stillRunning := running_of_reduces later (by rw [kept, atState]; exact typed)
        (by rw [kept, atState]; exact first)
      exact absurd stillRunning stopped
    · rw [atState] at valid
      have same : receipt.target = next := reduces_deterministic image (valid_reduces valid) first
      have later := spec.advance_reached ticks quantum reached
      rw [committed] at later
      obtain ⟨more, done, halted⟩ := ih later same (same ▸ spec.typed_of_valid valid)
        (reduct_inImage image first)
      refine ⟨ticks + more, ?_, ?_⟩
      · rw [Machine.advance_add, committed]; exact done
      · rw [Machine.advance_add, committed]; exact halted

/-- **Halting is reached.** If `w ∈ c.eval v`, then under any positive quantum some page of the
runner ends normally at `Halt w`. -/
theorem done_of_halts {c : Code} {v w : List ℕ} (halts : w ∈ c.eval v) {quantum : Nat} (positive : 0 < quantum) :
    ∃ ticks, (run c v ticks quantum).phase = .done ∧ (run c v ticks quantum).state = encCfg (.halt w) :=
  done_of_reaches positive ((adequacy c v w).mpr halts) (spec.begin_reached _) rfl (normalTerm_typed c v)
    (.inl ⟨c, .halt, v, rfl⟩)

/-- **The runner computes the partial recursive functions.** It ends normally at `Halt w` for some
page exactly when `w ∈ c.eval v`. -/
theorem done_iff {c : Code} {v w : List ℕ} {quantum : Nat} (positive : 0 < quantum) :
    (∃ ticks, (run c v ticks quantum).phase = .done ∧ (run c v ticks quantum).state = encCfg (.halt w)) ↔
      w ∈ c.eval v := by
  constructor
  · rintro ⟨ticks, done, halted⟩
    obtain ⟨output, state, member⟩ := halts_of_done done
    rw [halted] at state
    have same := encCfg_injective state
    cases same
    exact member
  · intro halts
    exact done_of_halts halts positive

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralLiveRunnerPartrec
