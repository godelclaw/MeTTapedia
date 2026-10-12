import Mettapedia.Languages.Dataflow.Semantics
import Mettapedia.Machines.ResumableRegion
import Mettapedia.Machines.OwnedPullDriverCost

/-!
# Data-driven execution and adequacy

Kahn-style execution: a state carries the cells computed so far and the
instructions still pending, and a step fires *any* pending instruction whose
operands are already available.  No program counter and no schedule is
imposed — the write/read dependency is the only ordering.

The results:

* `Step.pending_length_lt` — firing strictly decreases the pending count, so
  every run is finite (`Steps.length_le`);
* `Invariant.step` — the reachability invariant is preserved;
* `progress` — a well-formed program with pending work always has a step:
  no deadlock;
* `terminal_result_eq_denote` — **the crown**: every terminal state of every
  run assigns the returned cell exactly its denotation.

Schedule independence of the answer is then a corollary
(`terminal_result_unique`), because the denotation is a function: it needs
no confluence argument.  The diamond property proved at the end is about
*states*, which is the stronger statement the process-calculus layer will
need.
-/

namespace Mettapedia.Languages.Dataflow

variable {Op Value : Type}

/-! ## Readiness -/

/-- Evaluate an operand vector against the computed environment. -/
def evalOperands (env : List (CellId × Value)) :
    List CellId → Option (List Value)
  | [] => some []
  | c :: cs =>
      match lookup env c with
      | none => none
      | some v =>
          match evalOperands env cs with
          | none => none
          | some vs => some (v :: vs)

/-- The value an instruction produces, when its operands are available. -/
def readyValue (spec : PureOperatorSpec Op Value)
    (env : List (CellId × Value)) : Instruction Op Value → Option Value
  | .const _ v => some v
  | .apply _ op operands =>
      if operands.length = spec.arity op then
        match evalOperands env operands with
        | some values => some (spec.apply op values)
        | none => none
      else
        none

@[simp] theorem readyValue_const (spec : PureOperatorSpec Op Value)
    (env : List (CellId × Value)) (d : CellId) (v : Value) :
    readyValue spec env (.const d v) = some v := rfl

/-- Operand evaluation succeeds exactly when every operand is available. -/
theorem evalOperands_isSome_of_forall {env : List (CellId × Value)} :
    ∀ {cs : List CellId}, (∀ c ∈ cs, (lookup env c).isSome) →
      ∃ vs, evalOperands env cs = some vs := by
  intro cs
  induction cs with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons c cs inductionHypothesis =>
      intro available
      obtain ⟨v, headValue⟩ := Option.isSome_iff_exists.mp
        (available c (List.mem_cons_self ..))
      obtain ⟨vs, tailValues⟩ := inductionHypothesis
        (fun d member => available d (List.mem_cons_of_mem _ member))
      exact ⟨v :: vs, by simp [evalOperands, headValue, tailValues]⟩

/-- If an operand vector fails to evaluate, some operand is unavailable. -/
theorem exists_unavailable_of_evalOperands_none {env : List (CellId × Value)} :
    ∀ {cs : List CellId}, evalOperands env cs = none →
      ∃ c ∈ cs, lookup env c = none := by
  intro cs
  induction cs with
  | nil => intro failed; simp [evalOperands] at failed
  | cons c cs inductionHypothesis =>
      intro failed
      cases headValue : lookup env c with
      | none => exact ⟨c, List.mem_cons_self .., headValue⟩
      | some v =>
          cases tailValues : evalOperands env cs with
          | none =>
              obtain ⟨d, member, missing⟩ := inductionHypothesis tailValues
              exact ⟨d, List.mem_cons_of_mem _ member, missing⟩
          | some vs =>
              simp [evalOperands, headValue, tailValues] at failed

/-- Operand evaluation depends only on the bindings it actually names. -/
theorem evalOperands_eq_of_agreement (left right : List (CellId × Value))
    (operands : List CellId)
    (agrees : ∀ cell ∈ operands, lookup left cell = lookup right cell) :
    evalOperands left operands = evalOperands right operands := by
  induction operands with
  | nil => rfl
  | cons cell cells inductionHypothesis =>
      have head := agrees cell (by simp)
      have tail := inductionHypothesis (fun observed member => agrees observed (by simp [member]))
      simp only [evalOperands, head, tail]

/-- Agreement on the actual operand footprint preserves complete readiness,
including missing operands and arity rejection. -/
theorem readyValue_eq_of_agreement (spec : PureOperatorSpec Op Value)
    (left right : List (CellId × Value)) (instruction : Instruction Op Value)
    (agrees : ∀ cell ∈ instruction.operands, lookup left cell = lookup right cell) :
    readyValue spec left instruction = readyValue spec right instruction := by
  cases instruction with
  | const _ _ => rfl
  | apply destination operator operands =>
      have same := evalOperands_eq_of_agreement left right operands agrees
      simp only [readyValue, same]

/-! ## States and steps -/

/-- Execution state: the environment computed so far, and the instructions
still to fire. -/
structure State (Op Value : Type) where
  computed : List (CellId × Value)
  pending : List (Instruction Op Value)

/-- Execution starts with the inputs available and everything pending. -/
def Program.initialState (p : Program Op Value) : State Op Value :=
  ⟨p.inputs, p.instructions⟩

/-- One firing: any ready pending instruction, in any position. -/
inductive Step (spec : PureOperatorSpec Op Value) :
    State Op Value → State Op Value → Prop where
  | fire {computed : List (CellId × Value)}
      {pre post : List (Instruction Op Value)} {i : Instruction Op Value}
      {v : Value} (ready : readyValue spec computed i = some v) :
      Step spec ⟨computed, pre ++ i :: post⟩
        ⟨(i.dst, v) :: computed, pre ++ post⟩

/-- Reflexive-transitive execution. -/
abbrev Steps (spec : PureOperatorSpec Op Value) :
    State Op Value → State Op Value → Prop :=
  Relation.ReflTransGen (Step spec)

/-- Firing strictly decreases the pending count: every run is finite. -/
theorem Step.pending_length_lt {spec : PureOperatorSpec Op Value}
    {s s' : State Op Value} (step : Step spec s s') :
    s'.pending.length < s.pending.length := by
  cases step with
  | fire _ => simp

/-- A run cannot be longer than the initial pending count. -/
theorem Steps.pending_length_le {spec : PureOperatorSpec Op Value}
    {s s' : State Op Value} (run : Steps spec s s') :
    s'.pending.length ≤ s.pending.length := by
  induction run with
  | refl => exact Nat.le_refl _
  | tail _ step inductionHypothesis =>
      exact Nat.le_trans (Nat.le_of_lt step.pending_length_lt)
        inductionHypothesis

/-! ## Well-formedness -/

/-- The arity obligation an instruction carries. -/
def Instruction.arityOk (spec : PureOperatorSpec Op Value) :
    Instruction Op Value → Bool
  | .const _ _ => true
  | .apply _ op operands => operands.length == spec.arity op

/-- A program is well formed when writers are unique, inputs are distinct
and unwritten, arities agree, and every instruction destination and the
returned cell denote.  The last condition is where definedness and
acyclicity live: a cell on a dependency cycle denotes nothing. -/
structure Program.WellFormed (spec : PureOperatorSpec Op Value)
    (p : Program Op Value) : Prop where
  writersUnique : (p.instructions.map Instruction.dst).Nodup
  inputsUnique : (p.inputs.map Prod.fst).Nodup
  inputsNotWritten : ∀ i ∈ p.instructions, p.inputValue? i.dst = none
  aritiesOk : ∀ i ∈ p.instructions, i.arityOk spec = true
  destinationsDenote : ∀ i ∈ p.instructions, ∃ v, Denotes spec p i.dst v
  resultDenotes : ∃ v, Denotes spec p p.result v

/-- In a list of instructions with distinct destinations, searching by an
instruction's own destination finds that instruction. -/
theorem find?_dst_eq_self :
    ∀ {l : List (Instruction Op Value)}, (l.map Instruction.dst).Nodup →
      ∀ {i : Instruction Op Value}, i ∈ l →
        l.find? (fun j => j.dst == i.dst) = some i := by
  intro l
  induction l with
  | nil => intro _ i member; cases member
  | cons head tail inductionHypothesis =>
      intro unique i member
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases List.mem_cons.mp member with rfl | tailMember
      · rw [List.find?_cons_of_pos (by simp)]
      · have headNe : head.dst ≠ i.dst := fun h =>
          unique.1 (h ▸ List.mem_map_of_mem tailMember)
        rw [List.find?_cons_of_neg (by simpa using headNe)]
        exact inductionHypothesis unique.2 tailMember

/-- In a program with unique writers, an instruction is *the* writer of its
own destination. -/
theorem writerOf_eq_self {p : Program Op Value}
    (unique : (p.instructions.map Instruction.dst).Nodup)
    {i : Instruction Op Value} (member : i ∈ p.instructions) :
    p.writerOf? i.dst = some i :=
  find?_dst_eq_self unique member

/-! ## Soundness of firing -/

/-- Operand evaluation against a denoting environment denotes. -/
theorem evalOperands_denotes {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} {env : List (CellId × Value)}
    (sound : ∀ c v, lookup env c = some v → Denotes spec p c v) :
    ∀ {cs : List CellId} {vs : List Value}, evalOperands env cs = some vs →
      DenotesList spec p cs vs := by
  intro cs
  induction cs with
  | nil =>
      intro vs evaluated
      have : vs = [] := by simpa [evalOperands] using evaluated.symm
      subst this
      exact DenotesList.nil
  | cons c cs inductionHypothesis =>
      intro vs evaluated
      cases headValue : lookup env c with
      | none => simp [evalOperands, headValue] at evaluated
      | some v =>
          cases tailValues : evalOperands env cs with
          | none => simp [evalOperands, headValue, tailValues] at evaluated
          | some tail =>
              simp only [evalOperands, headValue, tailValues,
                Option.some.injEq] at evaluated
              subst evaluated
              exact DenotesList.cons (sound c v headValue)
                (inductionHypothesis tailValues)

/-- A fired instruction's value is the denotation of its destination. -/
theorem readyValue_denotes {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} (wf : p.WellFormed spec)
    {env : List (CellId × Value)}
    (sound : ∀ c v, lookup env c = some v → Denotes spec p c v)
    {i : Instruction Op Value} (member : i ∈ p.instructions) {v : Value}
    (ready : readyValue spec env i = some v) : Denotes spec p i.dst v := by
  cases i with
  | const d constValue =>
      have writer := writerOf_eq_self wf.writersUnique member
      have notInput := wf.inputsNotWritten _ member
      simp only [readyValue_const, Option.some.injEq] at ready
      subst ready
      exact Denotes.const notInput (by simpa using writer)
  | apply d op operands =>
      have writer := writerOf_eq_self wf.writersUnique member
      have notInput := wf.inputsNotWritten _ member
      have arity : operands.length = spec.arity op := by
        have := wf.aritiesOk _ member
        simpa [Instruction.arityOk] using this
      simp only [readyValue, if_pos arity] at ready
      cases operandValues : evalOperands env operands with
      | none => rw [operandValues] at ready; cases ready
      | some values =>
          rw [operandValues] at ready
          have valueEq : spec.apply op values = v := by simpa using ready
          subst valueEq
          exact Denotes.apply notInput (by simpa using writer) arity
            (evalOperands_denotes sound operandValues)

/-! ## The reachability invariant -/

/-- What holds of every state reachable from the initial one. -/
structure Invariant (spec : PureOperatorSpec Op Value)
    (p : Program Op Value) (s : State Op Value) : Prop where
  sound : ∀ c v, lookup s.computed c = some v → Denotes spec p c v
  pendingSublist : s.pending.Sublist p.instructions
  firedComputed : ∀ i ∈ p.instructions, i ∉ s.pending →
    (lookup s.computed i.dst).isSome
  inputsPresent : ∀ c v, p.inputValue? c = some v →
    lookup s.computed c = some v
  pendingNotComputed : ∀ i ∈ s.pending, lookup s.computed i.dst = none

theorem Invariant.initial {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} (wf : p.WellFormed spec) :
    Invariant spec p p.initialState where
  sound := fun _ _ found => Denotes.input found
  pendingSublist := List.Sublist.refl _
  firedComputed := fun _ member notPending => absurd member notPending
  inputsPresent := fun _ _ isInput => isInput
  pendingNotComputed := fun i member => wf.inputsNotWritten i member

/-- Instructions are distinct, since their destinations are. -/
theorem instructions_nodup {p : Program Op Value}
    (unique : (p.instructions.map Instruction.dst).Nodup) :
    p.instructions.Nodup :=
  List.Nodup.of_map _ unique

theorem Invariant.step {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} (wf : p.WellFormed spec) {s s' : State Op Value}
    (invariant : Invariant spec p s) (step : Step spec s s') :
    Invariant spec p s' := by
  cases step with
  | @fire computed pre post i v ready =>
      have memberPending : i ∈ p.instructions :=
        invariant.pendingSublist.mem (List.mem_append_right _
          (List.mem_cons_self ..))
      have restSublist : (pre ++ post).Sublist p.instructions :=
        List.Sublist.trans
          (List.Sublist.append (List.Sublist.refl pre)
            ((List.Sublist.refl post).cons i))
          invariant.pendingSublist
      have pendingNodup : (pre ++ i :: post).Nodup :=
        invariant.pendingSublist.nodup (instructions_nodup wf.writersUnique)
      have distinctDst : ∀ j ∈ pre ++ post, i.dst ≠ j.dst := by
        intro j memberJ
        have jInstr : j ∈ p.instructions :=
          restSublist.mem memberJ
        have notMember : i ∉ pre ++ post :=
          (List.nodup_cons.mp (List.nodup_middle.mp pendingNodup)).1
        have jNe : j ≠ i := fun same => notMember (same ▸ memberJ)
        intro dstSame
        have := List.inj_on_of_nodup_map wf.writersUnique memberPending
          jInstr dstSame
        exact jNe this.symm
      refine ⟨?_, restSublist, ?_, ?_, ?_⟩
      · intro c w found
        by_cases same : i.dst = c
        · subst same
          rw [lookup_cons_self] at found
          have valueEq : v = w := by simpa using found
          subst valueEq
          exact readyValue_denotes wf invariant.sound memberPending ready
        · rw [lookup_cons_of_ne same] at found
          exact invariant.sound c w found
      · intro j memberJ notPending
        by_cases dstSame : i.dst = j.dst
        · rw [dstSame, lookup_cons_self]; simp
        · rw [lookup_cons_of_ne dstSame]
          refine invariant.firedComputed j memberJ ?_
          intro memberBefore
          rcases List.mem_append.mp memberBefore with inPre | inTail
          · exact notPending (List.mem_append_left _ inPre)
          · rcases List.mem_cons.mp inTail with rfl | inPost
            · exact dstSame rfl
            · exact notPending (List.mem_append_right _ inPost)
      · intro c w isInput
        have notDst : i.dst ≠ c := by
          intro same
          have := wf.inputsNotWritten i memberPending
          rw [same, isInput] at this
          cases this
        rw [lookup_cons_of_ne notDst]
        exact invariant.inputsPresent c w isInput
      · intro j memberJ
        rw [lookup_cons_of_ne (distinctDst j memberJ)]
        exact invariant.pendingNotComputed j
          (List.mem_append.mpr (by
            rcases List.mem_append.mp memberJ with inPre | inPost
            · exact Or.inl inPre
            · exact Or.inr (List.mem_cons_of_mem _ inPost)))

theorem Invariant.steps {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} (wf : p.WellFormed spec) {s s' : State Op Value}
    (invariant : Invariant spec p s) (run : Steps spec s s') :
    Invariant spec p s' := by
  induction run with
  | refl => exact invariant
  | tail _ step inductionHypothesis => exact inductionHypothesis.step wf step

/-! ## Progress: a well-formed program never deadlocks -/

/-- Every operand of a denoting vector denotes at the *same* budget. -/
theorem denoteOperands_mem_denoteCell {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} {fuel : Nat} :
    ∀ {cs : List CellId} {vs : List Value},
      denoteOperands spec p fuel cs = some vs → ∀ d ∈ cs,
        ∃ w, denoteCell spec p fuel d = some w := by
  intro cs
  induction cs with
  | nil => intro vs _ d member; cases member
  | cons c cs inductionHypothesis =>
      intro vs evaluated d member
      cases headValue : denoteCell spec p fuel c with
      | none => simp [denoteOperands_cons, headValue] at evaluated
      | some v =>
          cases tailValues : denoteOperands spec p fuel cs with
          | none =>
              simp [denoteOperands_cons, headValue, tailValues] at evaluated
          | some tail =>
              rcases List.mem_cons.mp member with rfl | tailMember
              · exact ⟨v, headValue⟩
              · exact inductionHypothesis tailValues d tailMember

/-- A writer found by lookup is an instruction of the program writing that
very cell. -/
theorem writerOf_mem {p : Program Op Value} {c : CellId}
    {i : Instruction Op Value} (writer : p.writerOf? c = some i) :
    i ∈ p.instructions ∧ i.dst = c :=
  ⟨List.mem_of_find?_eq_some writer, by simpa using List.find?_some writer⟩

/-- A denoting cell is supplied either as an input or by an instruction. -/
theorem Denotes.has_source {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} {c : CellId} {v : Value}
    (denotes : Denotes spec p c v) :
    (p.inputValue? c).isSome ∨ (p.writerOf? c).isSome := by
  obtain ⟨fuel, evaluated⟩ := denotes
  cases fuel with
  | zero => rw [denoteCell_zero] at evaluated; exact Or.inl (by simp [evaluated])
  | succ fuel =>
      cases isInput : p.inputValue? c with
      | some inputValue => exact Or.inl (by simp)
      | none =>
          cases writer : p.writerOf? c with
          | none =>
              rw [denoteCell_succ, isInput, writer] at evaluated
              cases evaluated
          | some i => exact Or.inr (by simp)

/-- **No deadlock.**  In a well-formed program, any reachable state with
pending work has a ready instruction, so execution can always continue. -/
theorem progress {spec : PureOperatorSpec Op Value} {p : Program Op Value}
    (wf : p.WellFormed spec) {s : State Op Value}
    (invariant : Invariant spec p s) (nonempty : s.pending ≠ []) :
    ∃ s', Step spec s s' := by
  -- a ready pending instruction can always be found by descending the
  -- denotation of any pending destination
  have findReady : ∀ (fuel : Nat) (c : CellId) (v : Value),
      denoteCell spec p fuel c = some v → lookup s.computed c = none →
      ∃ j ∈ s.pending, (readyValue spec s.computed j).isSome := by
    intro fuel
    induction fuel with
    | zero =>
        intro c v evaluated notComputed
        rw [denoteCell_zero] at evaluated
        rw [invariant.inputsPresent c v evaluated] at notComputed
        cases notComputed
    | succ fuel inductionHypothesis =>
        intro c v evaluated notComputed
        cases isInput : p.inputValue? c with
        | some inputValue =>
            rw [invariant.inputsPresent c inputValue isInput] at notComputed
            cases notComputed
        | none =>
            cases writer : p.writerOf? c with
            | none =>
                rw [denoteCell_succ, isInput, writer] at evaluated
                cases evaluated
            | some j =>
                obtain ⟨memberJ, dstJ⟩ := writerOf_mem writer
                have pendingJ : j ∈ s.pending := by
                  by_contra notPending
                  have := invariant.firedComputed j memberJ notPending
                  rw [dstJ, notComputed] at this
                  exact absurd this (by simp)
                cases j with
                | const d constValue =>
                    exact ⟨.const d constValue, pendingJ, by simp⟩
                | apply d op operands =>
                    have arity : operands.length = spec.arity op := by
                      have := wf.aritiesOk _ memberJ
                      simpa [Instruction.arityOk] using this
                    cases operandValues :
                        evalOperands s.computed operands with
                    | some values =>
                        refine ⟨.apply d op operands, pendingJ, ?_⟩
                        simp [readyValue, arity, operandValues]
                    | none =>
                        obtain ⟨e, memberE, missing⟩ :=
                          exists_unavailable_of_evalOperands_none
                            operandValues
                        rw [denoteCell_succ, isInput, writer] at evaluated
                        simp only [if_pos arity] at evaluated
                        cases childValues :
                            denoteOperands spec p fuel operands with
                        | none => rw [childValues] at evaluated; cases evaluated
                        | some childList =>
                            obtain ⟨w, childEvaluated⟩ :=
                              denoteOperands_mem_denoteCell childValues e
                                memberE
                            exact inductionHypothesis e w childEvaluated missing
  obtain ⟨i, pendingI, restList, pendingEq⟩ :
      ∃ i pre post, s.pending = pre ++ i :: post := by
    cases pendingShape : s.pending with
    | nil => exact absurd pendingShape nonempty
    | cons head tail => exact ⟨head, [], tail, by simp⟩
  have memberI : i ∈ p.instructions :=
    invariant.pendingSublist.mem (by rw [pendingEq]; simp)
  have notComputed : lookup s.computed i.dst = none :=
    invariant.pendingNotComputed i (by rw [pendingEq]; simp)
  obtain ⟨v, denotes⟩ := wf.destinationsDenote i memberI
  obtain ⟨fuel, evaluated⟩ := denotes
  obtain ⟨j, pendingJ, ready⟩ := findReady fuel i.dst v evaluated notComputed
  obtain ⟨w, readyValue⟩ := Option.isSome_iff_exists.mp ready
  obtain ⟨pre, post, split⟩ := List.append_of_mem pendingJ
  refine ⟨⟨(j.dst, w) :: s.computed, pre ++ post⟩, ?_⟩
  have stateEq : s = ⟨s.computed, pre ++ j :: post⟩ := by
    cases s; simp_all
  rw [stateEq]
  exact Step.fire readyValue

/-- A state with no available step has nothing pending: the only way to stop
is to finish. -/
theorem terminal_of_no_step {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} (wf : p.WellFormed spec) {s : State Op Value}
    (invariant : Invariant spec p s) (stuck : ¬ ∃ s', Step spec s s') :
    s.pending = [] := by
  by_contra nonempty
  exact stuck (progress wf invariant nonempty)

/-- **Termination.**  Execution of a well-formed program always reaches a
state with nothing pending. -/
theorem exists_terminal_run {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} (wf : p.WellFormed spec) :
    ∃ s, Steps spec p.initialState s ∧ s.pending = [] := by
  suffices reach : ∀ (bound : Nat) (s : State Op Value),
      Invariant spec p s → s.pending.length ≤ bound →
      ∃ t, Steps spec s t ∧ t.pending = [] by
    obtain ⟨t, run, terminal⟩ := reach p.initialState.pending.length
      p.initialState (Invariant.initial wf) (Nat.le_refl _)
    exact ⟨t, run, terminal⟩
  intro bound
  induction bound with
  | zero =>
      intro s invariant lengthLe
      exact ⟨s, Relation.ReflTransGen.refl,
        List.eq_nil_of_length_eq_zero (Nat.le_zero.mp lengthLe)⟩
  | succ bound inductionHypothesis =>
      intro s invariant lengthLe
      by_cases empty : s.pending = []
      · exact ⟨s, Relation.ReflTransGen.refl, empty⟩
      · obtain ⟨s', step⟩ := progress wf invariant empty
        have shorter : s'.pending.length ≤ bound := by
          have := step.pending_length_lt
          omega
        obtain ⟨t, run, terminal⟩ :=
          inductionHypothesis s' (invariant.step wf step) shorter
        exact ⟨t, Relation.ReflTransGen.head step run, terminal⟩

/-! ## Adequacy: every terminal state carries the denotation -/

/-- **The crown.**  Under every schedule, a terminated run of a well-formed
program assigns the returned cell exactly its denotation. -/
theorem terminal_result_eq_denote {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} (wf : p.WellFormed spec) {s : State Op Value}
    (run : Steps spec p.initialState s) (terminal : s.pending = []) :
    ∃ v, Denotes spec p p.result v ∧ lookup s.computed p.result = some v := by
  have invariant := (Invariant.initial wf).steps wf run
  obtain ⟨v, denotes⟩ := wf.resultDenotes
  refine ⟨v, denotes, ?_⟩
  have computedSome : (lookup s.computed p.result).isSome := by
    rcases denotes.has_source with isInput | hasWriter
    · obtain ⟨inputValue, found⟩ := Option.isSome_iff_exists.mp isInput
      rw [invariant.inputsPresent p.result inputValue found]
      simp
    · obtain ⟨j, writer⟩ := Option.isSome_iff_exists.mp hasWriter
      obtain ⟨memberJ, dstJ⟩ := writerOf_mem writer
      have notPending : j ∉ s.pending := by rw [terminal]; simp
      have := invariant.firedComputed j memberJ notPending
      rwa [dstJ] at this
  obtain ⟨w, found⟩ := Option.isSome_iff_exists.mp computedSome
  rw [found, Denotes.functional (invariant.sound p.result w found) denotes]

/-- Schedule independence of the answer: any two terminated runs agree on
the returned cell.  This needs no confluence argument — the denotation is a
function, and both runs compute it. -/
theorem terminal_result_unique {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} (wf : p.WellFormed spec) {s t : State Op Value}
    (runLeft : Steps spec p.initialState s) (terminalLeft : s.pending = [])
    (runRight : Steps spec p.initialState t) (terminalRight : t.pending = []) :
    lookup s.computed p.result = lookup t.computed p.result := by
  obtain ⟨v, denotesLeft, foundLeft⟩ :=
    terminal_result_eq_denote wf runLeft terminalLeft
  obtain ⟨w, denotesRight, foundRight⟩ :=
    terminal_result_eq_denote wf runRight terminalRight
  rw [foundLeft, foundRight, Denotes.functional denotesLeft denotesRight]

/-! ## Independent ready firings

Readiness supplies the read dependency: a ready instruction cannot read a
cell that is still absent. Inserting such a fresh cell therefore preserves
its already computed operands. Distinct destinations supply the write
dependency. These facts give a concrete square of operational firings,
with the same pending instructions and the same value at every cell.
-/

/-- Adding a previously absent cell cannot change an available operand
vector. This uses the actual lookup results, not an asserted footprint. -/
theorem evalOperands_cons_of_none {env : List (CellId × Value)}
    {cell : CellId} (fresh : lookup env cell = none) (value : Value) :
    ∀ {operands : List CellId} {values : List Value},
      evalOperands env operands = some values →
      evalOperands ((cell, value) :: env) operands = some values := by
  intro operands
  induction operands with
  | nil => intro values ready; exact ready
  | cons operand rest ih =>
      intro values ready
      cases head : lookup env operand with
      | none => simp [evalOperands, head] at ready
      | some first =>
          have different : cell ≠ operand := by
            intro same
            subst operand
            rw [fresh] at head
            cases head
          cases tail : evalOperands env rest with
          | none => simp [evalOperands, head, tail] at ready
          | some remaining =>
              simpa only [evalOperands, lookup_cons_of_ne different,
                head, tail, ih tail] using ready

/-- A ready instruction keeps its value when another instruction fills a
previously absent cell. -/
theorem readyValue_cons_of_none {spec : PureOperatorSpec Op Value}
    {env : List (CellId × Value)} {cell : CellId}
    (fresh : lookup env cell = none) (value : Value)
    {instruction : Instruction Op Value} {result : Value}
    (ready : readyValue spec env instruction = some result) :
    readyValue spec ((cell, value) :: env) instruction = some result := by
  cases instruction with
  | const destination constant => exact ready
  | apply destination operator operands =>
      by_cases arity : operands.length = spec.arity operator
      · cases values : evalOperands env operands with
        | none => simp [readyValue, arity, values] at ready
        | some arguments =>
            simpa only [readyValue, if_pos arity,
              values, evalOperands_cons_of_none fresh value values] using ready
      · simp [readyValue, arity] at ready

/-- Two independently ready instructions can fire in either order. The
intermediate and final pending lists are explicit: neither firing discards
or reorders the remaining program. Computed association lists may differ
in insertion order, but all cell observations agree. -/
theorem ready_pair_diamond (spec : PureOperatorSpec Op Value)
    (env : List (CellId × Value))
    (pre middle post : List (Instruction Op Value))
    (left right : Instruction Op Value) (leftValue rightValue : Value)
    (distinct : left.dst ≠ right.dst)
    (leftFresh : lookup env left.dst = none)
    (rightFresh : lookup env right.dst = none)
    (leftReady : readyValue spec env left = some leftValue)
    (rightReady : readyValue spec env right = some rightValue) :
    Step spec ⟨env, pre ++ left :: (middle ++ right :: post)⟩
      ⟨(left.dst, leftValue) :: env, pre ++ middle ++ right :: post⟩ ∧
    Step spec ⟨env, pre ++ left :: (middle ++ right :: post)⟩
      ⟨(right.dst, rightValue) :: env, pre ++ left :: (middle ++ post)⟩ ∧
    Step spec ⟨(left.dst, leftValue) :: env, pre ++ middle ++ right :: post⟩
      ⟨(right.dst, rightValue) :: (left.dst, leftValue) :: env,
        pre ++ middle ++ post⟩ ∧
    Step spec ⟨(right.dst, rightValue) :: env, pre ++ left :: (middle ++ post)⟩
      ⟨(left.dst, leftValue) :: (right.dst, rightValue) :: env,
        pre ++ middle ++ post⟩ ∧
    ∀ cell, lookup ((right.dst, rightValue) :: (left.dst, leftValue) :: env) cell =
      lookup ((left.dst, leftValue) :: (right.dst, rightValue) :: env) cell := by
  have rightAfter := readyValue_cons_of_none leftFresh leftValue rightReady
  have leftAfter := readyValue_cons_of_none rightFresh rightValue leftReady
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.append_assoc] using
      (Step.fire (pre := pre) (post := middle ++ right :: post) leftReady)
  · simpa only [List.append_assoc, List.cons_append] using
      (Step.fire (pre := pre ++ left :: middle) (post := post) rightReady)
  · exact Step.fire (pre := pre ++ middle) (post := post) rightAfter
  · simpa only [List.append_assoc] using
      (Step.fire (pre := pre) (post := middle ++ post) leftAfter)
  · intro cell
    by_cases atLeft : left.dst = cell
    · subst cell
      rw [lookup_cons_of_ne distinct.symm, lookup_cons_self, lookup_cons_self]
    · by_cases atRight : right.dst = cell
      · subst cell
        rw [lookup_cons_self, lookup_cons_of_ne distinct, lookup_cons_self]
      · rw [lookup_cons_of_ne atRight, lookup_cons_of_ne atLeft,
          lookup_cons_of_ne atLeft, lookup_cons_of_ne atRight]

/-- A ready pure computation remains valid while another pending instruction
fires in an invariant state. Its operands cannot include the still-absent
destination being filled. This preserves the value; it does not authorize a
second firing of an instruction that has already left the pending list. -/
theorem Invariant.ready_preserved_step {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} {before after : State Op Value}
    (invariant : Invariant spec p before) (step : Step spec before after)
    {instruction : Instruction Op Value} {value : Value}
    (ready : readyValue spec before.computed instruction = some value) :
    readyValue spec after.computed instruction = some value := by
  cases step with
  | @fire computed pre post fired result fires =>
      exact readyValue_cons_of_none
        (invariant.pendingNotComputed fired
          (List.mem_append_right pre (List.mem_cons_self ..))) result ready

/-- An arbitrary scheduling delay preserves an already-ready computation in
the single-assignment language. The intermediate states use the existing
reachability invariant, so no fresh noninterference premise is needed for
each delayed step. -/
theorem Invariant.ready_preserved_steps {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} (wf : p.WellFormed spec)
    {before after : State Op Value} (invariant : Invariant spec p before)
    (run : Steps spec before after)
    {instruction : Instruction Op Value} {value : Value}
    (ready : readyValue spec before.computed instruction = some value) :
    readyValue spec after.computed instruction = some value := by
  induction run with
  | refl => exact ready
  | tail priorRun step ih =>
      exact (invariant.steps wf priorRun).ready_preserved_step step ih

/-! ## Executable scheduling through the common resumable machine

The first-ready scheduler skips unavailable instructions and retains them in
their original order. Its step function implements the existing firing
relation. Other admitted schedules still use that relation and its independent
firing laws; this executable policy does not redefine concurrency.
-/

/-- Select the first available instruction, retaining every unselected one. -/
def fireReady (spec : PureOperatorSpec Op Value) (env : List (CellId × Value)) :
    List (Instruction Op Value) → Option (State Op Value)
  | [] => none
  | instruction :: rest =>
      match readyValue spec env instruction with
      | some value => some ⟨(instruction.dst, value) :: env, rest⟩
      | none => (fireReady spec env rest).map fun next =>
          { next with pending := instruction :: next.pending }

/-- Unselected pending instructions can be retained before a firing. -/
theorem Step.prepend_pending {spec : PureOperatorSpec Op Value}
    {before after : State Op Value} (step : Step spec before after)
    (earlier : List (Instruction Op Value)) :
    Step spec { before with pending := earlier ++ before.pending }
      { after with pending := earlier ++ after.pending } := by
  cases step with
  | @fire computed pre post instruction value ready =>
      simpa only [List.append_assoc] using
        (Step.fire (pre := earlier ++ pre) (post := post) ready)

/-- Every successful scheduler transition is an actual source firing. -/
theorem fireReady_sound (spec : PureOperatorSpec Op Value)
    (env : List (CellId × Value)) :
    ∀ (pending : List (Instruction Op Value)) (next : State Op Value),
      fireReady spec env pending = some next → Step spec ⟨env, pending⟩ next := by
  intro pending
  induction pending with
  | nil => intro next found; simp [fireReady] at found
  | cons instruction rest ih =>
      intro next found
      cases ready : readyValue spec env instruction with
      | some value =>
          have same : next = ⟨(instruction.dst, value) :: env, rest⟩ := by
            simpa [fireReady, ready] using found.symm
          subst next
          exact Step.fire (pre := []) ready
      | none =>
          cases tail : fireReady spec env rest with
          | none => simp [fireReady, ready, tail] at found
          | some nextTail =>
              have same : next = { nextTail with pending := instruction :: nextTail.pending } := by
                simpa [fireReady, ready, tail] using found.symm
              subst next
              simpa using (ih nextTail tail).prepend_pending [instruction]

/-- Failure to schedule means that every pending instruction is unavailable. -/
theorem fireReady_none_iff (spec : PureOperatorSpec Op Value)
    (env : List (CellId × Value)) (pending : List (Instruction Op Value)) :
    fireReady spec env pending = none ↔
      ∀ instruction ∈ pending, readyValue spec env instruction = none := by
  induction pending with
  | nil => simp [fireReady]
  | cons instruction rest ih =>
      cases ready : readyValue spec env instruction <;> simp [fireReady, ready, ih]

/-- A concrete dataflow inhabitant of the shared bounded-resumption interface.
One transition fires one instruction; this count does not price lookup or the
operator implementation. A state with no step can still be malformed/stuck. -/
def readyMachine (spec : PureOperatorSpec Op Value) :
    Mettapedia.Machines.MachineCore (Program Op Value) where
  State := State Op Value
  load := Program.initialState
  step := fun state => fireReady spec state.computed state.pending

/-- The executable scheduler stops exactly when the source has no firing. -/
theorem readyMachine_final_iff (spec : PureOperatorSpec Op Value) (state : State Op Value) :
    (readyMachine spec).step state = none ↔ ¬ ∃ next, Step spec state next := by
  constructor
  · intro final ⟨next, step⟩
    have unavailable := (fireReady_none_iff spec state.computed state.pending).mp final
    cases step with
    | @fire computed pre post instruction value ready =>
        have missing := unavailable instruction
          (List.mem_append_right pre (List.mem_cons_self ..))
        rw [ready] at missing
        cases missing
  · intro stopped
    cases result : (readyMachine spec).step state with
    | none => rfl
    | some next =>
        exact False.elim (stopped ⟨next, fireReady_sound spec _ _ next result⟩)

/-- Whole bounded machine executions refine source runs, including their
complete computed environment and still-pending instructions. -/
theorem readyMachine_slice_steps (spec : PureOperatorSpec Op Value) (fuel : Nat)
    (state : State Op Value) :
    Steps spec state ((readyMachine spec).runSlice fuel state).1 := by
  suffices lift : ∀ {before after : State Op Value},
      (readyMachine spec).Steps before after → Steps spec before after from
    lift ((readyMachine spec).runSlice_steps fuel state)
  intro before after run
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact ih.tail (fireReady_sound spec _ _ _ step)

/-- Every firing removes precisely one pending instruction. -/
theorem Step.pending_length_add_one {spec : PureOperatorSpec Op Value}
    {before after : State Op Value} (step : Step spec before after) :
    after.pending.length + 1 = before.pending.length := by
  cases step with
  | fire ready => simp [Nat.add_assoc]

/-- The common slice's paid transitions account for exactly the instructions
removed from the complete residual. Unavailable scans do not count as firings. -/
theorem readyMachine_slice_pending (spec : PureOperatorSpec Op Value) (fuel : Nat)
    (state : State Op Value) :
    ((readyMachine spec).runSlice fuel state).1.pending.length +
      ((readyMachine spec).runSlice fuel state).2 = state.pending.length := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases advanced : (readyMachine spec).step state with
      | none => simp [Mettapedia.Machines.MachineCore.runSlice, advanced]
      | some next =>
          have removed := (fireReady_sound spec _ _ _ advanced).pending_length_add_one
          change next.pending.length + 1 = state.pending.length at removed
          have remaining := ih next
          simp only [Mettapedia.Machines.MachineCore.runSlice, advanced]
          omega

/-- Enough firing allowance completes every invariant state of a well-formed
program. The general final-state interface alone does not imply completion. -/
theorem readyMachine_slice_terminal {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} (wf : p.WellFormed spec) {state : State Op Value}
    (invariant : Invariant spec p state) (fuel : Nat)
    (enough : state.pending.length ≤ fuel) :
    ((readyMachine spec).runSlice fuel state).1.pending = [] := by
  have reachable := readyMachine_slice_steps spec fuel state
  by_cases early : ((readyMachine spec).runSlice fuel state).2 < fuel
  · exact terminal_of_no_step wf (invariant.steps wf reachable)
      ((readyMachine_final_iff spec _).mp
        ((readyMachine spec).runSlice_under_budget_final fuel state early))
  · have used := (readyMachine spec).runSlice_used_le fuel state
    have accounted := readyMachine_slice_pending spec fuel state
    have empty : ((readyMachine spec).runSlice fuel state).1.pending.length = 0 := by omega
    exact List.eq_nil_of_length_eq_zero empty

/-- The actual executable policy returns the source denotation within the
instruction-count allowance, using the existing schedule adequacy theorem. -/
theorem readyMachine_slice_denotes {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} (wf : p.WellFormed spec) (fuel : Nat)
    (enough : p.instructions.length ≤ fuel) :
    ∃ value, Denotes spec p p.result value ∧
      lookup ((readyMachine spec).runSlice fuel p.initialState).1.computed p.result = some value :=
  terminal_result_eq_denote wf (readyMachine_slice_steps spec fuel p.initialState)
    (readyMachine_slice_terminal wf (Invariant.initial wf) fuel enough)

/-! ## Retained child computations behind ready firings

An admitted pure instruction may be implemented by a child program that takes
many transitions. The child owns its work and caller frames. The parent still
observes operands in its declared order, regardless of worker completion order.
This connects the existing owned driver and snapshot kernel to the readiness
diamond; it does not apply the finite instruction bound to child execution.
-/

namespace RetainedChildren

open Mettapedia.Machines

/-- Read only completed invocation roots into a cell environment. Unfinished
children remain in the pool and cannot supply a provisional internal value. -/
def completedCells {Event : Type} (slots : List CellId)
    (pool : CellId → Nat × OwnedPullDriver.State Value Event) : List (CellId × Value) :=
  slots.filterMap fun cell => (OwnedPullDriver.completedValue (pool cell).2).map
    (fun value => (cell, value))

/-- Interleaving independent child quanta preserves the whole paid pool and
the parent's ordered operand readout, including missing or repeated operands. -/
theorem ordered_join_interleaving {Event : Type}
    (pool : CellId → Nat × OwnedPullDriver.State Value Event)
    (first second : List (CellId × Nat)) (slots operands : List CellId)
    (env : List (CellId × Value))
    (same : ∀ owner, first.filter (fun item => decide (item.1 = owner)) =
      second.filter (fun item => decide (item.1 = owner))) :
    let kernel := OwnedPullDriver.paidKernel CellId Value Event
    let left := kernel.run () (fun _ => ()) pool first
    let right := kernel.run () (fun _ => ()) pool second
    left = right ∧
      evalOperands (completedCells slots left ++ env) operands =
        evalOperands (completedCells slots right ++ env) operands := by
  have equal := OwnedPullDriver.paidKernel_interleaving pool first second same
  exact ⟨equal, congrArg (fun state =>
    evalOperands (completedCells slots state ++ env) operands) equal⟩

/-- A finite semantic derivation for each child, combined with independent
ready destinations, realizes the existing two-firing square. Private worker
partitioning preserves both paid states; publication performs no child work.

The two readiness premises are the local implementation obligations: the
child's actual result must implement its parent's instruction. They do not
assert the scheduling or publication conclusions being proved here. -/
theorem completed_pair_fires {Event : Type}
    (spec : PureOperatorSpec Op Value) (env : List (CellId × Value))
    (pre middle post : List (Instruction Op Value))
    (left right : Instruction Op Value) (leftValue rightValue : Value)
    (leftWork rightWork : OwnedPullDriver.Program Value Event)
    (leftEvents rightEvents : List Event)
    (leftCalls leftDepth rightCalls rightDepth leftPaid rightPaid leftExtra rightExtra : Nat)
    (leftRun : OwnedPullDriver.CostedRuns leftWork leftEvents leftValue leftCalls leftDepth)
    (rightRun : OwnedPullDriver.CostedRuns rightWork rightEvents rightValue rightCalls rightDepth)
    (distinct : left.dst ≠ right.dst)
    (leftFresh : lookup env left.dst = none)
    (rightFresh : lookup env right.dst = none)
    (leftReady : readyValue spec env left = some leftValue)
    (rightReady : readyValue spec env right = some rightValue)
    (pool : CellId → Nat × OwnedPullDriver.State Value Event)
    (leftInitial : pool left.dst = (leftPaid, ⟨leftWork, []⟩))
    (rightInitial : pool right.dst = (rightPaid, ⟨rightWork, []⟩))
    (parts : List (List (CellId × Nat)))
    (coverage : parts.flatten.Perm
      [(left.dst, leftEvents.length + 2 * leftCalls + leftExtra),
       (right.dst, rightEvents.length + 2 * rightCalls + rightExtra)]) :
    let result := (OwnedPullDriver.paidKernel CellId Value Event).partitioned
      () (fun _ => ()) pool parts
    result left.dst =
      (leftPaid + leftEvents.length + 2 * leftCalls, ⟨.done leftValue, []⟩) ∧
    result right.dst =
      (rightPaid + rightEvents.length + 2 * rightCalls, ⟨.done rightValue, []⟩) ∧
    Steps spec ⟨env, pre ++ left :: (middle ++ right :: post)⟩
      ⟨completedCells [left.dst, right.dst] result ++ env, pre ++ middle ++ post⟩ ∧
    ∀ observer, readyValue spec
        (completedCells [left.dst, right.dst] result ++ env) observer =
      readyValue spec
        (completedCells [right.dst, left.dst] result ++ env) observer := by
  let kernel := OwnedPullDriver.paidKernel CellId Value Event
  let schedule := [(left.dst, leftEvents.length + 2 * leftCalls + leftExtra),
    (right.dst, rightEvents.length + 2 * rightCalls + rightExtra)]
  have unique : kernel.Disjoint schedule := by
    simp [SnapshotBatch.Kernel.Disjoint, kernel, schedule, OwnedPullDriver.paidKernel, distinct]
  have whole := kernel.partitioned_eq_run () (fun _ => ()) pool parts schedule coverage unique
  let result := kernel.partitioned () (fun _ => ()) pool parts
  have leftResult : result left.dst =
      (leftPaid + leftEvents.length + 2 * leftCalls, ⟨.done leftValue, []⟩) := by
    change kernel.partitioned () (fun _ => ()) pool parts left.dst = _
    rw [whole]
    have owned := kernel.run_at_owned () (fun _ => ()) pool schedule unique
      (left.dst, leftEvents.length + 2 * leftCalls + leftExtra) (by simp [schedule])
    simpa only [kernel, OwnedPullDriver.paidKernel, leftInitial,
      leftRun.paidSlice leftPaid leftExtra] using owned
  have rightResult : result right.dst =
      (rightPaid + rightEvents.length + 2 * rightCalls, ⟨.done rightValue, []⟩) := by
    change kernel.partitioned () (fun _ => ()) pool parts right.dst = _
    rw [whole]
    have owned := kernel.run_at_owned () (fun _ => ()) pool schedule unique
      (right.dst, rightEvents.length + 2 * rightCalls + rightExtra) (by simp [schedule])
    simpa only [kernel, OwnedPullDriver.paidKernel, rightInitial,
      rightRun.paidSlice rightPaid rightExtra] using owned
  have square := ready_pair_diamond spec env pre middle post left right
    leftValue rightValue distinct leftFresh rightFresh leftReady rightReady
  have cells : completedCells [left.dst, right.dst] result =
      [(left.dst, leftValue), (right.dst, rightValue)] := by
    simp [completedCells, leftResult, rightResult, OwnedPullDriver.completedValue]
  have reverseCells : completedCells [right.dst, left.dst] result =
      [(right.dst, rightValue), (left.dst, leftValue)] := by
    simp [completedCells, leftResult, rightResult, OwnedPullDriver.completedValue]
  refine ⟨leftResult, rightResult, ?_, ?_⟩
  · change Steps spec _ ⟨completedCells [left.dst, right.dst] result ++ env, _⟩
    rw [cells]
    exact Relation.ReflTransGen.head square.2.1
      (Relation.ReflTransGen.single square.2.2.2.1)
  · intro observer
    change readyValue spec (completedCells [left.dst, right.dst] result ++ env) observer =
      readyValue spec (completedCells [right.dst, left.dst] result ++ env) observer
    rw [cells, reverseCells]
    exact readyValue_eq_of_agreement spec _ _ observer
      (fun cell _ => (square.2.2.2.2 cell).symm)

end RetainedChildren

end Mettapedia.Languages.Dataflow
