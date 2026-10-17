import Mettapedia.GSLT.LanguageDef.ProofSystems
import Mettapedia.Computability.StackMachineComposition
import Mathlib.Computability.TuringMachine.Computable

/-!
# Operational realizations of proof-certificate translations

`ProofSystems.PSimulation` records a polynomial declared cost account.
`OperationalPSimulation` additionally requires a finite-stack machine that computes
its actual translation on encoded inputs, with a polynomial execution bound in
Mathlib's `TM2OutputsInTime` semantics. The encoding length is polynomially bounded
by the source checker's declared input size. Forgetting the realization recovers
the existing interface, with a clock derived from the proved machine execution.

`SymbolMapMachine` is a concrete two-stack realization of finite alphabet symbol
relocation. It takes at most `2 * input.length + 2` machine steps and retains input
order. `CertificateRelocation` uses it to change a chronological certificate's
finite rule tags, carrying its claim and preserving every reference payload and
physical occurrence. This is a representation transport, not an implementation
of a different logical kernel. `BinaryReferenceMachine` realizes comparison of
complete binary reference fields, with positive, unequal-address and malformed
field controls. The complete HOL graph translation still requires an operational
realization of its term operations and graph traversal.

The cost unit is Mathlib's TM2 statement execution. Each fixed machine has finite
state and alphabet tables, and each statement contains finitely many stack
operations. This is an operational complexity result, not a native runtime or
wall-clock performance assertion. `ExecutedDispatch` realizes optional operations
through a consumed finite status cell; refused inputs never enter the inner
program, and successful input bodies are handed over without re-encoding.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ProofSystems
open Turing StateTransition Polynomial

namespace ExecutedComposition

/-- Two concrete polynomial-time realizations compose by executing both programs
and transferring their intermediate word. The intermediate encoding must have
its own proved polynomial length bound. -/
noncomputable def realization {Source Middle Target InputAlphabet MiddleAlphabet OutputAlphabet : Type}
    [Fintype MiddleAlphabet] [Inhabited MiddleAlphabet]
    {sourceEncoding : Source → List InputAlphabet}
    {middleEncoding : Middle → List MiddleAlphabet}
    {targetEncoding : Target → List OutputAlphabet}
    {firstFunction : Source → Middle} {secondFunction : Middle → Target}
    (first : TM2ComputableInPolyTime sourceEncoding middleEncoding firstFunction)
    (second : TM2ComputableInPolyTime middleEncoding targetEncoding secondFunction)
    (middleSize : ℕ[X])
    (middleBound : ∀ input, (middleEncoding (firstFunction input)).length ≤
      middleSize.eval (sourceEncoding input).length) :
    TM2ComputableInPolyTime sourceEncoding targetEncoding (secondFunction ∘ firstFunction) := by
  letI : Fintype (first.tm.Γ first.tm.k₁) :=
    Fintype.ofEquiv MiddleAlphabet first.outputAlphabet.symm
  letI : Inhabited (first.tm.Γ first.tm.k₁) := ⟨first.outputAlphabet.symm default⟩
  let bridge := first.outputAlphabet.trans second.inputAlphabet.symm
  refine
    { tm := Mettapedia.Computability.StackMachineComposition.machine first.tm second.tm bridge
      inputAlphabet := first.inputAlphabet
      outputAlphabet := second.outputAlphabet
      time := first.time + C 2 * middleSize + C 2 + second.time.comp middleSize
      outputsFun := ?_ }
  intro input
  let intermediate := (middleEncoding (firstFunction input)).map first.outputAlphabet.symm
  have transfer_eq : intermediate.map bridge =
      (middleEncoding (firstFunction input)).map second.inputAlphabet.symm := by
    simp [intermediate, bridge, List.map_map, Function.comp_def]
  have secondRun := second.outputsFun (firstFunction input)
  change TM2OutputsInTime second.tm
    ((middleEncoding (firstFunction input)).map second.inputAlphabet.symm)
    (some ((targetEncoding (secondFunction (firstFunction input))).map second.outputAlphabet.symm)) _ at secondRun
  rw [← transfer_eq] at secondRun
  have joined := Mettapedia.Computability.StackMachineComposition.outputs first.tm second.tm
    bridge ((sourceEncoding input).map first.inputAlphabet.symm) intermediate
    ((targetEncoding (secondFunction (firstFunction input))).map second.outputAlphabet.symm)
    (first.time.eval (sourceEncoding input).length)
    (second.time.eval (middleEncoding (firstFunction input)).length)
    (first.outputsFun input) secondRun
  have middleLength : intermediate.length ≤ middleSize.eval (sourceEncoding input).length := by
    simpa only [intermediate, List.length_map] using middleBound input
  have laterTime := eval_mono second.time (middleBound input)
  change EvalsToInTime _ _ _ _
  refine { toEvalsTo := joined.toEvalsTo, steps_le_m := ?_ }
  apply joined.steps_le_m.trans
  simp only [eval_add, eval_mul, eval_C, eval_comp]
  omega

/-- Successful composition exposes the original two output functions, without
forgetting word positions or duplicate symbols at the handoff. -/
noncomputable def outputs {Source Middle Target InputAlphabet MiddleAlphabet OutputAlphabet : Type}
    [Fintype MiddleAlphabet] [Inhabited MiddleAlphabet]
    {sourceEncoding : Source → List InputAlphabet}
    {middleEncoding : Middle → List MiddleAlphabet}
    {targetEncoding : Target → List OutputAlphabet}
    {firstFunction : Source → Middle} {secondFunction : Middle → Target}
    (first : TM2ComputableInPolyTime sourceEncoding middleEncoding firstFunction)
    (second : TM2ComputableInPolyTime middleEncoding targetEncoding secondFunction)
    (middleSize : ℕ[X])
    (middleBound : ∀ input, (middleEncoding (firstFunction input)).length ≤
      middleSize.eval (sourceEncoding input).length)
    (input : Source) :
    TM2OutputsInTime (realization first second middleSize middleBound).tm
      ((sourceEncoding input).map (realization first second middleSize middleBound).inputAlphabet.symm)
      (some ((targetEncoding (secondFunction (firstFunction input))).map
        (realization first second middleSize middleBound).outputAlphabet.symm))
      ((realization first second middleSize middleBound).time.eval (sourceEncoding input).length) :=
  (realization first second middleSize middleBound).outputsFun input

end ExecutedComposition

/-- A simulation with an actual finite-stack implementation of its certificate
translation. The input encoding is polynomially bounded by the declared source
size; the machine must compute the translation for every input, including refused
certificates. -/
structure OperationalPSimulation {Claim SourceCertificate TargetCertificate InputAlphabet
    OutputAlphabet : Type} [Fintype InputAlphabet] [Fintype OutputAlphabet]
    (target : SizedChecker Claim TargetCertificate) (source : SizedChecker Claim SourceCertificate)
    (inputEncoding : Computability.Encoding (Claim × SourceCertificate) InputAlphabet)
    (outputEncoding : Computability.Encoding TargetCertificate OutputAlphabet)
    extends SizeSimulation target source where
  inputLengthBound : PolyBoundedBy (encodedSize inputEncoding) source.inputSize
  realization : TM2ComputableInPolyTime inputEncoding.encode outputEncoding.encode
    (fun input => translate input.1 input.2)

namespace OperationalPSimulation

def toPSimulation {Claim SourceCertificate TargetCertificate InputAlphabet OutputAlphabet : Type}
    [Fintype InputAlphabet] [Fintype OutputAlphabet]
    {target : SizedChecker Claim TargetCertificate} {source : SizedChecker Claim SourceCertificate}
    {inputEncoding : Computability.Encoding (Claim × SourceCertificate) InputAlphabet}
    {outputEncoding : Computability.Encoding TargetCertificate OutputAlphabet}
    (simulation : OperationalPSimulation target source inputEncoding outputEncoding) :
    PSimulation target source where
  toSizeSimulation := simulation.toSizeSimulation
  translationTime claim certificate := simulation.realization.time.eval
    (encodedSize inputEncoding (claim, certificate))
  timeBound := PolyBoundedBy.trans ⟨simulation.realization.time, fun _ => le_rfl⟩
    simulation.inputLengthBound

/-- The old time account obtained from an operational simulation bounds an actual
run of the supplied machine, rather than an independently selected clock. -/
def execution {Claim SourceCertificate TargetCertificate InputAlphabet OutputAlphabet : Type}
    [Fintype InputAlphabet] [Fintype OutputAlphabet]
    {target : SizedChecker Claim TargetCertificate} {source : SizedChecker Claim SourceCertificate}
    {inputEncoding : Computability.Encoding (Claim × SourceCertificate) InputAlphabet}
    {outputEncoding : Computability.Encoding TargetCertificate OutputAlphabet}
    (simulation : OperationalPSimulation target source inputEncoding outputEncoding)
    (claim : Claim) (certificate : SourceCertificate) :
    TM2OutputsInTime simulation.realization.tm
      ((inputEncoding.encode (claim, certificate)).map simulation.realization.inputAlphabet.invFun)
      (some ((outputEncoding.encode (simulation.translate claim certificate)).map
        simulation.realization.outputAlphabet.invFun))
      (simulation.toPSimulation.translationTime claim certificate) :=
  simulation.realization.outputsFun (claim, certificate)

/-- A successful encoded execution cannot be certified by a zero-step clock:
initial configurations have a current label and final configurations do not. -/
theorem outputs_positive {machine : FinTM2} {input : List (machine.Γ machine.k₀)}
    {output : List (machine.Γ machine.k₁)} {bound : ℕ}
    (execution : TM2OutputsInTime machine input (some output) bound) : 0 < bound := by
  by_contra nonpositive
  have boundZero : bound = 0 := by omega
  have stepsBound := execution.steps_le_m
  have stepsZero : execution.steps = 0 := by omega
  have same := execution.evals_in_steps
  rw [stepsZero] at same
  have configurations : initList machine input = haltList machine output :=
    Option.some.inj same
  have labels := congrArg Turing.TM2.Cfg.l configurations
  simp [initList, haltList] at labels

/-- The realized clock excludes the unattested zero-clock construction. -/
theorem time_positive {Claim SourceCertificate TargetCertificate InputAlphabet OutputAlphabet : Type}
    [Fintype InputAlphabet] [Fintype OutputAlphabet]
    {target : SizedChecker Claim TargetCertificate} {source : SizedChecker Claim SourceCertificate}
    {inputEncoding : Computability.Encoding (Claim × SourceCertificate) InputAlphabet}
    {outputEncoding : Computability.Encoding TargetCertificate OutputAlphabet}
    (simulation : OperationalPSimulation target source inputEncoding outputEncoding)
    (claim : Claim) (certificate : SourceCertificate) :
    0 < simulation.toPSimulation.translationTime claim certificate :=
  outputs_positive (simulation.execution claim certificate)

end OperationalPSimulation

namespace SymbolMapMachine
open Turing.TM2.Stmt

variable {Γ : Type} [Fintype Γ] [Inhabited Γ]

/-- Two passes map a finite alphabet word without reversing its order. The first
pass maps input into a temporary stack; the second restores authored order. -/
def machine (rename : Γ → Γ) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := false
  Γ _ := Γ
  Λ := Bool
  main := false
  σ := Option Γ
  initialState := none
  m phase := if phase then
    pop true (fun _ value => value)
      (branch Option.isSome
        (push false (fun value => value.getD default) (goto fun _ => true))
        (load (fun _ => none) halt))
    else
    pop false (fun _ value => value)
      (branch Option.isSome
        (push true (fun value => rename (value.getD default)) (goto fun _ => false))
        (load (fun _ => none) (goto fun _ => true)))

/-- A machine state with named input and temporary stacks. -/
def config (rename : Γ → Γ) (phase : Option Bool) (state : Option Γ)
    (input temporary : List Γ) : (machine rename).Cfg where
  l := phase
  var := state
  stk index := if (show Bool from index) = true then temporary else input

theorem scan_cons (rename : Γ → Γ) (state : Option Γ) (head : Γ)
    (tail temporary : List Γ) :
    (machine rename).step (config rename (some false) state (head :: tail) temporary) =
      some (config rename (some false) (some head) tail (rename head :: temporary)) := by
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]
  congr 2
  funext index
  cases index <;> simp [Function.update]

theorem scan_nil (rename : Γ → Γ) (state : Option Γ) (temporary : List Γ) :
    (machine rename).step (config rename (some false) state [] temporary) =
      some (config rename (some true) none [] temporary) := by
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]
  congr 2
  funext index
  cases index <;> simp [Function.update]

theorem restore_cons (rename : Γ → Γ) (state : Option Γ) (head : Γ)
    (input tail : List Γ) :
    (machine rename).step (config rename (some true) state input (head :: tail)) =
      some (config rename (some true) (some head) (head :: input) tail) := by
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]
  congr 2
  funext index
  cases index <;> simp [Function.update]

theorem restore_nil (rename : Γ → Γ) (state : Option Γ) (input : List Γ) :
    (machine rename).step (config rename (some true) state input []) =
      some (config rename none none input []) := by
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]
  congr 2
  funext index
  cases index <;> simp [Function.update]

/-- A concrete one-step execution, measured by Mathlib's iteration semantics. -/
def oneStep {σ : Type} {step : σ → Option σ} {before after : σ}
    (executed : step before = some after) : EvalsToInTime step before (some after) 1 where
  steps := 1
  evals_in_steps := by simpa [flip, Option.bind] using executed
  steps_le_m := le_rfl

/-- The scan phase maps each symbol exactly once into the temporary stack. -/
def scan_run (rename : Γ → Γ) (word temporary : List Γ) (state : Option Γ) :
    EvalsToInTime (machine rename).step (config rename (some false) state word temporary)
      (some (config rename (some true) none [] ((word.map rename).reverse ++ temporary)))
      (word.length + 1) := by
  induction word generalizing temporary state with
  | nil => simpa using oneStep (scan_nil rename state temporary)
  | cons head tail ih =>
      have first := oneStep (scan_cons rename state head tail temporary)
      have rest := ih (rename head :: temporary) (some head)
      have joined := EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest
      simpa using joined

/-- The restoring phase reestablishes source order without consulting labels. -/
def restore_run (rename : Γ → Γ) (temporary input : List Γ) (state : Option Γ) :
    EvalsToInTime (machine rename).step (config rename (some true) state input temporary)
      (some (config rename none none (temporary.reverse ++ input) []))
      (temporary.length + 1) := by
  induction temporary generalizing input state with
  | nil => simpa using oneStep (restore_nil rename state input)
  | cons head tail ih =>
      have first := oneStep (restore_cons rename state head input tail)
      have rest := ih (head :: input) (some head)
      have joined := EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest
      simpa using joined

private theorem init_eq (rename : Γ → Γ) (word : List Γ) :
    initList (machine rename) word = config rename (some false) none word [] := by
  simp only [initList, config, machine]
  congr 1
  funext index
  cases index
  · simp
    rfl
  · simp

private theorem halt_eq (rename : Γ → Γ) (word : List Γ) :
    haltList (machine rename) word = config rename none none word [] := by
  simp only [haltList, config, machine]
  congr 1
  funext index
  cases index
  · simp
    rfl
  · simp

set_option backward.isDefEq.respectTransparency false in
/-- The actual machine maps any input word in at most `2 * length + 2` steps. -/
def outputs (rename : Γ → Γ) (word : List Γ) :
    TM2OutputsInTime (machine rename) word (some (word.map rename)) (2 * word.length + 2) := by
  have first := scan_run rename word [] none
  simp only [List.append_nil] at first
  have rest := restore_run rename (word.map rename).reverse [] none
  have joined := EvalsToInTime.trans _ (word.length + 1)
    ((word.map rename).reverse.length + 1) _ _ _ first rest
  change EvalsToInTime _ (initList (machine rename) word)
    (some (haltList (machine rename) (word.map rename))) _
  rw [init_eq rename word, halt_eq rename (word.map rename)]
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

set_option backward.isDefEq.respectTransparency false in
/-- Finite alphabet symbol relocation is genuinely polynomial-time computable. -/
noncomputable def computable (rename : Γ → Γ) : TM2ComputableInPolyTime
    (fun word : List Γ => word) (fun word : List Γ => word) (List.map rename) where
  tm := machine rename
  inputAlphabet := Equiv.refl Γ
  outputAlphabet := Equiv.refl Γ
  time := C 2 * X + C 2
  outputsFun word := by
    change TM2OutputsInTime (machine rename) (word.map id) (some ((word.map rename).map id)) _
    simp only [List.map_id_fun]
    simpa using outputs rename word

/-- Two successive symbol relocations fuse into one actual two-pass machine.
This realizes the composed translation without using an unproved generic
Turing-machine composition theorem. -/
noncomputable def fusedComputable (first second : Γ → Γ) :
    TM2ComputableInPolyTime (fun word : List Γ => word) (fun word : List Γ => word)
      (fun word => (word.map first).map second) := by
  simpa only [List.map_map] using computable (second ∘ first)

omit [Fintype Γ] [Inhabited Γ] in
/-- Fusion retains the complete mapped word, rather than merely its set of symbols. -/
theorem fusion_word (first second : Γ → Γ) (word : List Γ) :
    word.map (second ∘ first) = (word.map first).map second := by
  simp only [List.map_map]

/-- One fused scan-and-restore pass has a smaller statement-step bound than two
separate passes, including empty input. -/
theorem fusion_bound_lt (length : ℕ) :
    2 * length + 2 < (2 * length + 2) + (2 * length + 2) := by omega

set_option backward.isDefEq.respectTransparency false in
/-- Structural compiler encodings that commute with finite symbol relocation
inherit the concrete two-pass realization. The certificate-size bound and logical
preservation come from the supplied size simulation; execution comes from the
machine proved above. -/
noncomputable def simulation {Claim SourceCertificate TargetCertificate : Type}
    {target : SizedChecker Claim TargetCertificate} {source : SizedChecker Claim SourceCertificate}
    (sizeSimulation : SizeSimulation target source)
    (inputEncoding : Computability.Encoding (Claim × SourceCertificate) Γ)
    (outputEncoding : Computability.Encoding TargetCertificate Γ)
    (rename : Γ → Γ)
    (inputLengthBound : PolyBoundedBy (encodedSize inputEncoding) source.inputSize)
    (encodedTranslation : ∀ input, outputEncoding.encode
      (sizeSimulation.translate input.1 input.2) = (inputEncoding.encode input).map rename) :
    OperationalPSimulation target source inputEncoding outputEncoding where
  toSizeSimulation := sizeSimulation
  inputLengthBound := inputLengthBound
  realization :=
    { tm := machine rename
      inputAlphabet := Equiv.refl Γ
      outputAlphabet := Equiv.refl Γ
      time := C 2 * X + C 2
      outputsFun input := by
        change TM2OutputsInTime (machine rename) ((inputEncoding.encode input).map id)
          (some ((outputEncoding.encode (sizeSimulation.translate input.1 input.2)).map id)) _
        simp only [List.map_id_fun, encodedTranslation]
        simpa using outputs rename (inputEncoding.encode input) }

/-- Relocation of row tags retains every row's reference payload in authored
order, including repeated references and repeated rows. -/
theorem map_preserves_payload {Tag Payload : Type} (rename : Tag → Tag)
    (rows : List (Tag × Payload)) :
    (rows.map (fun row => (rename row.1, row.2))).map Prod.snd = rows.map Prod.snd := by
  simp [List.map_map, Function.comp_def]

/-- The relocated list has exactly the original number of physical rows. -/
theorem map_preserves_occurrences {Tag Payload : Type} (rename : Tag → Tag)
    (rows : List (Tag × Payload)) :
    (rows.map (fun row => (rename row.1, row.2))).length = rows.length := by simp

/-- Every physical index retains its own payload; equal-looking rows are not
merged by relocation. -/
theorem map_index {Tag Payload : Type} (rename : Tag → Tag)
    (rows : List (Tag × Payload)) (index : ℕ) :
    (rows.map (fun row => (rename row.1, row.2)))[index]? =
      rows[index]?.map (fun row => (rename row.1, row.2)) := by
  simp

/-- The finite-stack machine realizes structural tag relocation on arbitrary
row sequences in linear time. A reference payload is opaque to the relocation. -/
noncomputable def tagRelocation {Tag Payload : Type} [Fintype Tag] [Fintype Payload]
    [Inhabited Tag] [Inhabited Payload] (rename : Tag → Tag) :
    TM2ComputableInPolyTime (fun rows : List (Tag × Payload) => rows)
      (fun rows : List (Tag × Payload) => rows)
      (List.map (fun row => (rename row.1, row.2))) :=
  computable (fun row => (rename row.1, row.2))

/-- Changing tags really changes the output of this realization; the machine is
not the identity on rows. -/
theorem tagRelocation_changes :
    List.map (fun row : Bool × (Fin 3 × Fin 3) => (!row.1, row.2))
      [(false, (0, 0)), (true, (0, 0)), (true, (1, 1))] =
      [(true, (0, 0)), (false, (0, 0)), (false, (1, 1))] := rfl

/-- A relocation preserves ordered duplicate edges, rather than unfolding their
shared proof or dropping one of its uses. -/
theorem tagRelocation_sharing :
    (List.map (fun row : Bool × (Fin 3 × Fin 3) => (!row.1, row.2))
      [(false, (0, 0)), (true, (0, 0)), (true, (1, 1))]).map Prod.snd =
      [(0, 0), (0, 0), (1, 1)] := rfl

/-- A reversed output fails the declared physical-order observation. -/
theorem tagRelocation_reversed_refused :
    (List.map (fun row : Bool × (Fin 3 × Fin 3) => (!row.1, row.2))
      [(false, (0, 0)), (true, (0, 0)), (true, (1, 1))]).reverse ≠
      [(true, (0, 0)), (false, (0, 0)), (false, (1, 1))] := by decide

end SymbolMapMachine


namespace BinaryReferenceMachine
open Turing.TM2.Stmt

inductive Symbol where
  | bit (value : Bool)
  | delimiter
  deriving DecidableEq, Fintype, Inhabited

set_option backward.isDefEq.respectTransparency false in
inductive Stack where
  | input | temporary | left
  deriving DecidableEq, Fintype

set_option backward.isDefEq.respectTransparency false in
inductive Phase where
  | scan | restore | compare | drain
  deriving DecidableEq, Fintype

/-- Finite control compares two bit words without decoding them to naturals. -/
def bitMatch : Option Symbol → Option Symbol → Bool
  | some (.bit left), some (.bit right) => left == right
  | _, _ => false

/-- The input contains two binary fields separated by one delimiter. -/
def input (left right : List Bool) : List Symbol :=
  left.map Symbol.bit ++ Symbol.delimiter :: right.map Symbol.bit

/-- The three stacks keep input order, with one finite Boolean accumulator. -/
def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .input
  Γ _ := Symbol
  Λ := Phase
  main := .scan
  σ := Option Symbol × Bool
  initialState := (none, true)
  m phase := match phase with
    | .scan => pop .input (fun state value => (value, state.2))
        (branch (fun state => state.1 == some .delimiter)
          (goto fun _ => .restore)
          (branch (fun state => state.1.isSome)
            (push .temporary (fun state => state.1.getD .delimiter) (goto fun _ => .scan))
            (load (fun _ => (none, false)) (goto fun _ => .restore))))
    | .restore => pop .temporary (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome)
          (push .left (fun state => state.1.getD .delimiter) (goto fun _ => .restore))
          (goto fun _ => .compare))
    | .compare => pop .input (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome)
          (pop .left (fun state value => (none, state.2 && bitMatch state.1 value))
            (goto fun _ => .compare))
          (goto fun _ => .drain))
    | .drain => pop .left (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome)
          (load (fun _ => (none, false)) (goto fun _ => .drain))
          (push .input (fun state => .bit state.2) (load (fun _ => (none, true)) halt)))

def config (phase : Option Phase) (state : Option Symbol × Bool)
    (input temporary left : List Symbol) : machine.Cfg where
  l := phase
  var := state
  stk stack := match (show Stack from stack) with
    | .input => input
    | .temporary => temporary
    | .left => left

theorem scan_bit (state : Option Symbol × Bool) (head : Bool)
    (tail temporary left : List Symbol) :
    machine.step (config (some .scan) state (.bit head :: tail) temporary left) =
      some (config (some .scan) (some (.bit head), state.2) tail (.bit head :: temporary) left) := by
  have mismatch : (Symbol.bit head == Symbol.delimiter) = false := rfl
  simp [mismatch, FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]
  congr 2
  funext stack
  cases stack <;> simp [Function.update]

theorem scan_delimiter (state : Option Symbol × Bool) (tail temporary left : List Symbol) :
    machine.step (config (some .scan) state (.delimiter :: tail) temporary left) =
      some (config (some .restore) (some .delimiter, state.2) tail temporary left) := by
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]
  congr 2
  funext stack
  cases stack <;> simp [Function.update]

theorem restore_cons (state : Option Symbol × Bool) (head : Symbol)
    (input tail left : List Symbol) :
    machine.step (config (some .restore) state input (head :: tail) left) =
      some (config (some .restore) (some head, state.2) input tail (head :: left)) := by
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]
  congr 2
  funext stack
  cases stack <;> simp [Function.update]

theorem restore_nil (state : Option Symbol × Bool) (input left : List Symbol) :
    machine.step (config (some .restore) state input [] left) =
      some (config (some .compare) (none, state.2) input [] left) := by
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]
  congr 2
  funext stack
  cases stack <;> simp [Function.update]

theorem compare_cons_cons (state : Option Symbol × Bool) (right left : Bool)
    (rightTail leftTail : List Symbol) :
    machine.step (config (some .compare) state (.bit right :: rightTail) [] (.bit left :: leftTail)) =
      some (config (some .compare) (none, state.2 && (right == left)) rightTail [] leftTail) := by
  simp [FinTM2.step, machine, config, bitMatch, Turing.TM2.step, Turing.TM2.stepAux]
  congr 2
  funext stack
  cases stack <;> simp [Function.update]

theorem compare_cons_nil (state : Option Symbol × Bool) (right : Bool) (rightTail : List Symbol) :
    machine.step (config (some .compare) state (.bit right :: rightTail) [] []) =
      some (config (some .compare) (none, false) rightTail [] []) := by
  simp [FinTM2.step, machine, config, bitMatch, Turing.TM2.step, Turing.TM2.stepAux, Function.update]
  congr 2
  funext stack
  cases stack <;> simp [Function.update]

theorem compare_nil (state : Option Symbol × Bool) (left : List Symbol) :
    machine.step (config (some .compare) state [] [] left) =
      some (config (some .drain) (none, state.2) [] [] left) := by
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]
  congr 2
  funext stack
  cases stack <;> simp [Function.update]

theorem drain_cons (state : Option Symbol × Bool) (head : Symbol) (tail : List Symbol) :
    machine.step (config (some .drain) state [] [] (head :: tail)) =
      some (config (some .drain) (none, false) [] [] tail) := by
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]
  congr 2
  funext stack
  cases stack <;> simp [Function.update]

theorem drain_nil (state : Option Symbol × Bool) :
    machine.step (config (some .drain) state [] [] []) =
      some (config none (none, true) [.bit state.2] [] []) := by
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]
  congr 2
  funext stack
  cases stack <;> simp [Function.update]

/-- Enlarging a bound retains the actual execution witness and its exact steps. -/
def within {State : Type} {step : State → Option State} {before : State} {after : Option State}
    {bound enlarged : Nat} (run : EvalsToInTime step before after bound) (le : bound ≤ enlarged) :
    EvalsToInTime step before after enlarged :=
  ⟨run.toEvalsTo, run.steps_le_m.trans le⟩

def scan_run (left right : List Bool) (state : Option Symbol × Bool)
    (temporary stored : List Symbol) :
    EvalsToInTime machine.step
      (config (some .scan) state (input left right) temporary stored)
      (some (config (some .restore) (some .delimiter, state.2)
        (right.map Symbol.bit) ((left.map Symbol.bit).reverse ++ temporary) stored))
      (left.length + 1) := by
  induction left generalizing state temporary with
  | nil =>
      simpa [input] using SymbolMapMachine.oneStep
        (scan_delimiter state (right.map Symbol.bit) temporary stored)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (scan_bit state head (input tail right) temporary stored)
      have rest := ih (some (.bit head), state.2) (.bit head :: temporary)
      simpa [input] using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

def restore_run (temporary input left : List Symbol) (state : Option Symbol × Bool) :
    EvalsToInTime machine.step
      (config (some .restore) state input temporary left)
      (some (config (some .compare) (none, state.2) input [] (temporary.reverse ++ left)))
      (temporary.length + 1) := by
  induction temporary generalizing state left with
  | nil => simpa using SymbolMapMachine.oneStep (restore_nil state input left)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (restore_cons state head input tail left)
      have rest := ih (head :: left) (some head, state.2)
      simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

def drain_run (left : List Symbol) (state : Option Symbol × Bool) :
    EvalsToInTime machine.step
      (config (some .drain) state [] [] left)
      (some (config none (none, true) [.bit (state.2 && decide (left = []))] [] []))
      (left.length + 1) := by
  induction left generalizing state with
  | nil => simpa using SymbolMapMachine.oneStep (drain_nil state)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (drain_cons state head tail)
      have rest := ih (none, false)
      simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

def compare_run (left right : List Bool) (state : Option Symbol × Bool) :
    EvalsToInTime machine.step
      (config (some .compare) state (right.map Symbol.bit) [] (left.map Symbol.bit))
      (some (config none (none, true) [.bit (state.2 && decide (left = right))] [] []))
      (left.length + right.length + 2) := by
  induction right generalizing left state with
  | nil =>
      have first := SymbolMapMachine.oneStep (compare_nil state (left.map Symbol.bit))
      have rest := drain_run (left.map Symbol.bit) (none, state.2)
      simpa using EvalsToInTime.trans _ 1 ((left.map Symbol.bit).length + 1) _ _ _ first rest
  | cons head tail ih =>
      cases left with
      | nil =>
        have first := SymbolMapMachine.oneStep (compare_cons_nil state head (tail.map Symbol.bit))
        have rest := ih [] (none, false)
        simpa using EvalsToInTime.trans _ 1 (0 + tail.length + 2) _ _ _ first rest
      | cons left rest =>
        have first := SymbolMapMachine.oneStep (compare_cons_cons state head left
          (tail.map Symbol.bit) (rest.map Symbol.bit))
        have later := ih rest (none, state.2 && (head == left))
        have joined := EvalsToInTime.trans _ 1 (rest.length + tail.length + 2) _ _ _ first later
        have bound : rest.length + tail.length + 2 + 1 ≤ (left :: rest).length + (head :: tail).length + 2 := by simp; omega
        have enlarged := within joined bound
        cases left <;> cases head <;> simpa using enlarged

private theorem init_eq (left right : List Bool) :
    initList machine (input left right) = config (some .scan) (none, true) (input left right) [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext stack
  cases stack
  · simp; rfl
  · simp
  · simp

private theorem halt_eq (value : Bool) :
    haltList machine [.bit value] = config none (none, true) [.bit value] [] [] := by
  simp only [haltList, machine, config]
  congr 1
  funext stack
  cases stack
  · simp; rfl
  · simp
  · simp

/-- This compares the actual two encoded fields in a linear number of finite
machine steps. Neither field is decoded into an unbounded register. -/
def outputs (left right : List Bool) :
    TM2OutputsInTime machine (input left right) (some [.bit (decide (left = right))])
      (3 * left.length + right.length + 4) := by
  have scanned := scan_run left right (none, true) [] []
  simp only [List.append_nil] at scanned
  have restored := restore_run (left.map Symbol.bit).reverse (right.map Symbol.bit) []
    (some .delimiter, true)
  simp only [List.reverse_reverse, List.append_nil] at restored
  have compared := compare_run left right (none, true)
  have first := EvalsToInTime.trans _ (left.length + 1)
    ((left.map Symbol.bit).reverse.length + 1) _ _ _ scanned restored
  have joined := EvalsToInTime.trans _
    (((left.map Symbol.bit).reverse.length + 1) + (left.length + 1))
    (left.length + right.length + 2) _ _ _ first compared
  change EvalsToInTime _ (initList machine (input left right))
    (some (haltList machine [.bit (decide (left = right))])) _
  rw [init_eq, halt_eq]
  simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm,
    Nat.succ_mul, Nat.mul_add] using joined

/-- The field delimiter contributes one symbol to the actual input size. -/
theorem input_length (left right : List Bool) :
    (input left right).length = left.length + right.length + 1 := by simp [input]; omega

set_option backward.isDefEq.respectTransparency false in
noncomputable def computable : TM2ComputableInPolyTime
    (fun fields : List Bool × List Bool => input fields.1 fields.2)
    (fun result : Bool => [Symbol.bit result])
    (fun fields : List Bool × List Bool => decide (fields.1 = fields.2)) where
  tm := machine
  inputAlphabet := Equiv.refl Symbol
  outputAlphabet := Equiv.refl Symbol
  time := C 3 * X + C 1
  outputsFun fields := by
    change TM2OutputsInTime machine ((input fields.1 fields.2).map id)
      (some ([Symbol.bit (decide (fields.1 = fields.2))].map id)) _
    simp only [List.map_id_fun]
    apply within (outputs fields.1 fields.2)
    simp only [eval_add, eval_mul, eval_C, eval_X, input_length]
    omega

/-- A binary reference has its entire word charged, even when it is refused. -/
def referenceInput (references : Nat × Nat) : List Symbol :=
  input (Computability.encodingNatBool.encode references.1)
    (Computability.encodingNatBool.encode references.2)

theorem referenceInput_length (left right : Nat) :
    (referenceInput (left, right)).length = Nat.size left + Nat.size right + 1 := by
  simp only [referenceInput, input_length]
  change encodedSize Computability.encodingNatBool left +
    encodedSize Computability.encodingNatBool right + 1 = _
  rw [encodedSize_binary, encodedSize_binary]

set_option backward.isDefEq.respectTransparency false in
/-- Equality of natural-number references is realized over their complete binary
encodings. The machine is polynomial in bits, including rejected references. -/
noncomputable def referencesComputable : TM2ComputableInPolyTime
    referenceInput (fun result : Bool => [Symbol.bit result])
    (fun references : Nat × Nat => decide (references.1 = references.2)) where
  tm := machine
  inputAlphabet := Equiv.refl Symbol
  outputAlphabet := Equiv.refl Symbol
  time := C 3 * X + C 1
  outputsFun references := by
    have compared := computable.outputsFun
      (Computability.encodingNatBool.encode references.1,
       Computability.encodingNatBool.encode references.2)
    have exactReference :
        Computability.encodingNatBool.encode references.1 =
          Computability.encodingNatBool.encode references.2 ↔ references.1 = references.2 :=
      Computability.encodingNatBool.encode_injective.eq_iff
    change TM2OutputsInTime machine
      ((input (Computability.encodingNatBool.encode references.1)
        (Computability.encodingNatBool.encode references.2)).map id)
      (some ([Symbol.bit (decide (Computability.encodingNatBool.encode references.1 =
        Computability.encodingNatBool.encode references.2))].map id))
      ((C 3 * X + C 1).eval (referenceInput references).length) at compared
    change TM2OutputsInTime machine ((referenceInput references).map id)
      (some ([Symbol.bit (decide (references.1 = references.2))].map id))
      ((C 3 * X + C 1).eval (referenceInput references).length)
    simpa only [referenceInput, exactReference] using compared

/-- Counting a single reference occurrence cannot polynomially bound its binary
field length. This applies to raw input before chronological refusal. -/
theorem reference_bits_not_bounded_by_occurrence_count :
    ¬ PolyBoundedBy Nat.size (fun _ : Nat => 1) := by
  rintro ⟨polynomial, bound⟩
  have tooLarge := bound (2 ^ polynomial.eval 1)
  rw [Nat.size_pow] at tooLarge
  change polynomial.eval 1 + 1 ≤ polynomial.eval 1 at tooLarge
  omega

theorem scan_nil (state : Option Symbol × Bool) (temporary left : List Symbol) :
    machine.step (config (some .scan) state [] temporary left) =
      some (config (some .restore) (none, false) [] temporary left) := by
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]
  congr 2
  funext stack
  cases stack <;> simp [Function.update]

/-- Missing field delimiters are handled by finite control and retain their
full scanning cost, rather than returning an unchecked comparison. -/
def missingDelimiterScan (word : List Bool) (temporary left : List Symbol)
    (state : Option Symbol × Bool) :
    EvalsToInTime machine.step
      (config (some .scan) state (word.map Symbol.bit) temporary left)
      (some (config (some .restore) (none, false) [] ((word.map Symbol.bit).reverse ++ temporary) left))
      (word.length + 1) := by
  induction word generalizing state temporary with
  | nil => simpa using SymbolMapMachine.oneStep (scan_nil state temporary left)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (scan_bit state head (tail.map Symbol.bit) temporary left)
      have rest := ih (.bit head :: temporary) (some (.bit head), state.2)
      simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

/-- A missing delimiter produces a real negative machine output after all
internal stacks have been cleared. -/
def missingDelimiterOutputs (word : List Bool) :
    TM2OutputsInTime machine (word.map Symbol.bit) (some [.bit false]) (3 * word.length + 4) := by
  have scanned := missingDelimiterScan word [] [] (none, true)
  simp only [List.append_nil] at scanned
  have restored := restore_run (word.map Symbol.bit).reverse [] [] (none, false)
  simp only [List.reverse_reverse, List.append_nil] at restored
  have compared := compare_run word [] (none, false)
  have first := EvalsToInTime.trans _ (word.length + 1)
    ((word.map Symbol.bit).reverse.length + 1) _ _ _ scanned restored
  have joined := EvalsToInTime.trans _
    (((word.map Symbol.bit).reverse.length + 1) + (word.length + 1))
    (word.length + 0 + 2) _ _ _ first compared
  change EvalsToInTime _ (initList machine (word.map Symbol.bit))
    (some (haltList machine [.bit false])) _
  have initial : initList machine (word.map Symbol.bit) =
      config (some .scan) (none, true) (word.map Symbol.bit) [] [] := by
    simp only [initList, machine, config]
    congr 1
    funext stack
    cases stack
    · simp; rfl
    · simp
    · simp
  rw [initial, halt_eq]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add, Nat.mul_comm, Nat.succ_mul, Nat.mul_succ] using joined

set_option backward.isDefEq.respectTransparency false in
/-- The realized primitive keeps the actual binary field length in its clock. -/
noncomputable def referenceOutputs (left right : Nat) :
    TM2OutputsInTime machine (referenceInput (left, right))
      (some [.bit (decide (left = right))]) (3 * (referenceInput (left, right)).length + 1) := by
  have compared := referencesComputable.outputsFun (left, right)
  change TM2OutputsInTime machine ((referenceInput (left, right)).map id)
    (some ([Symbol.bit (decide (left = right))].map id))
    ((C 3 * X + C 1).eval (referenceInput (left, right)).length) at compared
  simpa only [List.map_id_fun, id_eq, eval_add, eval_mul, eval_C, eval_X] using compared

/-- The same physical address has a positive executed comparison. -/
noncomputable def sameReference (index : Nat) :
    TM2OutputsInTime machine (referenceInput (index, index)) (some [.bit true])
      (3 * (referenceInput (index, index)).length + 1) := by
  simpa using referenceOutputs index index

/-- A different address is refused without iterating up to its numeric value. -/
noncomputable def differentReference (left right : Nat) (different : left ≠ right) :
    TM2OutputsInTime machine (referenceInput (left, right)) (some [.bit false])
      (3 * (referenceInput (left, right)).length + 1) := by
  simpa [different] using referenceOutputs left right

end BinaryReferenceMachine
namespace CertificateRelocation
open Mettapedia.GSLT.LanguageDef.KernelAuthority

variable {ClaimSymbol Tag Payload : Type}

/-- Measure a word claim and its chronological row certificate by their physical
symbol counts. Each row symbol carries a tag and a reference payload. -/
def source (checker : Checker (List ClaimSymbol) (List (Tag × Payload))) :
    SizedChecker (List ClaimSymbol) (List (Tag × Payload)) where
  toChecker := checker
  claimSize := List.length
  certificateSize := List.length

/-- The target certificate carries its claim and relocated rows. The target
checks the claim and replays the same row checker in the old tag namespace;
reference payloads are retained verbatim. This is a representation transport,
not a translation between different logical kernels. -/
def target [DecidableEq ClaimSymbol] (checker : Checker (List ClaimSymbol) (List (Tag × Payload)))
    (rename : Tag ≃ Tag) :
    SizedChecker (List ClaimSymbol) (List ClaimSymbol × List (Tag × Payload)) where
  check claim certificate := decide (claim = certificate.1) &&
    checker.check claim (certificate.2.map fun row => (rename.symm row.1, row.2))
  claimSize := List.length
  certificateSize certificate := certificate.1.length + certificate.2.length

/-- The structural certificate compiler changes row tags, retains shared
reference payloads, and carries the claim explicitly. -/
def translate (rename : Tag ≃ Tag) (claim : List ClaimSymbol) (rows : List (Tag × Payload)) :
    List ClaimSymbol × List (Tag × Payload) :=
  (claim, rows.map fun row => (rename row.1, row.2))

/-- Forward and inverse tag relocation cancel on every physical row. -/
theorem map_inverse (rename : Tag ≃ Tag) (rows : List (Tag × Payload)) :
    (rows.map fun row => (rename row.1, row.2)).map
      (fun row => (rename.symm row.1, row.2)) = rows := by
  simp [List.map_map, Function.comp_def]

/-- Checking transported evidence gives exactly the original verdict. -/
theorem check_translate [DecidableEq ClaimSymbol] (checker : Checker (List ClaimSymbol) (List (Tag × Payload)))
    (rename : Tag ≃ Tag) (claim : List ClaimSymbol) (rows : List (Tag × Payload)) :
    (target checker rename).check claim (translate rename claim rows) = checker.check claim rows := by
  simp only [target, translate, decide_true, Bool.true_and]
  rw [map_inverse]

/-- Refused certificates stay refused after structural transport. -/
theorem refused_translate [DecidableEq ClaimSymbol]
    (checker : Checker (List ClaimSymbol) (List (Tag × Payload))) (rename : Tag ≃ Tag)
    (claim : List ClaimSymbol) (rows : List (Tag × Payload))
    (refused : checker.check claim rows = false) :
    (target checker rename).check claim (translate rename claim rows) = false := by
  rw [check_translate, refused]

/-- Carrying a different claim cannot authorize evidence for the requested claim. -/
theorem claim_mismatch_refused [DecidableEq ClaimSymbol]
    (checker : Checker (List ClaimSymbol) (List (Tag × Payload))) (rename : Tag ≃ Tag)
    (claim : List ClaimSymbol) (certificate : List ClaimSymbol × List (Tag × Payload))
    (mismatch : claim ≠ certificate.1) :
    (target checker rename).check claim certificate = false := by
  simp [target, mismatch]

/-- Logical preservation and linear output-size bound for row relocation. -/
def sizeSimulation [DecidableEq ClaimSymbol] (checker : Checker (List ClaimSymbol) (List (Tag × Payload)))
    (rename : Tag ≃ Tag) : SizeSimulation (target checker rename) (source checker) where
  translate := translate rename
  preserves claim rows accepted := by simpa only [check_translate, source] using accepted
  sizeBound := ⟨X, fun input => by simp [target, source, translate, SizedChecker.inputSize]⟩

/-- The input word contains tagged claim symbols followed by tagged row symbols. -/
def encoding : Computability.Encoding (List ClaimSymbol × List (Tag × Payload))
    (ClaimSymbol ⊕ (Tag × Payload)) :=
  Computability.encodingProd (Computability.encodingList _) (Computability.encodingList _)

/-- The actual symbol relocation distinguishes claim symbols from row symbols;
it changes only row tags. -/
def relocateSymbol (rename : Tag ≃ Tag) :
    (ClaimSymbol ⊕ (Tag × Payload)) → (ClaimSymbol ⊕ (Tag × Payload))
  | .inl symbol => .inl symbol
  | .inr row => .inr (rename row.1, row.2)

/-- Serialization commutes with structural relocation without expanding edges. -/
theorem encode_translate (rename : Tag ≃ Tag)
    (input : List ClaimSymbol × List (Tag × Payload)) :
    encoding.encode (translate rename input.1 input.2) =
      (encoding.encode input).map (relocateSymbol rename) := by
  simp [encoding, translate, relocateSymbol, Computability.encodingProd,
    Computability.encodingList, List.map_map, Function.comp_def]

/-- A genuine operational simulation for structural shared-reference relocation.
Unlike a supplied clock, its bound is derived from the actual finite-stack
execution over the serialized claim and row data. -/
noncomputable def operationalSimulation
    [Fintype ClaimSymbol] [DecidableEq ClaimSymbol] [Fintype Tag] [Fintype Payload]
    [Inhabited Tag] [Inhabited Payload]
    (checker : Checker (List ClaimSymbol) (List (Tag × Payload))) (rename : Tag ≃ Tag) :
    OperationalPSimulation (target checker rename) (source checker) encoding encoding := by
  haveI : Inhabited (ClaimSymbol ⊕ (Tag × Payload)) := ⟨.inr default⟩
  apply SymbolMapMachine.simulation (Γ := ClaimSymbol ⊕ (Tag × Payload)) (sizeSimulation checker rename) encoding encoding
    (relocateSymbol rename)
  · exact ⟨X, fun input => by
      simp [encodedSize, encoding, Computability.encodingProd, Computability.encodingList,
        source, SizedChecker.inputSize]⟩
  · exact encode_translate rename

end CertificateRelocation

end Mettapedia.GSLT.LanguageDef.ProofSystems


namespace Mettapedia.GSLT.LanguageDef.ProofSystems.ExecutedDispatch

open Turing StateTransition Polynomial
open Mettapedia.Computability.StackMachineComposition

def inputEncoding {Source InputAlphabet : Type} (encode : Source → List InputAlphabet)
    (success refusal : InputAlphabet) : Option Source → List InputAlphabet
  | none => [refusal]
  | some source => success :: encode source

/-- Optional computation dispatches through an actual finite status cell. A
refused input never calls the inner program, and all successful fields retain
their physical order. The clock includes the status transition and cleanup. -/
noncomputable def realization {Source Target InputAlphabet OutputAlphabet : Type}
    {sourceEncoding : Source → List InputAlphabet} {targetEncoding : Target → List OutputAlphabet}
    {operation : Source → Target}
    (inner : TM2ComputableInPolyTime sourceEncoding targetEncoding operation)
    (success refusal : InputAlphabet) (distinct : refusal ≠ success) (refused : Target) :
    TM2ComputableInPolyTime (inputEncoding sourceEncoding success refusal) targetEncoding
      (fun source => source.elim refused operation) := by
  classical
  let accept : inner.tm.Γ inner.tm.k₀ → Bool :=
    fun tag => decide (tag = inner.inputAlphabet.symm success)
  let refusalWord := (targetEncoding refused).map inner.outputAlphabet.symm
  refine
    { tm := Dispatch.machine inner.tm accept refusalWord
      inputAlphabet := inner.inputAlphabet
      outputAlphabet := inner.outputAlphabet
      time := inner.time + X + C 2
      outputsFun := ?_ }
  intro source
  cases source with
  | none =>
      have rejected : accept (inner.inputAlphabet.symm refusal) = false := by
        simp [accept, distinct]
      have run := Dispatch.outputs_refused inner.tm accept refusalWord
        (inner.inputAlphabet.symm refusal) [] rejected
      change EvalsToInTime _ _ _ _
      refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
      apply run.steps_le_m.trans
      simp [inputEncoding]
  | some source =>
      have run := Dispatch.outputs_success inner.tm accept refusalWord
        (inner.inputAlphabet.symm success)
        ((sourceEncoding source).map inner.inputAlphabet.symm)
        ((targetEncoding (operation source)).map inner.outputAlphabet.symm)
        (inner.time.eval (sourceEncoding source).length)
        (by simp [accept]) (inner.outputsFun source)
      change EvalsToInTime _ _ _ _
      refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
      apply run.steps_le_m.trans
      have monotone := eval_mono inner.time
        (Nat.le_succ (sourceEncoding source).length)
      simp only [Nat.succ_eq_add_one] at monotone
      simp only [inputEncoding, List.length_cons, eval_add, eval_X, eval_C]
      omega

end Mettapedia.GSLT.LanguageDef.ProofSystems.ExecutedDispatch
