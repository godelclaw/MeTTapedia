import Mettapedia.GSLT.LanguageDef.ProofSystems
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
of a different logical kernel. In particular, unbounded binary reference encoding
and the HOL rule-to-MM0 translation require their own realizations.

The cost unit is Mathlib's TM2 statement execution. Each fixed machine has finite
state and alphabet tables, and each statement contains finitely many stack
operations. This is an operational complexity result, not a native runtime or
wall-clock performance assertion.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ProofSystems
open Turing StateTransition Polynomial

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
