import Mettapedia.Machines.FunctionalCorrespondence

/-!
# Shared substrate, divergent control: the two machines separated by a term

The two machines of `FunctionalCorrespondence` interpret the *same* term
type. This file makes the substrate/control split formal:

* `MachineCore` packages a machine as (state, load, step) over a term type;
  `cekCore` and `krivineCore` are two inhabitants over the one `Tm` — the
  shared-substrate claim as a type-level fact.
* The **strategy separation witness**: for the term
  `tKO = (λx. λy. x) 7 Ω`, the call-by-value evaluator returns nothing at
  every fuel (`evalV_tKO_none` — the discarded argument `Ω` is still
  evaluated and diverges), while the call-by-name evaluator computes `7`
  outright (`evalN_tKO`, a kernel `rfl`). So eager and demand-driven
  control genuinely differ on the shared substrate; no fairness or fuel
  bound rescues the eager core on this term.

The divergence proofs are structural recursions over definitional two-step
unrollings of the evaluator. No project-specific axioms or proof placeholders
are introduced.

No common store or heap interface is asserted here.  The CEK environment and
the Krivine thunk environment are components of their derived controls, while
Prime's call-by-need heap additionally requires memoization, update, and cycle
laws absent from call-by-name.  A shared store interface belongs only after
those concrete machines supply refinement maps into it.
-/

namespace Mettapedia.Machines

/-! ## Machines as data over a shared term substrate -/

/-- A machine core: states, a loader, and a step function over a term
substrate. Different evaluation semantics inhabit this signature with
different control structures over the *same* terms. -/
structure MachineCore (Term : Type) where
  State : Type
  load : Term → State
  step : State → Option State

/-- The eager (call-by-value) control core over `Tm`. -/
def cekCore : MachineCore Tm where
  State := CEK.St
  load := fun t => ⟨.ev t [], []⟩
  step := CEK.step

/-- The demand-driven (call-by-name) control core over `Tm`. -/
def krivineCore : MachineCore Tm where
  State := Krivine.KSt
  load := fun t => ⟨t, [], []⟩
  step := Krivine.kstep

/-! ## The separation witness: `(λx. λy. x) 7 Ω` -/

/-- `x x` — the self-application body. -/
def selfApp : Tm := .app (.var 0) (.var 0)

/-- `δ = λx. x x`. -/
def delta : Tm := .lam selfApp

/-- `Ω = δ δ`, the canonical divergent term. -/
def bigOmega : Tm := .app delta delta

/-- The δ-closure value the CBV evaluator builds for `δ`. -/
def deltaV : CEK.Val := .clo selfApp []

/-- `K = λx. λy. x`: returns its first argument, discards its second. -/
def kComb : Tm := .lam (.lam (.var 1))

/-- `tKO = (K 7) Ω`: the answer needs only `7`; the discarded argument
diverges. -/
def tKO : Tm := .app (.app kComb (.lit 7)) bigOmega

/-- Under call-by-value, self-application of the δ-closure never returns,
at any fuel: two evaluator layers reproduce the same call. -/
theorem evalV_selfApp_none : ∀ n, CEK.evalV n [deltaV] selfApp = none
  | 0 => rfl
  | 1 => rfl
  | n + 2 => evalV_selfApp_none (n + 1)

/-- Under call-by-value, `Ω` never returns, at any fuel. -/
theorem evalV_bigOmega_none : ∀ n, CEK.evalV n [] bigOmega = none
  | 0 => rfl
  | 1 => rfl
  | n + 2 => evalV_selfApp_none (n + 1)

/-- **Eager control diverges on `tKO`** at every fuel: call-by-value must
evaluate the discarded argument, and the discarded argument is `Ω`. -/
theorem evalV_tKO_none : ∀ n, CEK.evalV n [] tKO = none := by
  intro n
  cases n with
  | zero => rfl
  | succ m =>
    have hunfold : CEK.evalV (m + 1) [] tKO =
        (match CEK.evalV m [] (.app kComb (.lit 7)) with
         | none => none
         | some fv =>
           match CEK.evalV m [] bigOmega with
           | none => none
           | some av =>
             match fv with
             | .lit _ => none
             | .clo b ρ' => CEK.evalV m (av :: ρ') b) := rfl
    rw [hunfold]
    cases hf : CEK.evalV m [] (.app kComb (.lit 7)) with
    | none => exact rfl
    | some fv =>
      rw [evalV_bigOmega_none m]

/-- **Demand-driven control computes `tKO`** — outright, by kernel
computation: the discarded argument is never demanded. -/
theorem evalN_tKO : Krivine.evalN 6 [] tKO = some (.lit 7) := rfl

/-- The strategy separation, packaged: one substrate term on which the two
control cores of the one machine family provably differ — the eager core
returns nothing at every fuel while the demand-driven core answers. -/
theorem strategy_separation :
    (∀ n, CEK.evalV n [] tKO = none) ∧ Krivine.evalN 6 [] tKO = some (.lit 7) :=
  ⟨evalV_tKO_none, rfl⟩

/-- Demand-driven success transports to the Krivine machine itself: the
machine walk for `tKO` ends presenting the literal `7`. -/
theorem krivine_machine_computes_tKO :
    ∃ st, Krivine.KSteps ⟨tKO, [], []⟩ st ∧ Krivine.Presents (.lit 7) [] st :=
  Krivine.eval_to_machine 6 [] tKO (.lit 7) rfl []

/-! ## Checked code loading and instruction validity -/

namespace MachineCore

variable {Term Image : Type}

/-! ## Selected machine families

A configuration retains one fixed package selection and the selected machine's
own question and state types. A selection may include a language, loaded
library rows and primitive realizations; it is not a common guest logic.
Mutable provider/world revisions remain inside the selected state or require
an independently justified crossing to another package.
-/

/-- Construct a common computational carrier for independently supplied
machines, without identifying their questions or control states. -/
def familyCore {Selection : Type} {Question : Selection → Type}
    (kernels : (selection : Selection) → MachineCore (Question selection)) :
    MachineCore (Σ selection, Question selection) where
  State := Σ selection, (kernels selection).State
  load question := ⟨question.1, (kernels question.1).load question.2⟩
  step state := ((kernels state.1).step state.2).map (Sigma.mk state.1)

@[simp] theorem familyCore_load {Selection : Type} {Question : Selection → Type}
    (kernels : (selection : Selection) → MachineCore (Question selection))
    (selection : Selection) (question : Question selection) :
    (familyCore kernels).load ⟨selection, question⟩ =
      ⟨selection, (kernels selection).load question⟩ := rfl

/-- Every successful family transition is an actual transition of the retained
kernel. Conversely, that transition constructs the corresponding family step. -/
theorem familyCore_step_some_iff {Selection : Type} {Question : Selection → Type}
    (kernels : (selection : Selection) → MachineCore (Question selection))
    (state next : (familyCore kernels).State) :
    (familyCore kernels).step state = some next ↔
      ∃ inner : (kernels state.1).State,
        (kernels state.1).step state.2 = some inner ∧ next = ⟨state.1, inner⟩ := by
  constructor
  · intro advanced
    obtain ⟨inner, actual, packed⟩ := Option.map_eq_some_iff.mp advanced
    exact ⟨inner, actual, packed.symm⟩
  · rintro ⟨inner, actual, rfl⟩
    simp [familyCore, actual]

theorem familyCore_step_keeps_selection {Selection : Type} {Question : Selection → Type}
    (kernels : (selection : Selection) → MachineCore (Question selection))
    {state next : (familyCore kernels).State}
    (advanced : (familyCore kernels).step state = some next) : next.1 = state.1 := by
  obtain ⟨_, _, packed⟩ := (familyCore_step_some_iff kernels state next).mp advanced
  rw [packed]

@[simp] theorem familyCore_step_none_iff {Selection : Type} {Question : Selection → Type}
    (kernels : (selection : Selection) → MachineCore (Question selection))
    (state : (familyCore kernels).State) :
    (familyCore kernels).step state = none ↔ (kernels state.1).step state.2 = none := by
  exact Option.map_eq_none_iff

/-- No finite chain of family transitions silently changes the selected
kernel, including chains from a resumed retained configuration. -/
theorem familyCore_reachable_keeps_selection {Selection : Type} {Question : Selection → Type}
    (kernels : (selection : Selection) → MachineCore (Question selection))
    {state last : (familyCore kernels).State}
    (reached : Relation.ReflTransGen
      (fun before after => (familyCore kernels).step before = some after) state last) :
    last.1 = state.1 := by
  induction reached using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head advanced _ ih => exact ih.trans (familyCore_step_keeps_selection kernels advanced)

/-- Select a package, then decode a question using that package's own reader.
Either stage can refuse. The reader retains the selected package in the result. -/
def decodeSelected {Selection : Type} {Question : Selection → Type}
    (select : Image → Option Selection)
    (decode : (selection : Selection) → Image → Option (Question selection))
    (image : Image) : Option (Σ selection, Question selection) :=
  (select image).bind fun selection => (decode selection image).map (Sigma.mk selection)

/-- Successful decoding includes both actual reader equations and the retained
dependent question; the selected interpretation cannot be inferred from bytes. -/
theorem decodeSelected_some_iff {Selection : Type} {Question : Selection → Type}
    (select : Image → Option Selection)
    (decode : (selection : Selection) → Image → Option (Question selection))
    (image : Image) (question : Σ selection, Question selection) :
    decodeSelected select decode image = some question ↔
      ∃ selection inner, select image = some selection ∧
        decode selection image = some inner ∧ question = ⟨selection, inner⟩ := by
  constructor
  · intro decoded
    obtain ⟨selection, selected, body⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨inner, parsed, packed⟩ := Option.map_eq_some_iff.mp body
    exact ⟨selection, inner, selected, parsed, packed.symm⟩
  · rintro ⟨selection, inner, selected, parsed, rfl⟩
    simp [decodeSelected, selected, parsed]

theorem decodeSelected_none_iff {Selection : Type} {Question : Selection → Type}
    (select : Image → Option Selection)
    (decode : (selection : Selection) → Image → Option (Question selection)) (image : Image) :
    decodeSelected select decode image = none ↔
      select image = none ∨ ∃ selection,
        select image = some selection ∧ decode selection image = none := by
  cases selected : select image <;> simp [decodeSelected, selected]

/-- Load a code image only after its decoder supplies a source question.
Decoder refusal creates no machine configuration. -/
def loadCode (core : MachineCore Term) (decode : Image → Option Term)
    (image : Image) : Option core.State :=
  (decode image).map core.load

theorem loadCode_some_iff (core : MachineCore Term) (decode : Image → Option Term)
    (image : Image) (state : core.State) :
    core.loadCode decode image = some state ↔
      ∃ question, decode image = some question ∧ core.load question = state := by
  cases decoded : decode image <;> simp [loadCode, decoded]

@[simp] theorem loadCode_none_iff (core : MachineCore Term) (decode : Image → Option Term)
    (image : Image) : core.loadCode decode image = none ↔ decode image = none := by
  cases decoded : decode image <;> simp [loadCode, decoded]

@[simp] theorem loadCode_identity (core : MachineCore Term) (question : Term) :
    core.loadCode some question = some (core.load question) := rfl

/-- Loading through two partial readers obeys their ordered composition.
A failure in either reader cannot be replaced by a fabricated input. -/
theorem loadCode_comp {Outer : Type} (core : MachineCore Term)
    (decode : Image → Option Term) (outer : Outer → Option Image) (image : Outer) :
    core.loadCode (fun packet => (outer packet).bind decode) image =
      (outer image).bind (core.loadCode decode) := by
  cases decoded : outer image <;> simp [loadCode, decoded]

/-- A constructed compiler/readback inverse supplies exact canonical loading. -/
theorem loadCode_encode (core : MachineCore Term) (encode : Term → Image)
    (decode : Image → Option Term)
    (roundtrip : ∀ question, decode (encode question) = some question) (question : Term) :
    core.loadCode decode (encode question) = some (core.load question) := by
  simp [loadCode, roundtrip]

/-- Selected loading composes the two partial readers with the actual kernel
loader. No failed selection or reader is replaced by a default interpretation. -/
theorem familyCore_loadCode_eq {Selection : Type} {Question : Selection → Type}
    (kernels : (selection : Selection) → MachineCore (Question selection))
    (select : Image → Option Selection)
    (decode : (selection : Selection) → Image → Option (Question selection)) (image : Image) :
    (familyCore kernels).loadCode (decodeSelected select decode) image =
      (select image).bind fun selection =>
        ((kernels selection).loadCode (decode selection) image).map (Sigma.mk selection) := by
  cases selected : select image <;>
    simp [loadCode, decodeSelected, selected, familyCore, Option.map_map, Function.comp_def]

theorem familyCore_loadCode_some_iff {Selection : Type} {Question : Selection → Type}
    (kernels : (selection : Selection) → MachineCore (Question selection))
    (select : Image → Option Selection)
    (decode : (selection : Selection) → Image → Option (Question selection))
    (image : Image) (state : (familyCore kernels).State) :
    (familyCore kernels).loadCode (decodeSelected select decode) image = some state ↔
      ∃ selection question, select image = some selection ∧
        decode selection image = some question ∧ state = ⟨selection, (kernels selection).load question⟩ := by
  rw [loadCode_some_iff]
  constructor
  · rintro ⟨question, decoded, loaded⟩
    obtain ⟨selection, inner, selected, parsed, rfl⟩ :=
      (decodeSelected_some_iff select decode image question).mp decoded
    exact ⟨selection, inner, selected, parsed, loaded.symm⟩
  · rintro ⟨selection, question, selected, parsed, rfl⟩
    refine ⟨⟨selection, question⟩, ?_, rfl⟩
    exact (decodeSelected_some_iff select decode image _).mpr
      ⟨selection, question, selected, parsed, rfl⟩

theorem familyCore_loadCode_keeps_selection {Selection : Type} {Question : Selection → Type}
    (kernels : (selection : Selection) → MachineCore (Question selection))
    (select : Image → Option Selection)
    (decode : (selection : Selection) → Image → Option (Question selection))
    {image : Image} {state : (familyCore kernels).State}
    (loaded : (familyCore kernels).loadCode (decodeSelected select decode) image = some state) :
    select image = some state.1 := by
  obtain ⟨selection, _, selected, _, rfl⟩ :=
    (familyCore_loadCode_some_iff kernels select decode image state).mp loaded
  exact selected

theorem familyCore_loadCode_none_iff {Selection : Type} {Question : Selection → Type}
    (kernels : (selection : Selection) → MachineCore (Question selection))
    (select : Image → Option Selection)
    (decode : (selection : Selection) → Image → Option (Question selection)) (image : Image) :
    (familyCore kernels).loadCode (decodeSelected select decode) image = none ↔
      select image = none ∨ ∃ selection,
        select image = some selection ∧ decode selection image = none := by
  rw [loadCode_none_iff, decodeSelected_none_iff]

/-- A VM's fetched instruction must be legal in its actual retained state.
Instances relate this independent legality judgment to their executable step;
code admission alone does not supply this contract. -/
structure InstructionContract (core : MachineCore Term) (Opcode : Type) where
  fetch : core.State → Option Opcode
  Legal : core.State → Opcode → Prop
  enabled_iff : ∀ state,
    (∃ next, core.step state = some next) ↔
      ∃ opcode, fetch state = some opcode ∧ Legal state opcode

namespace InstructionContract

variable {Opcode : Type} {core : MachineCore Term}

/-- Every executed instruction carries the instance's legality witness. -/
theorem executed (contract : InstructionContract core Opcode)
    {state next : core.State} (advanced : core.step state = some next) :
    ∃ opcode, contract.fetch state = some opcode ∧ contract.Legal state opcode :=
  (contract.enabled_iff state).mp ⟨next, advanced⟩

/-- A missing or illegal fetched instruction has no outgoing core step.
Answer and fault observers still decide how the stopped state is reported. -/
theorem invalid_stops (contract : InstructionContract core Opcode)
    {state : core.State}
    (invalid : ¬ ∃ opcode, contract.fetch state = some opcode ∧ contract.Legal state opcode) :
    core.step state = none := by
  cases advanced : core.step state with
  | none => rfl
  | some next => exact False.elim (invalid (contract.executed advanced))

/-- A legal fetched instruction constructs an executable successor. -/
theorem legal_advances (contract : InstructionContract core Opcode)
    {state : core.State} {opcode : Opcode}
    (fetched : contract.fetch state = some opcode) (legal : contract.Legal state opcode) :
    ∃ next, core.step state = some next :=
  (contract.enabled_iff state).mpr ⟨opcode, fetched, legal⟩

end InstructionContract
end MachineCore

end Mettapedia.Machines
