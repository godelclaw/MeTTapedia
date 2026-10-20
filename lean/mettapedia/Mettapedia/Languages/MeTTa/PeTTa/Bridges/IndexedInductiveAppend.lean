import Mettapedia.GSLT.LanguageDef.IndexedInductiveVectorArray
import Mettapedia.Languages.MeTTa.PeTTa.ProgramQuotation
import Mettapedia.Languages.MeTTa.PeTTa.BridgeForms
import Mettapedia.Languages.MeTTa.PeTTa.StdLibCalls

/-!
# Array execution of the selected authored append program

The library uses existing expression arrays and integer operations. Its
execution is proved in the shared PeTTa machine, retaining the complete answer
packet. Source comparison uses the actual checked textual Nat/Vec program.
The source reader and the C/GMP implementation remain qualification boundaries.
Arguments are captured values; producers must be sequenced explicitly.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppend

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst applySubst_nil)
open Mettapedia.GSLT.LanguageDef IndexedInductive IndexedInductiveNatVec
open Effects (State)
open Eval BridgeKit ProgramQuotation

def source : QuotedProgram := petta_source_file%
  "../../../../../../../metta/gslt/lib/gslt_inductive_append.metta"
  sha256 "bf0657e63c471274ca19c5c387a903830236f970deada293f7fdb5425962e719"

def library : Library := ⟨⟨[], [], [], [], []⟩, source.program, ["gslt:inductive:"]⟩

theorem checked : library.check = true := by decide +kernel
theorem append_ready : library.headReady "gslt:inductive:append" = true := by decide +kernel
theorem length_ready : library.headReady "gslt:inductive:length" = true := by decide +kernel
theorem add_ready : library.headReady "gslt:inductive:add" = true := by decide +kernel

def appendCall (left right : Atom) : Atom :=
  .expression [.symbol "gslt:inductive:append", left, right]

/-- Arbitrary payload atoms are retained, including repeated occurrences and
atoms that would be executable if used as code. -/
theorem append_returns (state : State) (left right : List Atom) :
    PureReturns library.runtime [] state (appendCall (.expression left) (.expression right))
      state (.expression (left ++ right)) := by
  apply library.call checked append_ready [] state state
    [.expression left, .expression right] [.expression left, .expression right]
    (.expression (left ++ right)) rfl
  · simp only [List.map_cons, List.map_nil, applySubst_nil]
  · change PureReturns library.runtime [("right", .expression right), ("left", .expression left)]
      state (.expression [.symbol "union-atom", .var "left", .var "right"])
      state (.expression (left ++ right))
    apply native_variable_call_returns library.runtime _ state state "union-atom"
      ["left", "right"] (.expression (left ++ right)) (by decide +kernel) (by decide +kernel)
    · simp [applySubst, Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]
    · decide +kernel

theorem length_returns (state : State) (values : List Atom) :
    PureReturns library.runtime [] state
      (.expression [.symbol "gslt:inductive:length", .expression values])
      state (.grounded (.int values.length)) := by
  apply library.call checked length_ready [] state state
    [.expression values] [.expression values] (.grounded (.int values.length)) rfl
  · simp only [List.map_cons, List.map_nil, applySubst_nil]
  · change PureReturns library.runtime [("values", .expression values)] state
      (.expression [.symbol "size-atom", .var "values"]) state (.grounded (.int values.length))
    apply native_variable_call_returns library.runtime _ state state "size-atom"
      ["values"] (.grounded (.int values.length)) (by decide +kernel) (by decide +kernel)
    · simp [applySubst, Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]
    · decide +kernel

theorem add_returns (state : State) (left right : Int) :
    PureReturns library.runtime [] state
      (.expression [.symbol "gslt:inductive:add", .grounded (.int left), .grounded (.int right)])
      state (.grounded (.int (left + right))) := by
  apply library.call checked add_ready [] state state
    [.grounded (.int left), .grounded (.int right)]
    [.grounded (.int left), .grounded (.int right)] (.grounded (.int (left + right))) rfl
  · simp only [List.map_cons, List.map_nil, applySubst_nil]
  · change PureReturns library.runtime [("right", .grounded (.int right)), ("left", .grounded (.int left))]
      state (.expression [.symbol "+", .var "left", .var "right"])
      state (.grounded (.int (left + right)))
    apply native_variable_call_returns library.runtime _ state state "+"
      ["left", "right"] (.grounded (.int (left + right))) (by decide +kernel) (by decide +kernel)
    · simp [applySubst, Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]
    · decide +kernel

/-- Completed execution contains exactly one ordered array result. It does
not add answers, lose duplicates, change the store or produce I/O. -/
theorem append_completed_iff (before after : State) (left right answers input output : List Atom) :
    (∃ fuel, run library.runtime fuel
      { state := before, control := .evaluate [] (appendCall (.expression left) (.expression right)) } =
        .complete after answers input output) ↔
      after = before ∧ answers = [.expression (left ++ right)] ∧ input = [] ∧ output = [] :=
  path_completed_iff library.runtime _ before [.expression (left ++ right)] [] []
    (append_returns before left right) after answers input output

theorem append_captured_returns (state : State) (caller : Subst) (left right : Atom)
    (leftValues rightValues : List Atom)
    (leftCaptured : applySubst caller left = .expression leftValues)
    (rightCaptured : applySubst caller right = .expression rightValues) :
    PureReturns library.runtime caller state (appendCall left right)
      state (.expression (leftValues ++ rightValues)) := by
  apply library.capture checked append_ready caller state state [left, right]
    [.expression leftValues, .expression rightValues] (.expression (leftValues ++ rightValues)) rfl
  · simp only [List.map_cons, List.map_nil, leftCaptured, rightCaptured]
  · exact append_returns state leftValues rightValues

/-- Values already captured in a caller remain values when the first result
is reused. The fresh local binder cannot capture variables inside payloads. -/
theorem append_sequenced_returns (state : State) (left middle right : List Atom) :
    PureReturns library.runtime
      [("right", .expression right), ("middle", .expression middle), ("left", .expression left)] state
      (.expression [.symbol "let", .var "joined", appendCall (.var "left") (.var "middle"),
        appendCall (.var "joined") (.var "right")]) state (.expression ((left ++ middle) ++ right)) := by
  apply pure_let_returns library.runtime _ state "joined" _ (.expression (left ++ middle))
  · rfl
  · apply append_captured_returns <;> rfl
  · apply append_captured_returns <;> rfl

/-- Array execution and the independent source append have the same complete
payload. The source equivalence supplies the dependent sum index. -/
theorem source_append_returns (state : State) {n m : Natural.Carrier}
    (left : Vectors.Vector Atom n) (right : Vectors.Vector Atom m) :
    PureReturns library.runtime [] state
      (appendCall (.expression (VectorArray.encode left).val.toList)
        (.expression (VectorArray.encode right).val.toList)) state
      (.expression (VectorArray.encode (Vectors.append left right)).val.toList) := by
  rw [VectorArray.encode_append]
  simpa only [VectorArray.append, Array.toList_append] using
    append_returns state (VectorArray.encode left).val.toList (VectorArray.encode right).val.toList

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies

/-- Specialization is selected only after independent typed replay and exact
comparison with the supported core operations. This does not assert the
source producer's correctness for arbitrary modules. -/
def supports (input : ModuleSource.Module) : Bool :=
  AppendSource.checkProposal .declaredNullary input &&
    match AppendSource.propose .declaredNullary input with
    | none => false
    | some proposed => decide (proposed.appendFunction = Programs.appendTerm) &&
        decide (proposed.addition = Programs.add (.var 1) (.var 0))

def emit? (input : ModuleSource.Module) : Option String :=
  if supports input then some source.text else none

theorem supports_core (input : ModuleSource.Module) (accepted : supports input = true) :
    ∃ proposed, AppendSource.propose .declaredNullary input = some proposed ∧
      proposed.appendFunction = Programs.appendTerm ∧
      proposed.addition = Programs.add (.var 1) (.var 0) ∧
      FormationSensitive.Judgment Programs.rules .nil proposed.appendFunction Programs.appendType := by
  simp only [supports, Bool.and_eq_true] at accepted
  obtain ⟨typed, exactCore⟩ := accepted
  obtain ⟨proposed, found, judgment⟩ := AppendSource.checkProposal_sound _ input typed
  simp only [found, Bool.and_eq_true, decide_eq_true_eq] at exactCore
  exact ⟨proposed, found, exactCore.1, exactCore.2, judgment⟩

theorem emitted_source (input : ModuleSource.Module) (text : String)
    (emitted : emit? input = some text) : supports input = true ∧ text = source.text := by
  unfold emit? at emitted
  split at emitted
  · exact ⟨by assumption, (Option.some.inj emitted).symm⟩
  · cases emitted

theorem actual_supported : supports AppendSource.IndexedNatVecAppend.module = true := by
  decide +kernel

theorem actual_emitted : emit? AppendSource.IndexedNatVecAppend.module = some source.text := by
  simp [emit?, actual_supported]

/-- The actual textual program, its typed guest evaluation, and the emitted
array execution agree on complete ordered payloads. The endpoints use the
natural-only checking policy; the guest path uses the original operational rules;
the shared PeTTa machine additionally has the exact completed-packet theorem. -/
theorem actual_program_contract (state : State) {A : Type} (element : Tower.Tm 0)
    (payload : A → Tower.Tm 0) (runtimePayload : A → Atom)
    (elementTyped : Guest.AppendTyping.Selected.Typed .nil element (sortTm elementLevel))
    (payloadTyped : ∀ value, Guest.AppendTyping.Selected.Typed .nil (payload value) element)
    (left right : Array A) :
    emit? AppendSource.IndexedNatVecAppend.module = some source.text ∧
    Guest.AppendMeaning.ProgramExecutes
      (Declaration.IndexedFamily.applyArgs Programs.appendTerm
        [element, Guest.VectorMeaning.numeral left.size, Guest.VectorMeaning.numeral right.size,
          VectorArray.quoteArray element payload left, VectorArray.quoteArray element payload right])
      (VectorArray.quoteArray element payload (left ++ right)) ∧
    FormationSensitive.Judgment Guest.AppendTyping.Selected.rules .nil
      (VectorArray.quoteArray element payload (left ++ right))
      (vecApp element (Programs.add (Guest.VectorMeaning.numeral left.size)
        (Guest.VectorMeaning.numeral right.size))) ∧
    PureReturns library.runtime [] state
      (appendCall (.expression (left.toList.map runtimePayload))
        (.expression (right.toList.map runtimePayload)))
      state (.expression ((left ++ right).toList.map runtimePayload)) := by
  have guest := VectorArray.compiled_selected_contract Programs.appendTerm AppendSource.append_matches_reference
    element payload elementTyped payloadTyped left right
  exact ⟨actual_emitted, guest.2.1, guest.2.2,
    by simpa only [Array.toList_append, List.map_append] using
      append_returns state (left.toList.map runtimePayload) (right.toList.map runtimePayload)⟩

/-- A faithful payload representation makes the complete array observation
faithful. Length agreement without this condition cannot recover payloads. -/
theorem array_observation_injective {A : Type} (runtimePayload : A → Atom)
    (faithful : Function.Injective runtimePayload) :
    Function.Injective (fun values : Array A => Atom.expression (values.toList.map runtimePayload)) := by
  intro left right same
  apply Array.toList_inj.mp
  exact (List.map_injective_iff.mpr faithful) (Atom.expression.inj same)

theorem natural_add_returns (state : State) (left right : Natural.Carrier) :
    PureReturns library.runtime [] state
      (.expression [.symbol "gslt:inductive:add",
        .grounded (.int (Natural.toNat left)), .grounded (.int (Natural.toNat right))])
      state (.grounded (.int (Natural.toNat (Natural.add left right)))) := by
  simpa only [Natural.toNat_add, Nat.cast_add] using
    add_returns state (Natural.toNat left) (Natural.toNat right)

#print axioms append_completed_iff
#print axioms append_sequenced_returns
#print axioms supports_core
#print axioms actual_program_contract

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppend
