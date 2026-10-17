import Mettapedia.Logic.ProofSearch.SearchTransport
import Mettapedia.GSLT.LanguageDef.ResourceExecutionControls

/-!
# Nonidentity executed search-transport controls

The existing source control theory proves `true`; this independently specified
target theory proves `false`. Boolean negation maps the claims and a real
two-pass symbol-mapping machine implements the packet translation. The producer
retains a submitted candidate. Both accepted and refused source packets execute
the same producer, physical handoff and compiler; only accepted packets inhabit
the successful-search stage.

This is a control for packet transport, not a discovery algorithm for a larger
logic or an instance of shortest-proof automatizability.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ProofSearch.SearchTransport.Controls

open Mettapedia.GSLT.LanguageDef
open SemanticEvidence HeterogeneousTheory ResourceTranslation ProofSystems
open Turing Polynomial

def flippedTheory : TheoryFamily Unit where
  Signature := Unit
  signatureOf _ := ()
  Claim _ := Bool
  Scope _ b := b = false
  Meaning _ b := b = false
  scope_sound _ _ h := h

def flippedAuthority : AuthorityContract flippedTheory where
  Certificate _ := Unit
  checker _ := ⟨fun (b : Bool) (_ : Unit) => !b⟩
  scopeAuthority _ :=
    { sound := by intro b _ accepted; cases b <;> simp_all [flippedTheory]
      complete := by intro b h; exact ⟨(), by cases b <;> simp_all [flippedTheory]⟩ }

def flippedPacket (b : Bool) : Packet flippedAuthority := ⟨(), b, ()⟩

def flippedEncoding : Computability.Encoding (Packet flippedAuthority) Bool where
  encode packet := [packet.2.1]
  decode
    | [b] => some (flippedPacket b)
    | _ => none
  decode_encode := by rintro ⟨⟨⟩, b, ⟨⟩⟩; rfl

def flipTranslation : Translation ExecutionControls.authority flippedAuthority where
  mapKind := id
  mapSignature := id
  signature_commutes _ := rfl
  mapClaim _ b := !b
  scope_preserved _ b h := by cases b <;> simp_all [ExecutionControls.theory, flippedTheory]
  meaning_preserved _ b h := by cases b <;> simp_all [ExecutionControls.theory, flippedTheory]
  translate _ _ _ := ()
  preserves _ b _ h := by cases b <;> simp_all [ExecutionControls.authority, flippedAuthority]

theorem flipTranslation_exact : flipTranslation.Exact := by
  rintro ⟨⟨⟩, b, ⟨⟩⟩
  cases b <;> rfl

noncomputable def flipRealization : TM2ComputableInPolyTime ExecutionControls.encoding.encode
    flippedEncoding.encode flipTranslation.packet where
  tm := SymbolMapMachine.machine (! · : Bool → Bool)
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := C 2 * X + C 2
  outputsFun := by
    rintro ⟨⟨⟩, b, ⟨⟩⟩
    exact (SymbolMapMachine.computable (! · : Bool → Bool)).outputsFun [b]

/-- Every source packet, including refused candidates, executes bit negation. -/
noncomputable def flipCompiler : OperationalTranslation ExecutionControls.authority flippedAuthority
    ExecutionControls.encoding flippedEncoding where
  toTranslation := flipTranslation
  outputBound := ⟨C 1, by
    intro packet
    change 1 ≤ (C (1 : Nat)).eval _
    simp⟩
  realization := flipRealization
  finiteAlphabet _ := inferInstanceAs (Finite Bool)

/-- A submitted candidate is produced in one actual halting step. -/
def candidateProducer : FinTM2 := idComputer Bool

def candidateRun (b : Bool) : TM2OutputsInTime candidateProducer [b] (some [b]) 1 where
  steps := 1
  evals_in_steps := rfl
  steps_le_m := le_rfl

noncomputable def transportedProducer : FinTM2 :=
  followingMachine candidateProducer (Equiv.refl Bool) flipCompiler.realization

set_option backward.isDefEq.respectTransparency false in
noncomputable def transportedRun (b : Bool) :
    TM2OutputsInTime transportedProducer [b] (some [!b]) 9 := by
  have run := following_outputs candidateProducer (Equiv.refl Bool) flipCompiler.realization
    [b] (ExecutionControls.packet b) 1 (candidateRun b)
  have outputSame : (flippedEncoding.encode (flipCompiler.packet (ExecutionControls.packet b))).map
      flipCompiler.realization.outputAlphabet.symm = [!b] := rfl
  rw [outputSame] at run
  simpa [ExecutionControls.encoding, ExecutionControls.packet, flippedEncoding, flipCompiler,
    flipTranslation, flipRealization, transportedProducer, Translation.packet,
    HeterogeneousTheory.TheoryTranslation.identity, List.map_id_fun] using run

/-- Execute the original composition without evaluating its finiteness
witnesses as part of native transition extraction. -/
def transportedProgram :
    Mettapedia.Computability.StackMachineComposition.Programs.Labels Unit Bool →
      TM2.Stmt
        (Mettapedia.Computability.StackMachineComposition.Programs.Cells
          (FirstAlphabet := fun _ : Unit => Bool)
          (SecondAlphabet := fun _ : Bool => Bool) ())
        (Mettapedia.Computability.StackMachineComposition.Programs.Labels Unit Bool)
        (Mettapedia.Computability.StackMachineComposition.Programs.Registers
          (FirstState := Unit) (SecondState := Option Bool)
          (FirstAlphabet := fun _ : Unit => Bool) ()) :=
  Mettapedia.Computability.StackMachineComposition.Programs.body () false false false id
    (fun _ : Unit => .halt) (SymbolMapMachine.machine (! · : Bool → Bool)).m

set_option backward.isDefEq.respectTransparency false in
theorem transportedProgram_eq : transportedProgram = transportedProducer.m := by
  funext label
  cases label with
  | inl label => cases label; rfl
  | inr label => cases label with
    | inl phase => cases phase <;> rfl
    | inr phase => cases phase <;> rfl

theorem accepted_packet : checkPacket flippedAuthority
    (flipCompiler.packet (ExecutionControls.packet true)) = true := rfl

theorem refused_packet : checkPacket flippedAuthority
    (flipCompiler.packet (ExecutionControls.packet false)) = false := rfl

/-- An actual accepted source candidate inhabits the transported proof stage. -/
noncomputable def acceptedSearch :
    (successfulStage transportedProducer (Equiv.refl Bool) flippedEncoding).Evidence
      [true] (flippedPacket false) := by
  have evidence : (successfulStage candidateProducer (Equiv.refl Bool)
      ExecutionControls.encoding).Evidence [true] (ExecutionControls.packet true) :=
    ⟨(candidateRun true).toTM2Outputs, ⟨rfl⟩⟩
  exact forwardEvidence flipCompiler candidateProducer (Equiv.refl Bool) evidence

theorem accepted_search_scope : flippedTheory.Scope () false :=
  successfulStage_scope transportedProducer (Equiv.refl Bool) flippedEncoding acceptedSearch

/-- The refused candidate has a completed execution but cannot be called a
successful search. Rejection is not a fabricated checked proof. -/
theorem refused_search_isEmpty : IsEmpty
    ((successfulStage transportedProducer (Equiv.refl Bool) flippedEncoding).Evidence
      [false] (flippedPacket true)) := by
  refine ⟨fun evidence => ?_⟩
  have accepted := evidence.2.down
  change (!true) = true at accepted
  cases accepted

theorem executed_map_is_nonidentity : IsEmpty
    (TM2Outputs transportedProducer [true] (some [true])) := by
  refine ⟨fun run => ?_⟩
  have same := Mettapedia.Computability.StackMachineComposition.outputs_unique run
    (transportedRun true).toTM2Outputs
  cases same

end Mettapedia.Logic.ProofSearch.SearchTransport.Controls
