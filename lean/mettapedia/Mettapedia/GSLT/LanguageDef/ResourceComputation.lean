import Mettapedia.GSLT.LanguageDef.ResourceMachineBounds
import Mettapedia.GSLT.LanguageDef.ResourcePreorder

/-!
# Executed translations beyond polynomial clocks

The semantic translation is unchanged, but its execution may have any proved
per-packet bound. This accommodates computing elaborators whose fully written
output is not polynomially bounded. Every encoded packet terminates under this
interface; partial search remains in the separate successful-run interface.

Sequential composition executes the original machines and physical transfer.
Polynomial clocks recover the existing `OperationalTranslation`, with output
size derived from the actual writing work. Thus arbitrary computation and
polynomial simulation share their semantic and operational obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ResourceTranslation

open SemanticEvidence HeterogeneousTheory ProofSystems Turing
open Mettapedia.Computability

structure ExecutedTranslation {SK TK Γ Δ : Type} [Fintype Γ] [Fintype Δ]
    {S : TheoryFamily SK} {T : TheoryFamily TK}
    (SA : AuthorityContract S) (TA : AuthorityContract T)
    (sourceEncoding : Computability.Encoding (Packet SA) Γ)
    (targetEncoding : Computability.Encoding (Packet TA) Δ)
    extends Translation SA TA, TM2ComputableAux Γ Δ where
  time : Packet SA → Nat
  outputs : ∀ packet, TM2OutputsInTime tm
    ((sourceEncoding.encode packet).map inputAlphabet.symm)
    (some ((targetEncoding.encode (toTranslation.packet packet)).map outputAlphabet.symm))
    (time packet)
  finiteAlphabet : ∀ key, Finite (tm.Γ key)

namespace ExecutedTranslation

variable {SK MK TK Γ Δ Ε : Type} [Fintype Γ] [Fintype Δ] [Fintype Ε]
    {S : TheoryFamily SK} {M : TheoryFamily MK} {T : TheoryFamily TK}
    {SA : AuthorityContract S} {MA : AuthorityContract M} {TA : AuthorityContract T}
    {se : Computability.Encoding (Packet SA) Γ}
    {me : Computability.Encoding (Packet MA) Δ}
    {te : Computability.Encoding (Packet TA) Ε}

def ofPolynomial (translation : OperationalTranslation SA TA se te) :
    ExecutedTranslation SA TA se te where
  toTranslation := translation.toTranslation
  toTM2ComputableAux := translation.realization.toTM2ComputableAux
  time packet := translation.realization.time.eval (se.encode packet).length
  outputs := translation.execution
  finiteAlphabet := translation.finiteAlphabet

theorem clock_positive (translation : ExecutedTranslation SA TA se te) (packet : Packet SA) :
    0 < translation.time packet := OperationalPSimulation.outputs_positive (translation.outputs packet)

set_option backward.isDefEq.respectTransparency false in
/-- No size hypothesis is needed to compose arbitrary executed clocks: the
clock explicitly includes the full intermediate packet. -/
noncomputable def comp [Inhabited Δ]
    (first : ExecutedTranslation SA MA se me)
    (second : ExecutedTranslation MA TA me te) : ExecutedTranslation SA TA se te := by
  letI : Fintype (first.tm.Γ first.tm.k₁) := Fintype.ofEquiv Δ first.outputAlphabet.symm
  letI : Inhabited (first.tm.Γ first.tm.k₁) := ⟨first.outputAlphabet.symm default⟩
  let bridge := first.outputAlphabet.trans second.inputAlphabet.symm
  refine
    { toTranslation := first.toTranslation.comp second.toTranslation
      tm := StackMachineComposition.machine first.tm second.tm bridge
      inputAlphabet := first.inputAlphabet
      outputAlphabet := second.outputAlphabet
      time := fun packet => first.time packet +
        2 * (me.encode (first.packet packet)).length + 2 + second.time (first.packet packet)
      outputs := ?_
      finiteAlphabet := ?_ }
  · intro packet
    have latter := second.outputs (first.packet packet)
    have handoff : ((me.encode (first.packet packet)).map first.outputAlphabet.symm).map bridge =
        (me.encode (first.packet packet)).map second.inputAlphabet.symm := by
      simp [bridge, List.map_map, Function.comp_def]
    rw [← handoff] at latter
    have joined := StackMachineComposition.outputs first.tm second.tm bridge
      ((se.encode packet).map first.inputAlphabet.symm)
      ((me.encode (first.packet packet)).map first.outputAlphabet.symm)
      ((te.encode (second.packet (first.packet packet))).map second.outputAlphabet.symm)
      _ _ (first.outputs packet) latter
    convert joined using 1 <;> first | rfl | simp only [List.length_map]
  · intro key
    change Finite (StackMachineComposition.Alphabet first.tm second.tm key)
    cases key with
    | none => exact first.finiteAlphabet _
    | some key => cases key with
      | inl key => exact first.finiteAlphabet key
      | inr key => exact second.finiteAlphabet key

theorem comp_exact [Inhabited Δ]
    (first : ExecutedTranslation SA MA se me) (second : ExecutedTranslation MA TA me te)
    (firstExact : first.toTranslation.Exact) (secondExact : second.toTranslation.Exact) :
    (first.comp second).toTranslation.Exact := firstExact.comp secondExact

theorem output_length_le (translation : ExecutedTranslation SA TA se te)
    (packet : Packet SA) :
    (te.encode (translation.packet packet)).length ≤ (se.encode packet).length +
      StackMachineSpaceGrowth.machinePushBound translation.tm * translation.time packet := by
  simpa only [List.length_map] using
    StackMachineSpaceGrowth.output_length_le translation.tm (translation.outputs packet)

def peak (translation : ExecutedTranslation SA TA se te) (packet : Packet SA) : Nat :=
  StackMachineMicroSpace.runPeak translation.tm (translation.outputs packet)

theorem peak_le (translation : ExecutedTranslation SA TA se te) (packet : Packet SA) :
    translation.peak packet ≤ (se.encode packet).length +
      StackMachineSpaceGrowth.machinePushBound translation.tm * translation.time packet := by
  simpa only [peak, List.length_map] using
    StackMachineMicroSpace.runPeak_le translation.tm (translation.outputs packet)

/-- A polynomial bound on this supplied executed clock. Failure of this
property alone is not a lower bound on the machine or on other algorithms. -/
def PolynomialTime (translation : ExecutedTranslation SA TA se te) : Prop :=
  PolyBoundedBy translation.time (fun packet => (se.encode packet).length)

theorem ofPolynomial_polynomial (translation : OperationalTranslation SA TA se te) :
    (ofPolynomial translation).PolynomialTime :=
  ⟨translation.realization.time, fun _ => le_rfl⟩

theorem output_polynomial (translation : ExecutedTranslation SA TA se te)
    (bounded : translation.PolynomialTime) :
    PolyBoundedBy (fun packet => (te.encode (translation.packet packet)).length)
      (fun packet => (se.encode packet).length) :=
  PolyBoundedBy.of_le translation.output_length_le
    ((PolyBoundedBy.refl _).add
      ((PolyBoundedBy.const (StackMachineSpaceGrowth.machinePushBound translation.tm) _).mul bounded))

/-- A proved polynomial clock qualifies the existing polynomial interface,
using the same original machine and semantic map. -/
noncomputable def toPolynomial (translation : ExecutedTranslation SA TA se te)
    (bounded : translation.PolynomialTime) : OperationalTranslation SA TA se te where
  toTranslation := translation.toTranslation
  outputBound := translation.output_polynomial bounded
  realization :=
    { toTM2ComputableAux := translation.toTM2ComputableAux
      time := bounded.choose
      outputsFun packet :=
        { steps := (translation.outputs packet).steps
          evals_in_steps := (translation.outputs packet).evals_in_steps
          steps_le_m := (translation.outputs packet).steps_le_m.trans (bounded.choose_spec packet) } }
  finiteAlphabet := translation.finiteAlphabet

theorem comp_polynomial [Inhabited Δ]
    (first : ExecutedTranslation SA MA se me) (second : ExecutedTranslation MA TA me te)
    (firstBound : first.PolynomialTime) (secondBound : second.PolynomialTime) :
    (first.comp second).PolynomialTime := by
  have written := first.output_polynomial firstBound
  exact ((firstBound.add ((PolyBoundedBy.const 2 _).mul written)).add
    (PolyBoundedBy.const 2 _)).add ((secondBound.comp first.packet).trans written)

/-- A superpolynomial expanded output precludes a polynomial clock for that
same output convention, without asserting a lower bound for decision alone. -/
theorem not_polynomial_of_output (translation : ExecutedTranslation SA TA se te)
    (unbounded : ¬ PolyBoundedBy (fun packet => (te.encode (translation.packet packet)).length)
      (fun packet => (se.encode packet).length)) : ¬ translation.PolynomialTime :=
  fun bounded => unbounded (translation.output_polynomial bounded)

set_option backward.isDefEq.respectTransparency false in
/-- Computing elaboration can still be followed by an exact explicit checker.
Its entire execution cost remains visible, without a polynomial assertion. -/
noncomputable def thenCheck [Inhabited Ε]
    (translation : ExecutedTranslation SA TA se te)
    (exactReplay : translation.toTranslation.Exact)
    (checker : CheckerExecution TA te) : CheckerExecution SA se := by
  letI : Fintype (translation.tm.Γ translation.tm.k₁) :=
    Fintype.ofEquiv Ε translation.outputAlphabet.symm
  letI : Inhabited (translation.tm.Γ translation.tm.k₁) := ⟨translation.outputAlphabet.symm default⟩
  let bridge := translation.outputAlphabet.trans checker.inputAlphabet.symm
  refine
    { tm := StackMachineComposition.machine translation.tm checker.tm bridge
      inputAlphabet := translation.inputAlphabet
      outputAlphabet := checker.outputAlphabet
      time := fun packet => translation.time packet +
        2 * (te.encode (translation.packet packet)).length + 2 + checker.time (translation.packet packet)
      outputs := ?_
      finiteAlphabet := ?_ }
  · intro packet
    have checked := checker.outputs (translation.packet packet)
    have handoff : ((te.encode (translation.packet packet)).map translation.outputAlphabet.symm).map
        bridge = (te.encode (translation.packet packet)).map checker.inputAlphabet.symm := by
      simp [bridge, List.map_map, Function.comp_def]
    rw [← handoff] at checked
    have joined := StackMachineComposition.outputs translation.tm checker.tm bridge
      ((se.encode packet).map translation.inputAlphabet.symm)
      ((te.encode (translation.packet packet)).map translation.outputAlphabet.symm)
      ([checkPacket TA (translation.packet packet)].map checker.outputAlphabet.symm)
      _ _ (translation.outputs packet) checked
    rw [exactReplay packet] at joined
    convert joined using 1 <;> first | rfl | simp only [List.length_map]
  · intro key
    change Finite (StackMachineComposition.Alphabet translation.tm checker.tm key)
    cases key with
    | none => exact translation.finiteAlphabet _
    | some key => cases key with
      | inl key => exact translation.finiteAlphabet key
      | inr key => exact checker.finiteAlphabet key

theorem thenCheck_polynomial [Inhabited Ε]
    (translation : ExecutedTranslation SA TA se te)
    (exactReplay : translation.toTranslation.Exact) (checker : CheckerExecution TA te)
    (translationBound : translation.PolynomialTime)
    (checkerBound : PolyBoundedBy checker.time (fun packet => (te.encode packet).length)) :
    PolyBoundedBy (translation.thenCheck exactReplay checker).time
      (fun packet => (se.encode packet).length) := by
  have written := translation.output_polynomial translationBound
  exact ((translationBound.add ((PolyBoundedBy.const 2 _).mul written)).add
    (PolyBoundedBy.const 2 _)).add ((checkerBound.comp translation.packet).trans written)

end ExecutedTranslation

/-- The same replay/reflection policy applies to general executed routes. -/
def CanExecute (policy : ComparisonPolicy) (source target : EncodedAuthority) : Prop :=
  ∃ translation : ExecutedTranslation source.authority target.authority source.encoding target.encoding,
    (policy.exactReplay = true → translation.toTranslation.Exact) ∧
    (policy.reflectScope = true → translation.toTranslation.toTheoryTranslation.ScopeReflecting)

theorem canTranslate_canExecute {policy : ComparisonPolicy} {source target : EncodedAuthority}
    (polynomial : CanTranslate policy source target) : CanExecute policy source target := by
  obtain ⟨translation, exactReplay, reflects⟩ := polynomial
  exact ⟨ExecutedTranslation.ofPolynomial translation, exactReplay, reflects⟩

theorem canExecute_refl (policy : ComparisonPolicy) (source : EncodedAuthority) :
    CanExecute policy source source := canTranslate_canExecute (canTranslate_refl policy source)

theorem canExecute_trans (policy : ComparisonPolicy) {source middle target : EncodedAuthority}
    (first : CanExecute policy source middle) (second : CanExecute policy middle target) :
    CanExecute policy source target := by
  obtain ⟨first, firstExact, firstReflects⟩ := first
  obtain ⟨second, secondExact, secondReflects⟩ := second
  refine ⟨first.comp second, ?_, ?_⟩
  · intro required
    exact ExecutedTranslation.comp_exact first second (firstExact required) (secondExact required)
  · intro required kind claim proof
    exact firstReflects required kind claim
      (secondReflects required (first.mapKind kind) (first.mapClaim kind claim) proof)

/-- This order forgets polynomial efficiency, but retains finite machines,
termination on encoded packets, and the selected semantic/replay policy. -/
abbrev executionPreorder (policy : ComparisonPolicy) : Preorder EncodedAuthority where
  le := CanExecute policy
  le_refl := canExecute_refl policy
  le_trans := fun _ _ _ => canExecute_trans policy

end Mettapedia.GSLT.LanguageDef.ResourceTranslation
