import Mettapedia.OSLF.Syntax.RhoIntrinsicReadbackParallel

/-!
# Constructor readouts on actual sorted rho classes

The independent raw input and output constructors descend to the authored
equation quotient. Optional constructor readouts retain their complete children.
The quote/drop normalization is justified by the actual name eta equation;
no process beta equation is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoIntrinsicReadback

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

def outputClass {context : Ctx sig} (name : Name context) (payload : Process context) :
    Process context :=
  Quotient.map₂ outputRaw (fun first first' equation second second' equation' => by
    change EqClosure rhoSourceE first first' at equation
    change EqClosure rhoSourceE second second' at equation'
    exact EqClosure.cong (S := sig) (E := rhoSourceE) Op.out
      (.cons (bs := []) equation (.cons (bs := []) equation' .nil))) name payload

def inputClass {context : Ctx sig} (name : Name context)
    (body : Process (Srt.nm :: context)) : Process context :=
  Quotient.map₂ inputRaw (fun first first' equation second second' equation' => by
    change EqClosure rhoSourceE first first' at equation
    change EqClosure rhoSourceE second second' at equation'
    exact EqClosure.cong (S := sig) (E := rhoSourceE) Op.inp
      (.cons (bs := []) equation
        (EqArgs.cons (S := sig) (E := rhoSourceE) (bs := [Srt.nm]) equation' .nil))) name body

def optionalPair {first second result : Type} (operation : first → second → result)
    (left : Option first) (right : Option second) : Option result :=
  left.bind fun firstValue => right.map (operation firstValue)

theorem outputClass_project {context : Ctx sig} (name : Term sig context Srt.nm)
    (payload : Term sig context Srt.pr) :
    outputClass (project name) (project payload) = project (outputRaw name payload) := rfl

theorem inputClass_project {context : Ctx sig} (name : Term sig context Srt.nm)
    (body : Term sig (Srt.nm :: context) Srt.pr) :
    inputClass (project name) (project body) = project (inputRaw name body) := rfl

theorem readNameClass_quote (context : Ctx sig) (process : Pattern) :
    readNameClass context (.apply "NQuote" [process]) =
      (readProcessClass context process).map quote := by
  cases readout : readProcess context process <;>
    simp [readNameClass, readProcessClass, readName, readout, quote_project]

theorem readProcessClass_drop (context : Ctx sig) (name : Pattern) :
    readProcessClass context (.apply "PDrop" [name]) =
      (readNameClass context name).map drop := by
  cases readout : readName context name <;>
    simp [readNameClass, readProcessClass, readProcess, readout, drop_project]

theorem readProcessClass_output (context : Ctx sig) (name payload : Pattern) :
    readProcessClass context (.apply "POutput" [name, payload]) =
      optionalPair outputClass (readNameClass context name) (readProcessClass context payload) := by
  cases nameRead : readName context name <;>
    cases payloadRead : readProcess context payload <;>
    simp [readNameClass, readProcessClass, readProcess, nameRead, payloadRead,
      optionalPair, outputClass_project]

theorem readProcessClass_input (context : Ctx sig) (name body : Pattern) :
    readProcessClass context (.apply "PInput" [name, .lambda none body]) =
      optionalPair inputClass (readNameClass context name)
        (readProcessClass (Srt.nm :: context) body) := by
  cases nameRead : readName context name <;>
    cases bodyRead : readProcess (Srt.nm :: context) body <;>
    simp [readNameClass, readProcessClass, readProcess, nameRead, bodyRead,
      optionalPair, inputClass_project]

theorem readNameClass_normalizeQuote (context : Ctx sig) (process : Pattern) :
    readNameClass context (normalizeQuote process) =
      (readProcessClass context process).map quote := by
  by_cases isDrop : ∃ name, process = .apply "PDrop" [name]
  · obtain ⟨name, rfl⟩ := isDrop
    change readNameClass context name =
      (readProcessClass context (.apply "PDrop" [name])).map quote
    rw [readProcessClass_drop]
    cases readNameClass context name <;> simp [quote_drop]
  · have unchanged : normalizeQuote process = .apply "NQuote" [process] := by
      unfold normalizeQuote
      split
      · exact (isDrop ⟨_, rfl⟩).elim
      · rfl
    rw [unchanged, readNameClass_quote]

end Mettapedia.OSLF.Binding.RhoIntrinsicReadback
