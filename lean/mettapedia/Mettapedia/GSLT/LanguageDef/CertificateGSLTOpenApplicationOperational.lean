import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenApplication
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenSearchModalAdequacy

/-!
# Checked rule application and the existing operational proof machine

Application reconstructs the exact emitted proof; the original open-search
machine executes that proof with its ordered premise-use ledger. Its complete
event trace retains every rule instance and premise occurrence. The OSLF
closure diamond expresses existence of such a completion, not a proof-search
decision procedure or correctness of the C evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.Ultrainfinite
open OpenSearchMachine

mutual
  /-- A data view of the original machine's preorder events. -/
  def RawOpenProof.events : RawOpenProof → List (RuleInstance ⊕ Nat)
    | .premise index => [.inr index]
    | .node instantiation children => .inl instantiation :: RawOpenProof.childrenEvents children
  def RawOpenProof.childrenEvents : List RawOpenProof → List (RuleInstance ⊕ Nat)
    | [] => []
    | first :: rest => first.events ++ RawOpenProof.childrenEvents rest
end

def eventData {context : List Pattern} : Event context → RuleInstance ⊕ Nat
  | .rule instantiation => .inl instantiation
  | .assumption index => .inr index.val

mutual
  theorem events_eraseOpen {definition : ValidatedCalculusLanguageDef}
      {context : List Pattern} {goal : Pattern} (derivation : OpenDerivation definition context goal) :
      derivation.eraseOpen.events = (proofEvents derivation).map eventData := by
    cases derivation with
    | assumption index => rfl
    | byRule instantiation application children =>
        simp [OpenDerivation.eraseOpen, RawOpenProof.events, proofEvents, eventData,
          childrenEvents_eraseOpen children]

  theorem childrenEvents_eraseOpen {definition : ValidatedCalculusLanguageDef}
      {context goals : List Pattern} (derivations : OpenDerivationList definition context goals) :
      RawOpenProof.childrenEvents derivations.eraseOpen = (proofEventsList derivations).map eventData := by
    cases derivations with
    | nil => rfl
    | cons first rest =>
        simp [OpenDerivationList.eraseOpen, RawOpenProof.childrenEvents, proofEventsList,
          events_eraseOpen first, childrenEvents_eraseOpen rest]
end

/-- The submitted application yields a real complete machine route. Its
returned raw event list is exactly the route's event projection, and premise
use composes by ordered substitution, including repetitions. -/
theorem applyOpen?_operational {definition : ValidatedCalculusLanguageDef}
    {premises ambient : List Pattern} {goal : Pattern} {program result : RawOpenProof}
    {arguments : List RawOpenProof}
    (accepted : applyOpen? definition premises ambient goal program arguments = some result) :
    ∃ rule : OpenDerivation definition premises goal,
      ∃ supplied : OpenDerivationList definition ambient premises,
        rule.eraseOpen = program ∧ supplied.eraseOpen = arguments ∧
          (rule.bind supplied).eraseOpen = result ∧
          holeOccurrences (rule.bind supplied) =
            (holeOccurrences rule).flatMap (fun index => holeOccurrences (supplied.get index)) ∧
          (Route.trace eventOfStep (runToCompletion (rule.bind supplied))).map eventData = result.events := by
  obtain ⟨rule, supplied, re, se, output⟩ := applyOpen?_exact accepted
  refine ⟨rule, supplied, re, se, output, holeOccurrences_bind rule supplied, ?_⟩
  rw [trace_runToCompletion, ← events_eraseOpen, output]

/-- OSLF observes existence at the specified final ledger. The explicit
derivation witness retains the exact artifact; the modal proposition alone
does not choose or identify a particular proof tree. -/
theorem checked_ledger_iff_closureDiamond (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) (goal : Pattern) (ledger : List (Fin context.length)) :
    (∃ proof, checkOpenRaw definition context goal proof = true ∧
      ∃ derivation : OpenDerivation definition context goal,
        derivation.eraseOpen = proof ∧ holeOccurrences derivation = ledger) ↔
      Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond
        (OpenSearchModalAdequacy.theory definition context).closure
        (fun state => state = (⟨[], ledger⟩ : State context)) ⟨[goal], []⟩ := by
  rw [← OpenSearchModalAdequacy.exactDischarge_iff_closureDiamond]
  constructor
  · rintro ⟨_, _, derivation, _, same⟩
    exact ⟨⟨derivation, same⟩⟩
  · rintro ⟨⟨derivation, same⟩⟩
    exact ⟨derivation.eraseOpen, checkOpenRaw_erase derivation, derivation, rfl, same⟩

#print axioms applyOpen?_operational
#print axioms checked_ledger_iff_closureDiamond

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
