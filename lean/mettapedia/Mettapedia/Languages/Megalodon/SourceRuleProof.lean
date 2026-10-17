import Mettapedia.Languages.Megalodon.SourceProofInvariant
import Mettapedia.Languages.Megalodon.BudgetIndependent

/-!
# Reconstructing protected source proofs from local rows

Reconstruction uses the actual operand witness checked at each row. Merely
knowing that some local rule exists would lose the source-payload invariant.
The reconstructed proof is logical evidence, not a requirement to materialize
an expanded proof tree in the native runtime.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SourceCursor
open MathdataKernel ProofJudgment BorrowedProofCursor SourceScopeInvariant

def WitnessSafe : Witness → Prop
  | .termApp argument _ body => Protected argument ∧ Protected body
  | .proofApp domain => Protected domain
  | .proofLam source => Protected source
  | .typeApp _ body => Protected body
  | _ => True

instance witnessSafeDecidable (witness : Witness) : Decidable (WitnessSafe witness) := by
  cases witness <;> unfold WitnessSafe <;> infer_instance

theorem proof_mono {environment : Environment} {first second : Nat} {context : Context}
    {proof : Pf} {proposition : Tm} (increased : first ≤ second)
    (derived : Proves environment first context proof proposition) :
    Proves environment second context proof proposition := by
  induction derived with
  | hyp found => exact .hyp found
  | known found normalized =>
      exact .known found (FuelledConversionProfile.normalize_mono _ _ _ increased normalized)
  | termApp _ typed expanded normalized ih =>
      exact .termApp ih typed (BudgetIndependent.delta_mono _ _ _ increased expanded)
        (FuelledConversionProfile.normalize_mono _ _ _ increased normalized)
  | proofApp _ _ ihf iha => exact .proofApp ihf iha
  | termLam formed _ ih => exact .termLam formed ih
  | proofLam typed normalized _ ih =>
      exact .proofLam typed (FuelledConversionProfile.normalize_mono _ _ _ increased normalized) ih
  | typeApp _ ih => exact .typeApp ih
  | typeLam terms hypotheses _ ih => exact .typeLam terms hypotheses ih

def Supported (environment : Environment) (judgment : Judgment) : Prop :=
  ∃ fuel proof, ProofPayload proof ∧ Proves environment fuel judgment.context proof judgment.proposition

private theorem common_bound (environment : Environment) (premises : List Judgment)
    (supported : ∀ premise ∈ premises, Supported environment premise) :
    ∃ fuel, ∀ premise ∈ premises, ∃ proof, ProofPayload proof ∧
      Proves environment fuel premise.context proof premise.proposition := by
  induction premises with
  | nil => exact ⟨0, by simp⟩
  | cons first rest ih =>
      obtain ⟨firstFuel, firstProof, firstPayload, firstDerived⟩ := supported first (by simp)
      obtain ⟨restFuel, restProofs⟩ := ih (fun premise member => supported premise (by simp [member]))
      refine ⟨max firstFuel restFuel, ?_⟩
      intro premise member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨firstProof, firstPayload, proof_mono (Nat.le_max_left _ _) firstDerived⟩
      · obtain ⟨proof, payload, derived⟩ := restProofs premise later
        exact ⟨proof, payload, proof_mono (Nat.le_max_right _ _) derived⟩

theorem requirements_proof {environment : Environment} {fuel bound : Nat} {witness : Witness}
    {conclusion : Judgment} {premises : List Judgment} (increased : fuel ≤ bound)
    (safe : WitnessSafe witness)
    (accepted : requirements environment fuel witness conclusion = some premises)
    (parents : ∀ premise ∈ premises, ∃ proof, ProofPayload proof ∧
      Proves environment bound premise.context proof premise.proposition) :
    ∃ proof, ProofPayload proof ∧ Proves environment bound conclusion.context proof conclusion.proposition := by
  rcases conclusion with ⟨context, proposition⟩
  cases witness with
  | hyp index =>
      simp only [requirements] at accepted
      split at accepted
      · rename_i found
        exact ⟨.hyp index, trivial, .hyp found⟩
      · contradiction
  | known name =>
      cases found : environment.lookupKnown? name with
      | none => simp [requirements, found] at accepted
      | some source =>
          cases normalized : normalize environment fuel source with
          | none => simp [requirements, found, normalized] at accepted
          | some result =>
              by_cases same : result = proposition
              · subst result
                exact ⟨.known name, trivial, .known found
                  (FuelledConversionProfile.normalize_mono _ _ _ increased normalized)⟩
              · simp [requirements, found, normalized, same] at accepted
  | termApp argument domain body =>
      by_cases typed : inferTerm environment context.typeDepth context.terms argument = some domain
      · cases unfolded : deltaNormalize environment fuel argument with
        | none => simp [requirements, typed, unfolded] at accepted
        | some normalized =>
            cases result : normalize environment fuel (Tm.instantiate normalized body) with
            | none => simp [requirements, typed, unfolded, result] at accepted
            | some actual =>
                by_cases same : actual = proposition
                · subst actual
                  have shape : premises = [⟨context, .all domain body⟩] := by
                    simpa [requirements, typed, unfolded, result] using accepted.symm
                  subst premises
                  obtain ⟨proof, payload, derived⟩ := parents ⟨context, .all domain body⟩ (by simp)
                  exact ⟨.termApp proof argument, ⟨payload, safe.1⟩,
                    .termApp derived typed (BudgetIndependent.delta_mono _ _ _ increased unfolded)
                      (FuelledConversionProfile.normalize_mono _ _ _ increased result)⟩
                · simp [requirements, typed, unfolded, result, same] at accepted
      · simp [requirements, typed] at accepted
  | proofApp domain =>
      cases Option.some.inj accepted
      obtain ⟨function, functionPayload, functionProof⟩ := parents ⟨context, .imp domain proposition⟩ (by simp)
      obtain ⟨argument, argumentPayload, argumentProof⟩ := parents ⟨context, domain⟩ (by simp)
      exact ⟨.proofApp function argument, ⟨functionPayload, argumentPayload⟩, .proofApp functionProof argumentProof⟩
  | termLam =>
      cases proposition <;> simp only [requirements] at accepted
      all_goals try contradiction
      rename_i type body
      split at accepted
      · rename_i formed
        cases Option.some.inj accepted
        obtain ⟨proof, payload, derived⟩ := parents ⟨context.termBinder type, body⟩ (by simp)
        exact ⟨.termLam type proof, payload, .termLam formed derived⟩
      · contradiction
  | proofLam source =>
      cases proposition <;> simp only [requirements] at accepted
      all_goals try contradiction
      rename_i domain body
      split at accepted
      · rename_i checked
        cases Option.some.inj accepted
        obtain ⟨proof, payload, derived⟩ := parents ⟨context.proofBinder domain, body⟩ (by simp)
        exact ⟨.proofLam source proof, ⟨safe, payload⟩, .proofLam checked.1
          (FuelledConversionProfile.normalize_mono _ _ _ increased checked.2) derived⟩
      · contradiction
  | typeApp type body =>
      simp only [requirements] at accepted
      split at accepted
      · rename_i same
        cases Option.some.inj accepted
        subst proposition
        obtain ⟨proof, payload, derived⟩ := parents ⟨context, .typeAll body⟩ (by simp)
        exact ⟨.typeApp proof type, payload, .typeApp derived⟩
      · contradiction
  | typeLam =>
      cases proposition <;> simp only [requirements] at accepted
      all_goals try contradiction
      rename_i body
      split at accepted
      · rename_i empty
        cases Option.some.inj accepted
        obtain ⟨proof, payload, derived⟩ := parents ⟨context.typeBinder, body⟩ (by simp)
        exact ⟨.typeLam proof, payload, .typeLam empty.1 empty.2 derived⟩
      · contradiction

theorem requirements_supported {environment : Environment} {fuel : Nat} {witness : Witness}
    {conclusion : Judgment} {premises : List Judgment} (safe : WitnessSafe witness)
    (accepted : requirements environment fuel witness conclusion = some premises)
    (parents : ∀ premise ∈ premises, Supported environment premise) : Supported environment conclusion := by
  obtain ⟨parentFuel, parentProofs⟩ := common_bound environment premises parents
  obtain ⟨proof, payload, derived⟩ := requirements_proof (bound := max fuel parentFuel)
    (Nat.le_max_left _ _) safe accepted (by
      intro premise member
      obtain ⟨proof, payload, derived⟩ := parentProofs premise member
      exact ⟨proof, payload, proof_mono (Nat.le_max_right _ _) derived⟩)
  exact ⟨max fuel parentFuel, proof, payload, derived⟩

end Mettapedia.Languages.Megalodon.SourceCursor
