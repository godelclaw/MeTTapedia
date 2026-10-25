import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllResultComparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveDefinitionTables
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeJoins

/-!
# Checked definitions for Vector result projections and evidence maps

The four stored bodies are the original checked projection and universe-map
programs. Their types and bodies are checked before installing any new name.
The definition table adds only transparent delta unfolding. This assembly
supports compositional evidence production; erasure back into the base
profile remains a separate interpretation obligation.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultComparison.Named
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration
open NativeVectorAll.ResultView
abbrev base := NativeVectorAllResultComparison.rules

inductive Operation where
  | lowerResults
  | upperResults
  | raiseEvidence
  | lowerEvidence
  deriving DecidableEq, Repr

def operations : List Operation := [.lowerResults, .upperResults, .raiseEvidence, .lowerEvidence]

def name : Operation → DeclName
  | .lowerResults => `CumulativeTower.AllResults.lower
  | .upperResults => `CumulativeTower.AllResults.upper
  | .raiseEvidence => `CumulativeTower.AllEvidence.raise
  | .lowerEvidence => `CumulativeTower.AllEvidence.lower

def body : Operation → Tower.Tm 0
  | .lowerResults => NativeVectorAllCommonRecursorProfile.Projection.programme resultContainerLevel
  | .upperResults => NativeVectorAllCommonRecursorProfile.Projection.programme evidenceUpperLevel
  | .raiseEvidence => TelescopeAbstraction.closeTerm NativeVectorAll.Universes.context
      NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.forward
  | .lowerEvidence => TelescopeAbstraction.closeTerm NativeVectorAll.Universes.context
      NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.backward

def type : Operation → Tower.Tm 0
  | .lowerResults => NativeVectorAllCommonRecursorProfile.Projection.programmeType resultContainerLevel
  | .upperResults => NativeVectorAllCommonRecursorProfile.Projection.programmeType evidenceUpperLevel
  | .raiseEvidence => TelescopeAbstraction.closeType NativeVectorAll.Universes.context
      NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.forwardType
  | .lowerEvidence => TelescopeAbstraction.closeType NativeVectorAll.Universes.context
      NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.backwardType

theorem universe_regularity : FormationSensitive.UniverseRegularity base :=
  FormationSensitive.towerUniverseRegularity.includeSignature NativeVectorAllResultComparison.signature

private theorem closed_map {term displayed : Tower.Tm 4}
    (checked : FormationSensitive.Judgment base NativeVectorAll.Universes.context term displayed) :
    FormationSensitive.Judgment base .nil
      (TelescopeAbstraction.closeTerm NativeVectorAll.Universes.context term)
      (TelescopeAbstraction.closeType NativeVectorAll.Universes.context displayed) :=
  ⟨.nil, FormationCheckedTelescopePrograms.close_typed universe_regularity
    (fun first second => FormationCheckedTelescopePrograms.tower_joins first second)
      checked.context checked.typing⟩

theorem body_checked (operation : Operation) :
    FormationSensitive.Judgment base .nil (body operation) (type operation) := by
  cases operation with
  | lowerResults =>
    unfold body type
    rw [NativeVectorAllCommonRecursorProfile.Projection.lower_programme_readback,
      NativeVectorAllCommonRecursorProfile.Projection.lower_type_readback]
    exact lower_projection_formed
  | upperResults => exact upper_projection_formed
  | raiseEvidence =>
    exact closed_map (NativeVectorAllCommonRecursorProfile.forward_formed.monoSignature common_inclusion)
  | lowerEvidence =>
    exact closed_map (NativeVectorAllCommonRecursorProfile.backward_formed.monoSignature common_inclusion)

theorem type_formed (operation : Operation) : ∃ u, base.isUniverse u ∧
    FormationSensitive.Judgment base .nil (type operation) (.head u) :=
  (body_checked operation).regularity universe_regularity

theorem fresh (operation : Operation) : base.constantType (name operation) = none := by
  cases operation <;> decide +kernel

def entry (operation : Operation) : Entry Tower.Head := ⟨type operation, some (body operation)⟩
def declarations : List (DeclName × Entry Tower.Head) := operations.map fun operation => (name operation, entry operation)
def signature := Signature.ofList declarations
abbrev rules := extendRules base signature

theorem formed : signature.Formed base := by
  apply Signature.formed_of_base_judgments declarations
  · intro actual declared found
    obtain ⟨operation, _, selected⟩ := List.mem_map.mp found
    rcases Prod.mk.inj selected with ⟨rfl, rfl⟩
    exact fresh operation
  · intro actual declared found
    obtain ⟨operation, _, selected⟩ := List.mem_map.mp found
    rcases Prod.mk.inj selected with ⟨rfl, rfl⟩
    obtain ⟨u, isUniverse, checked⟩ := type_formed operation
    exact ⟨u, isUniverse, checked.typing⟩
  · intro actual declared found value selectedValue
    obtain ⟨operation, _, selected⟩ := List.mem_map.mp found
    rcases Prod.mk.inj selected with ⟨rfl, rfl⟩
    cases Option.some.inj selectedValue
    exact (body_checked operation).typing
  · intro actual declared found value selectedValue
    obtain ⟨operation, _, selected⟩ := List.mem_map.mp found
    rcases Prod.mk.inj selected with ⟨rfl, rfl⟩
    cases Option.some.inj selectedValue
    cases operation <;> intro impossible <;> cases impossible

theorem type_lookup (operation : Operation) : signature.typeOf? (name operation) = some (type operation) := by
  cases operation <;> rfl

theorem value_lookup (operation : Operation) : signature.valueOf? (name operation) = some (body operation) := by
  cases operation <;> rfl

theorem constant_known (operation : Operation) : rules.constantType (name operation) = some (type operation) :=
  combinedType_of_signature base signature (fresh operation) (type_lookup operation)

theorem constant_typed (operation : Operation) {n : Nat} (ambient : Tower.Ctx n) :
    FormationSensitive.Typing rules ambient (.const (name operation)) (liftClosed (type operation)) := by
  obtain ⟨u, isUniverse, checked⟩ := type_formed operation
  exact .const (constant_known operation) (checked.typing.includeSignature signature) isUniverse

theorem typed_unfolding (operation : Operation) {n : Nat} {ambient : Tower.Ctx n}
    {displayed : Tower.Tm n}
    (checked : FormationSensitive.Judgment rules ambient (.const (name operation)) displayed) :
    StepCore rules.computation rules.headEq (.const (name operation) : Tower.Tm n) (liftClosed (body operation)) ∧
      FormationSensitive.Judgment rules ambient (liftClosed (body operation)) displayed := by
  apply checked.delta (declared := type operation)
    (bodyTyped := (body_checked operation).typing.includeSignature signature)
  · exact value_lookup operation
  · exact constant_known operation

namespace Controls

theorem lower_unfolding :
    StepCore rules.computation rules.headEq (.const (name .lowerResults) : Tower.Tm 0)
      (liftClosed (body .lowerResults)) ∧
    FormationSensitive.Judgment rules .nil (liftClosed (body .lowerResults))
      (liftClosed (type .lowerResults)) :=
  typed_unfolding .lowerResults ⟨.nil, constant_typed .lowerResults .nil⟩

theorem upper_unfolding :
    StepCore rules.computation rules.headEq (.const (name .upperResults) : Tower.Tm 0)
      (liftClosed (body .upperResults)) ∧
    FormationSensitive.Judgment rules .nil (liftClosed (body .upperResults))
      (liftClosed (type .upperResults)) :=
  typed_unfolding .upperResults ⟨.nil, constant_typed .upperResults .nil⟩

end Controls

#print axioms formed
#print axioms body_checked
#print axioms constant_typed
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultComparison.Named
