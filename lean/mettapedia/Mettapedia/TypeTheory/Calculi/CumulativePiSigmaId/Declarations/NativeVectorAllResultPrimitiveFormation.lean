import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllResultDefinitions

/-!
# Refined primitive judgments in the shared Vector result profile

The seventeen primitive constant names are checked independently at their
actual declared types in the base profile. The checking judgments also earn
formation of those types. They do not assert completeness of a checker or
erasure of the transparent result definitions.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultComparison.Named.PrimitiveBase
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration
open NativeNaturalVectorFamilies
open NativeVectorAll.ResultView
abbrev base := Named.base
abbrev decoder := NativeVectorAllResultComparison.decoder
abbrev choices := NativeVectorAllResultComparison.choices

local instance : DecidableRel base.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred base.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (base.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel base.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel base.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def primitiveNames : List DeclName :=
  [natName, zeroName, succName, natEliminateName, vecName, vnilName, vconsName, vecEliminateName,
    OriginalInputUniverses.names vecName, OriginalInputUniverses.names vnilName,
    OriginalInputUniverses.names vconsName, OriginalInputUniverses.names vecEliminateName,
    NativeIndexedFamilies.Intrinsic.listName, NativeIndexedFamilies.Intrinsic.nilName,
    NativeIndexedFamilies.Intrinsic.consName, NativeIndexedFamilies.Intrinsic.eliminateName,
    NativeIndexedFamilies.Intrinsic.identityEliminateName]

def accepted (actual : DeclName) : Bool :=
  match base.constantType actual with
  | none => false
  | some declared => (FormationSensitiveElaboration.elaborate base decoder choices 128 .nil
      (.const actual) declared).isSome

set_option maxRecDepth 8192 in
theorem all_checked : primitiveNames.all accepted = true := by decide +kernel

theorem primitive_typed {actual : DeclName} (present : actual ∈ primitiveNames)
    {declared : Tower.Tm 0} (known : base.constantType actual = some declared) :
    FormationSensitive.Judgment base .nil (.const actual) declared := by
  have checked := (List.all_eq_true.mp all_checked) actual present
  simp only [accepted, known] at checked
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp checked
  exact FormationSensitiveElaboration.elaborate_sound base decoder choices 128 .nil _ _ submission produced

theorem primitive_type_formed {actual : DeclName} (present : actual ∈ primitiveNames)
    {declared : Tower.Tm 0} (known : base.constantType actual = some declared) :
    ∃ u, base.isUniverse u ∧ FormationSensitive.Judgment base .nil declared (.head u) :=
  (primitive_typed present known).regularity Named.universe_regularity

namespace Controls

theorem zero_typed : FormationSensitive.Judgment base .nil zeroTm natTm :=
  primitive_typed (by simp [primitiveNames]) rfl

theorem identity_type_formed : ∃ u, base.isUniverse u ∧
    FormationSensitive.Judgment base .nil NativeVectorIdentityComparison.identityType (.head u) :=
  primitive_type_formed (actual := NativeIndexedFamilies.Intrinsic.identityEliminateName)
    (by simp [primitiveNames]) rfl

end Controls

#print axioms all_checked
#print axioms primitive_typed
#print axioms primitive_type_formed
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultComparison.Named.PrimitiveBase
