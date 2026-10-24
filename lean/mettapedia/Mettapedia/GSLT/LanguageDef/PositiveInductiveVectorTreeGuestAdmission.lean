import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest

/-!
# Generated declaration-prefix admission and opaque formation.

The producer, checker, source requests and proof limits are unchanged.
-/

set_option autoImplicit false
set_option Elab.async false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest

open Presentation Presentation.Declaration
open Presentation.Declaration.ComputationAuthority
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

local instance : DecidableRel baseRules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred baseRules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (baseRules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel baseRules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel baseRules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

/-- Check each actual source prefix once, then reconstruct the unchanged
whole-inventory acceptance result through proved checker composition. -/
private theorem answerDeclarationAccepted :
    (IndexedInductive.Guest.Declarations.elaborate baseRules baseDecoder declarationChoices
      256 (entries.take 0) ((entries.drop 0).take 1)).isSome = true := by
  decide +kernel

private theorem familyDeclarationAccepted :
    (IndexedInductive.Guest.Declarations.elaborate baseRules baseDecoder declarationChoices
      256 (entries.take 1) ((entries.drop 1).take 1)).isSome = true := by
  decide +kernel

private theorem solvedDeclarationAccepted :
    (IndexedInductive.Guest.Declarations.elaborate baseRules baseDecoder declarationChoices
      256 (entries.take 2) ((entries.drop 2).take 1)).isSome = true := by
  decide +kernel

private theorem branchDeclarationAccepted :
    (IndexedInductive.Guest.Declarations.elaborate baseRules baseDecoder declarationChoices
      256 (entries.take 3) ((entries.drop 3).take 1)).isSome = true := by
  decide +kernel

private theorem eliminatorDeclarationAccepted :
    (IndexedInductive.Guest.Declarations.elaborate baseRules baseDecoder declarationChoices
      256 (entries.take 4) ((entries.drop 4).take 1)).isSome = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem inventoryAccepted_eq_true : inventoryAccepted = true := by
  change (IndexedInductive.Guest.Declarations.elaborate baseRules baseDecoder declarationChoices
    256 [] entries).isSome = true
  apply IndexedInductive.Guest.Declarations.elaborate_cons_of baseRules baseDecoder declarationChoices 256 answerDeclarationAccepted
  apply IndexedInductive.Guest.Declarations.elaborate_cons_of baseRules baseDecoder declarationChoices 256 familyDeclarationAccepted
  apply IndexedInductive.Guest.Declarations.elaborate_cons_of baseRules baseDecoder declarationChoices 256 solvedDeclarationAccepted
  apply IndexedInductive.Guest.Declarations.elaborate_cons_of baseRules baseDecoder declarationChoices 256 branchDeclarationAccepted
  apply IndexedInductive.Guest.Declarations.elaborate_cons_of baseRules baseDecoder declarationChoices 256 eliminatorDeclarationAccepted
  rfl

theorem inventory_admitted :
    DeclarationAdmissionReplay.Admitted baseRules [] entries := by
  obtain ⟨certificates, produced⟩ := Option.isSome_iff_exists.mp
    inventoryAccepted_eq_true
  exact IndexedInductive.Guest.Declarations.elaborate_sound
    baseRules baseDecoder declarationChoices 256 [] entries certificates produced

theorem inventory_formed : inventorySignature.Formed baseRules := by
  apply IndexedInductive.Guest.Declarations.opaque_formed baseRules entries
    inventory_admitted
  intro item member
  simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl


#print axioms inventoryAccepted_eq_true
#print axioms inventory_admitted
#print axioms inventory_formed

end Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest
