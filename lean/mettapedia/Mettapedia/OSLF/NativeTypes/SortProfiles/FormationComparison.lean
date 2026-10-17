import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeEnrichment
import Mettapedia.OSLF.NativeTypes.SortProfiles.Inhabitation
import Mettapedia.OSLF.NativeTypes.Instances.MeTTaFamily.EquationSite

/-!
# Free code formation and target-premised modal formation differ

The free code algebra may add a nullary code without supplying an operational
inhabitant. The paper's modal completion requires a target classifier even
when a site has no index or rely variables. These are distinct judgments:
the following controls refute their unconditional identification, not the
soundness of either judgment against its own specification.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.FormationComparison

open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.MeTTaIL.Syntax (TypeExpr)
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open Mettapedia.OSLF.NativeTypes.SortProfiles.Inhabitation
open Mettapedia.Logic.LP.HypotheticalPropositional (Derives)

/-- A diagnostic free-code signature, with an empty operational carrier. -/
def nullarySignature : CubeEnrichment.Signature where
  Carrier := TypeExpr
  Former := Unit
  arity := fun _ => 0
  input := fun _ => Fin.elim0
  output := fun _ => .base "Term"

def emptyOperational (_ : TypeExpr) : Type := Empty

def origin : CubeEnrichment.Vertex nullarySignature := fun _ _ => .star

def closedCode : CubeEnrichment.Code nullarySignature emptyOperational (.base "Term") :=
  .former () (fun position => Fin.elim0 position)

theorem closed_code_formed :
    Nonempty (CubeEnrichment.Kinded origin closedCode .star) := by
  apply (CubeEnrichment.inferKind_exact origin closedCode .star).mp
  simp [CubeEnrichment.inferKind, closedCode, origin, CubeEnrichment.outputSort,
    nullarySignature]

theorem no_operational_inhabitant : ¬ Nonempty (emptyOperational (.base "Term")) := by
  rintro ⟨value⟩
  exact Empty.elim value

def targetOnlyInterface : Interface := ⟨[], [], .base "Term", .base "Term"⟩

theorem target_only_requires_target (profile : Profile) :
    (modalClause targetOnlyInterface profile).premises =
      [(∅, (TypeExpr.base "Term", profile.target))] :=
  rely_free_premises rfl rfl profile

theorem paper_origin_has_no_classifier :
    ¬ Derives (originClauses [targetOnlyInterface] [.base "Term"]) ∅
      (TypeExpr.base "Term", HSort.star) := origin_has_no_types _ _ _

/-- A freely formed code cannot replace the modal target-premise obligation. -/
theorem free_formation_does_not_imply_paper_formation :
    ¬ (∀ code : CubeEnrichment.Code nullarySignature emptyOperational (.base "Term"),
      Nonempty (CubeEnrichment.Kinded origin code .star) →
        Derives (originClauses [targetOnlyInterface] [.base "Term"]) ∅
          (TypeExpr.base "Term", HSort.star)) := by
  intro comparison
  exact paper_origin_has_no_classifier (comparison closedCode closed_code_formed)

/-- An actual machine site separates the focus carrier from the target carrier. -/
theorem he_call_has_distinct_focus_and_target :
    ∃ interface,
      interfaceOf?
          Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE
          Mettapedia.OSLF.NativeTypes.Instances.MeTTaFamily.EquationSite.machineCallSite =
        some interface ∧ interface.hole ≠ interface.target := by
  refine ⟨⟨[], [.base "Atom", .base "Space", .base "Atom"], .base "Atom", .base "State"⟩,
    Mettapedia.OSLF.NativeTypes.Instances.MeTTaFamily.EquationSite.machine_call_interface, ?_⟩
  decide

end Mettapedia.OSLF.NativeTypes.SortProfiles.FormationComparison
