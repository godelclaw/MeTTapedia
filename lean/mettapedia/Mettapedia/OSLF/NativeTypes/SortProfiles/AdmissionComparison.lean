import Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph
import Mettapedia.OSLF.NativeTypes.SortProfiles.Source.AdmissionControls

/-!
# Equation stability and displayed-interface consistency are distinct

The same projected slot assignment can satisfy finite displayed matching and
fail uniform structural formation under an authored equation. Neither test is
an alternative proof of the other test's contract.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.AdmissionComparison

open Mettapedia.OSLF.NativeTypes.SortProfiles.Source.AdmissionControls

def displayedVertex : DisplayedGraph.Vertex commutativeChosen.language :=
  DisplayedGraph.extend commutativeChosen.language commutativeWrongVertex .star

theorem projection_preserves_chosen_assignment :
    DisplayedGraph.project commutativeChosen.language displayedVertex = commutativeWrongVertex :=
  DisplayedGraph.project_extend _ _ _

theorem displayed_assignment_consistent :
    DisplayedGraph.Consistent commutativeChosen.language [] displayedVertex := by
  have uniform : ∀ slot, displayedVertex.1 slot = .star := by
    intro slot
    simp only [displayedVertex, DisplayedGraph.extend, commutativeWrongVertex]
    split <;> rfl
  exact fun first second _ => (uniform first).trans (uniform second).symm

/-- The authored commutativity equation separates the two admission contracts. -/
theorem equation_stability_and_displayed_consistency_differ :
    commutativeGenerated.equationAdmission = some false ∧
      DisplayedGraph.check commutativeChosen.language [] displayedVertex = true :=
  ⟨authored_commutativity_rejects_unequal_input_slots,
    (DisplayedGraph.check_exact _ _ _).mpr displayed_assignment_consistent⟩

end Mettapedia.OSLF.NativeTypes.SortProfiles.AdmissionComparison
