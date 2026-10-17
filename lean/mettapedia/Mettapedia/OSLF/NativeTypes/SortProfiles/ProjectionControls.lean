import Mettapedia.OSLF.NativeTypes.SortProfiles.Projection
import Mettapedia.OSLF.NativeTypes.Instances.MeTTaFamily.Census

/-! Separating controls on authored sites, with coordinates generated from
their variable interfaces rather than supplied as an admissibility table. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.ProjectionControls

open Mettapedia.OSLF.NativeTypes.Generation.Occurrences
open Mettapedia.OSLF.NativeTypes.Instances.MeTTaFamily.Census
open Mettapedia.OSLF.NativeTypes.SortProfiles

/-- The generated receive site really loses index information when projected. -/
theorem receive_projection_loses_information :
    ∃ site ∈ generate rhoPaper, site.position = [0] ∧
      ¬ Function.Injective (@Projection.forget (SiteInterfaces.indexNames site).length
        (Slots.modalFamily rhoPaper site).slotCount) := by
  obtain ⟨site, generated, position, full, reduced⟩ := rho_receive_slots
  refine ⟨site, generated, position, ?_⟩
  rw [Projection.forget_injective_iff]
  have comparison := SiteInterfaces.slotCount_eq_family rhoPaper site
  rw [full, reduced] at comparison
  omega

/-- Distinguish raw sort profiles from sets of profiles forming signatures. -/
theorem receive_profile_and_signature_counts :
    ∃ site ∈ generate rhoPaper, site.position = [0] ∧
      Fintype.card (Projection.SiteFull rhoPaper site) = 8 ∧
      (SiteInterfaces.basedChoices (SiteInterfaces.slotCount site)).card = 128 ∧
      (SiteInterfaces.basedChoices (Slots.modalFamily rhoPaper site).slotCount).card = 8 := by
  obtain ⟨site, generated, position, full, reduced⟩ := rho_receive_slots
  refine ⟨site, generated, position, ?_, ?_, ?_⟩
  · rw [Projection.site_full_card, full]; rfl
  · rw [full, SiteInterfaces.basedChoices_card]; rfl
  · rw [reduced, SiteInterfaces.basedChoices_card]; rfl

/-- Removing no index coordinates is faithful, including empty retained blocks. -/
theorem no_index_projection_faithful (retained : Nat) :
    Function.Injective (@Projection.forget 0 retained) :=
  (Projection.forget_injective_iff 0 retained).mpr rfl

end Mettapedia.OSLF.NativeTypes.SortProfiles.ProjectionControls
