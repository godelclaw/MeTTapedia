import Mettapedia.GraphTheory.FourColor.FaceRegionDegree
import Mettapedia.GraphTheory.FourColor.RotationSystemEdgeColoring
import Mettapedia.GraphTheory.FourColor.GoertzelV24ForkInterfaceSupport

/-!
# The unique missing colour at an attachment vertex

At a vertex already touched by a selected face, an absent incident edge
forces exactly two retained incident edges. A proper colouring therefore
uses exactly two colours there, leaving a unique third colour. These facts
are derived from the cubic rotation and actual incidence.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceRegionMissingColour

open GoertzelV24FaceOrbitIncidence PhysicalForkCodeFaces PhysicalForkCodeCut
open FaceRegionDegree GoertzelV24ForkInterfaceSupport

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

/-- The incident retained edges are exactly the image of the retained darts. -/
theorem incident_image (S : Finset E) (v : V) :
    (S.filter fun x => v ∈ RS.endpoints x) =
      ((RS.dartsAt v).filter fun d => RS.edgeOf d ∈ S).image RS.edgeOf := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxS, hvx⟩ := Finset.mem_filter.mp hx
    obtain ⟨d, hd, hdv⟩ := RS.mem_endpoints_iff.mp hvx
    have hdx := RS.mem_dartsOn.mp hd
    refine Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨?_, hdx.symm ▸ hxS⟩, hdx⟩
    simp [RotationSystem.dartsAt, hdv]
  · intro hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hdv, hdS⟩ := Finset.mem_filter.mp hd
    refine Finset.mem_filter.mpr ⟨hdS, RS.mem_endpoints_iff.mpr ⟨d, RS.mem_dartsOn.mpr rfl, ?_⟩⟩
    simpa [RotationSystem.dartsAt] using hdv

theorem incident_card (S : Finset E) (v : V) :
    (S.filter fun x => v ∈ RS.endpoints x).card =
      ((RS.dartsAt v).filter fun d => RS.edgeOf d ∈ S).card := by
  rw [incident_image]
  exact Finset.card_image_of_injOn ((RS.edgeOf_injOn_dartsAt v).mono (Finset.filter_subset _ _))

variable {RS} {F : Finset (OrbitFace RS)}
variable (hC : Cubic3 RS) (hcubic : RS.IsCubic)
include hC hcubic

/-- No assumed boundary degree is needed: it follows from an old face and
the actual missing incident edge. -/
theorem incident_card_two {v : V} (hv : v ∈ touched RS (edges RS F))
    {x : E} (hx : x ∉ edges RS F) (hvx : v ∈ RS.endpoints x) :
    ((edges RS F).filter fun y => v ∈ RS.endpoints y).card = 2 := by
  obtain ⟨d, hd, hdv⟩ := RS.mem_endpoints_iff.mp hvx
  have hdx := RS.mem_dartsOn.mp hd
  have hlt : ((RS.dartsAt v).filter fun a => RS.edgeOf a ∈ edges RS F).card < 3 := by
    rw [← hcubic v]
    apply Finset.card_lt_card
    apply Finset.filter_ssubset.mpr
    refine ⟨d, ?_, hdx.symm ▸ hx⟩
    simp [RotationSystem.dartsAt, hdv]
  have hpos := Finset.card_pos.mpr ((touched_iff_sectors_nonempty RS F v).mp hv)
  have hf := retained_degree_formula (R := F) hC d
  rw [hdv] at hf
  rw [incident_card]
  split_ifs at hf <;> omega

/-- Properness makes the incidence-colour image injective at this vertex. -/
theorem profile_card_two {v : V} (hv : v ∈ touched RS (edges RS F))
    {x : E} (hx : x ∉ edges RS F) (hvx : v ∈ RS.endpoints x)
    {a : E → Fin 3} (ha : Proper RS.endpoints (edges RS F) a) :
    (profile RS.endpoints (edges RS F) a v).card = 2 := by
  have hinj : Set.InjOn a ((edges RS F).filter fun y => v ∈ RS.endpoints y) := by
    intro y hy z hz heq
    by_contra hyz
    obtain ⟨hyF, hvy⟩ := Finset.mem_filter.mp hy
    obtain ⟨hzF, hvz⟩ := Finset.mem_filter.mp hz
    exact ha y hyF z hzF hyz ⟨v, Finset.mem_inter.mpr ⟨hvy, hvz⟩⟩ heq
  rw [profile, Finset.card_image_of_injOn hinj]
  exact incident_card_two hC hcubic hv hx hvx

/-- The allowed colour is unique, rather than an extra input to transfer. -/
theorem existsUnique_missing {v : V} (hv : v ∈ touched RS (edges RS F))
    {x : E} (hx : x ∉ edges RS F) (hvx : v ∈ RS.endpoints x)
    {a : E → Fin 3} (ha : Proper RS.endpoints (edges RS F) a) :
    ∃! q : Fin 3, q ∉ profile RS.endpoints (edges RS F) a v := by
  have hcard : ((profile RS.endpoints (edges RS F) a v)ᶜ).card = 1 := by
    rw [Finset.card_compl, profile_card_two hC hcubic hv hx hvx ha]
    rfl
  simpa only [Finset.mem_compl] using Finset.card_eq_one_iff_existsUnique.mp hcard

end
end Mettapedia.GraphTheory.FourColor.FaceRegionMissingColour
