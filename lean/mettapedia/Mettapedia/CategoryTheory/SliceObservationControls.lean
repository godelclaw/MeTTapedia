import Mettapedia.CategoryTheory.SliceObservation

/-!
# Separating and incomplete observations

Each coordinate of a pair forgets information. Observing both coordinates
recovers the original conversion discipline. An explicit arrow between two
constant representations shows what a coarse view adds: the source meanings
are different, but the observed triangle commutes.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.CategoryTheory.SliceObservationControls

open SliceObservation

/-- Reading both coordinates admits exactly the original conversions. -/
theorem pair_coordinates_full :
    (Over.map (TypeCat.ofHom fun value : Bool × Bool => (value.1, value.2))).Full := by
  rw [pair_map_full_iff]
  exact fun _ _ => Prod.ext

/-- The first coordinate alone does not enforce the original meaning. -/
theorem first_coordinate_not_full :
    ¬(Over.map (TypeCat.ofHom (Prod.fst : Bool × Bool → Bool))).Full := by
  rw [map_full_iff_injective]
  intro injective
  have impossible : (false, false) = (false, true) := injective rfl
  exact Bool.false_ne_true (congrArg Prod.snd impossible)

/-- The second coordinate alone is likewise incomplete. -/
theorem second_coordinate_not_full :
    ¬(Over.map (TypeCat.ofHom (Prod.snd : Bool × Bool → Bool))).Full := by
  rw [map_full_iff_injective]
  intro injective
  have impossible : (false, false) = (true, false) := injective rfl
  exact Bool.false_ne_true (congrArg Prod.fst impossible)

/-- A representation with one stored value denoting the first pair. -/
def first : Over (Bool × Bool) :=
  Over.mk (TypeCat.ofHom fun _ : Unit => (false, false))

/-- The same storage shape, with a different second-coordinate meaning. -/
def second : Over (Bool × Bool) :=
  Over.mk (TypeCat.ofHom fun _ : Unit => (false, true))

/-- The first-coordinate observer licenses a conversion between the two
representations. Its underlying identity function is concrete data. -/
def coarseArrow :
    (Over.map (TypeCat.ofHom (Prod.fst : Bool × Bool → Bool))).obj first ⟶
      (Over.map (TypeCat.ofHom (Prod.fst : Bool × Bool → Bool))).obj second :=
  Over.homMk (𝟙 Unit) (by rfl)

/-- No function between the two singleton carriers preserves the full pair. -/
theorem no_fine_arrow : ¬Nonempty (first ⟶ second) := by
  rintro ⟨arrow⟩
  have same := ConcreteCategory.congr_hom (Over.w arrow) ()
  have impossible : true = false := congrArg Prod.snd same
  exact Bool.false_ne_true impossible.symm

/-- The observed conversion has no full-semantic lifting. -/
theorem coarseArrow_has_no_lift :
    ¬∃ arrow : first ⟶ second,
      (Over.map (TypeCat.ofHom (Prod.fst : Bool × Bool → Bool))).map arrow = coarseArrow := by
  rintro ⟨arrow, _⟩
  exact no_fine_arrow ⟨arrow⟩

end Mettapedia.CategoryTheory.SliceObservationControls
