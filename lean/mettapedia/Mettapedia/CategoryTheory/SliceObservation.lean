import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Types.Basic

/-!
# Observation change in a category of representations

An object of Mathlib's `Over Meaning` is a representation together with its
meaning map. A morphism is a concrete conversion that preserves that meaning.
Postcomposition with an observation `Meaning ⟶ Observation` weakens the
commuting triangle required of conversions.

The existing conversions remain distinct: `Over.map` is always faithful.
Every conversion admitted by the observation preserves the original meaning
precisely when the observation is monic. Over types this says injective;
for a family of observations it says jointly separating. No operational
transition, cost model, or algorithm is inferred from a slice morphism.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.CategoryTheory.SliceObservation

universe v u

section Category

variable {C : Type u} [Category.{v} C] {Meaning Observation : C}

/-- Changing the observation never identifies two existing conversions. -/
theorem map_faithful (observe : Meaning ⟶ Observation) :
    (Over.map observe).Faithful where
  map_injective := by
    intro source target first second same
    apply Over.OverMorphism.ext
    exact congrArg (fun arrow => arrow.left) same

/-- A monic observation permits exactly the meaning-preserving conversions. -/
theorem map_full_of_mono (observe : Meaning ⟶ Observation) [Mono observe] :
    (Over.map observe).Full where
  map_surjective := by
    intro source target arrow
    refine ⟨Over.homMk arrow.left ?_, ?_⟩
    · apply (cancel_mono observe).1
      simpa only [Over.map_obj_hom, Category.assoc] using Over.w arrow
    · apply Over.OverMorphism.ext
      rfl

/-- If every observed commuting triangle lifts, the observation is monic.
The proof tests two arbitrary meaning maps with the same observation, rather
than assuming that the selected examples exhaust the semantic domain. -/
theorem mono_of_map_full (observe : Meaning ⟶ Observation)
    (full : (Over.map observe).Full) : Mono observe := by
  have := full
  constructor
  intro carrier first second same
  let observed : (Over.map observe).obj (Over.mk first) ⟶
      (Over.map observe).obj (Over.mk second) :=
    Over.homMk (𝟙 carrier) (by simpa using same.symm)
  obtain ⟨original, lifts⟩ := (Over.map observe).map_surjective observed
  have underlying : original.left = 𝟙 carrier := congrArg (fun arrow => arrow.left) lifts
  simpa [underlying] using (Over.w original).symm

/-- An observation admits no additional conversions exactly when it is monic. -/
theorem map_full_iff_mono (observe : Meaning ⟶ Observation) :
    (Over.map observe).Full ↔ Mono observe :=
  ⟨mono_of_map_full observe, fun _ => map_full_of_mono observe⟩

end Category

section Types

variable {Meaning Observation : Type u}

/-- Over types, losing a distinction permits an additional observed conversion. -/
theorem map_full_iff_injective (observe : Meaning → Observation) :
    (Over.map (TypeCat.ofHom observe)).Full ↔ Function.Injective observe := by
  rw [map_full_iff_mono, _root_.CategoryTheory.ofHom_mono_iff_injective]

/-- Several observations retain the full conversion discipline when together
 they distinguish every pair of meanings; no individual observer need do so. -/
theorem family_map_full_iff {Index : Type u} {View : Index → Type u}
    (observe : ∀ index, Meaning → View index) :
    (Over.map (TypeCat.ofHom fun meaning index => observe index meaning)).Full ↔
      ∀ first second, (∀ index, observe index first = observe index second) →
        first = second := by
  rw [map_full_iff_injective]
  constructor
  · intro injective first second same
    exact injective (funext same)
  · intro separates first second same
    exact separates first second (congrFun same)

/-- Two individually incomplete views can jointly retain all meaning. -/
theorem pair_map_full_iff {First Second : Type u}
    (firstView : Meaning → First) (secondView : Meaning → Second) :
    (Over.map (TypeCat.ofHom fun meaning => (firstView meaning, secondView meaning))).Full ↔
      ∀ first second, firstView first = firstView second →
        secondView first = secondView second → first = second := by
  rw [map_full_iff_injective]
  constructor
  · intro injective first second one two
    exact injective (Prod.ext one two)
  · intro separates first second same
    exact separates first second (congrArg Prod.fst same) (congrArg Prod.snd same)

end Types

end Mettapedia.CategoryTheory.SliceObservation
