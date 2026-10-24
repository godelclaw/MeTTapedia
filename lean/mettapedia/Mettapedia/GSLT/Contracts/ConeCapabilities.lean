import Mettapedia.Algebra.FocusedAccess
import Mettapedia.GSLT.Contracts.AuthorityControls

/-!
# Capabilities on regions of a trie

A capability names a region of a path-indexed store, the cone of a prefix, and
the rights held there (`Capability`).  Its authority is located: the rights at
every path of the cone and nothing elsewhere (`Capability.located`), an element
of the pointwise separation algebra of rights
(`Mettapedia.GSLT.SeparationAlgebra.instPi`).  Reading and writing through a
capability goes through the focus below its prefix
(`Mettapedia.Algebra.FocusedAccess.below`), which changes nothing outside the cone
(`Mettapedia.Algebra.FocusedAccess.below_put_of_not_prefix`).

* **Two capabilities coexist exactly when their regions are disjoint or their
  rights coexist** (`located_separate_iff`).  Since cones are laminar, this is a
  test on two prefixes and two rights: writers below incomparable prefixes coexist
  (`Controls.sibling_writers_coexist`), a writer and a reader of nested regions do
  not (`Controls.nested_writer_reader_conflict`), readers always do
  (`Controls.nested_readers_coexist`).
* **Attenuation is a frame-preserving update** (`Attenuates.frameUpdate`):
  narrowing the region and updating the rights without breaking a frame never
  breaks a frame of anyone else.  Attenuation is a preorder (`Attenuates.refl`,
  `Attenuates.trans`), the order in which object capabilities are delegated.
* **Widening is not**: enlarging a writer's region breaks the frame of a reader of
  the sibling region (`Controls.widening_breaks_frame`), and a read capability
  never updates to a consume capability on the same region
  (`Controls.read_not_upgraded`).

The rights are any separation algebra: `Access` (none, read, consume) here, and the
append and monotone-read rights of `Mettapedia.GSLT.Contracts.AppendAuthority`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.ConeCapabilities

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.SeparationAlgebra.SepAlgebra
open Mettapedia.Algebra.FocusedAccess
open scoped Mettapedia.GSLT.SeparationAlgebra

universe u v

/-- A capability: rights over the cone of a prefix. -/
structure Capability (σ : Type u) (R : Type v) where
  region : List σ
  rights : R

variable {σ : Type u} [DecidableEq σ] {R : Type v} [Zero R] [Add R] [SepAlgebra R]

namespace Capability

/-- The rights a capability holds at each path. -/
def located (capability : Capability σ R) : List σ → R :=
  fun path => if capability.region <+: path then capability.rights else 0

omit [Add R] [SepAlgebra R] in
theorem located_of_mem {capability : Capability σ R} {path : List σ}
    (inside : capability.region <+: path) : capability.located path = capability.rights := by
  simp [located, inside]

omit [Add R] [SepAlgebra R] in
theorem located_of_not_mem {capability : Capability σ R} {path : List σ}
    (outside : ¬ capability.region <+: path) : capability.located path = 0 := by
  simp [located, outside]

end Capability

open Capability

/-- **Two capabilities coexist exactly when their regions are disjoint or their
rights coexist.** -/
theorem located_separate_iff (first second : Capability σ R) :
    first.located ## second.located ↔
      (¬ first.region <+: second.region ∧ ¬ second.region <+: first.region) ∨
        first.rights ## second.rights := by
  constructor
  · intro separate
    by_cases firstBelow : first.region <+: second.region
    · right
      have atSecond := separate second.region
      rwa [located_of_mem firstBelow, located_of_mem (List.prefix_refl _)] at atSecond
    · by_cases secondBelow : second.region <+: first.region
      · right
        have atFirst := separate first.region
        rwa [located_of_mem (List.prefix_refl _), located_of_mem secondBelow] at atFirst
      · exact Or.inl ⟨firstBelow, secondBelow⟩
  · rintro (⟨notFirst, notSecond⟩ | rightsSeparate) path
    · by_cases inFirst : first.region <+: path
      · have notInSecond : ¬ second.region <+: path := fun inSecond =>
          (List.prefix_or_prefix_of_prefix inFirst inSecond).elim notFirst notSecond
        rw [located_of_not_mem notInSecond]
        exact separate_zero _
      · rw [located_of_not_mem inFirst]
        exact zero_separate _
    · by_cases inFirst : first.region <+: path <;> by_cases inSecond : second.region <+: path
      · rwa [located_of_mem inFirst, located_of_mem inSecond]
      · rw [located_of_mem inFirst, located_of_not_mem inSecond]
        exact separate_zero _
      · rw [located_of_not_mem inFirst]
        exact zero_separate _
      · rw [located_of_not_mem inFirst]
        exact zero_separate _

omit [DecidableEq σ] in
/-- Frame-preserving updates of located rights are decided path by path. -/
theorem frameUpdate_of_pointwise {first second : List σ → R}
    (pointwise : ∀ path, FrameUpdate (first path) (second path)) : FrameUpdate first second :=
  fun frame separate path => pointwise path (frame path) (separate path)

/-- **Attenuation**: narrow the region and update the rights without breaking a
frame. -/
structure Attenuates (stronger weaker : Capability σ R) : Prop where
  narrows : stronger.region <+: weaker.region
  weakens : FrameUpdate stronger.rights weaker.rights

omit [DecidableEq σ] in
theorem Attenuates.refl (capability : Capability σ R) : Attenuates capability capability :=
  ⟨List.prefix_refl _, FrameUpdate.refl _⟩

omit [DecidableEq σ] in
theorem Attenuates.trans {first second third : Capability σ R} (firstSecond : Attenuates first second)
    (secondThird : Attenuates second third) : Attenuates first third :=
  ⟨firstSecond.narrows.trans secondThird.narrows, firstSecond.weakens.trans secondThird.weakens⟩

/-- **Attenuation never breaks a frame.** -/
theorem Attenuates.frameUpdate {stronger weaker : Capability σ R} (attenuates : Attenuates stronger weaker) :
    FrameUpdate stronger.located weaker.located := by
  apply frameUpdate_of_pointwise
  intro path
  by_cases inWeaker : weaker.region <+: path
  · rw [located_of_mem (attenuates.narrows.trans inWeaker), located_of_mem inWeaker]
    exact attenuates.weakens
  · rw [located_of_not_mem inWeaker]
    exact FrameUpdate.to_zero _

/-! ## Controls, with read and consume rights -/

namespace Controls

/-- A writer of a region. -/
def writer (region : List ℕ) : Capability ℕ Access := ⟨region, .consume⟩

/-- A reader of a region. -/
def reader (region : List ℕ) : Capability ℕ Access := ⟨region, .read⟩

/-- **Writers below incomparable prefixes coexist.** -/
theorem sibling_writers_coexist : (writer [0, 1]).located ## (writer [0, 2]).located :=
  (located_separate_iff _ _).mpr (Or.inl ⟨by simp [writer], by simp [writer]⟩)

/-- **A writer and a reader of nested regions do not.** -/
theorem nested_writer_reader_conflict : ¬ (writer [0]).located ## (reader [0, 1]).located := by
  rw [located_separate_iff]
  rintro (⟨notBelow, -⟩ | separate)
  · exact notBelow (by simp [writer, reader])
  · exact absurd separate (by decide)

/-- **Readers of nested regions coexist.** -/
theorem nested_readers_coexist : (reader [0]).located ## (reader [0, 1]).located :=
  (located_separate_iff _ _).mpr (Or.inr Access.read_selfSeparate)

/-- **Widening a writer's region breaks the frame of a reader of the sibling
region.** -/
theorem widening_breaks_frame : ¬ FrameUpdate (writer [0, 1]).located (writer [0]).located := by
  intro update
  have before : (writer [0, 1]).located ## (reader [0, 2]).located :=
    (located_separate_iff _ _).mpr (Or.inl ⟨by simp [writer, reader], by simp [writer, reader]⟩)
  have after := update _ before
  rw [located_separate_iff] at after
  rcases after with ⟨notBelow, -⟩ | separate
  · exact notBelow (by simp [writer, reader])
  · exact absurd separate (by decide)

/-- **A read capability never updates to a consume capability on its region.** -/
theorem read_not_upgraded (region : List ℕ) :
    ¬ FrameUpdate (reader region).located (writer region).located := by
  intro update
  have before : (reader region).located ## (reader region).located :=
    (located_separate_iff _ _).mpr (Or.inr Access.read_selfSeparate)
  have after := update _ before
  rw [located_separate_iff] at after
  rcases after with ⟨notBelow, -⟩ | separate
  · exact notBelow (List.prefix_refl _)
  · exact absurd separate (show ¬ (Access.read ## Access.consume) by decide)

/-- Delegating a narrower reader from a writer is an attenuation. -/
theorem writer_attenuates_to_reader : Attenuates (writer [0]) (reader [0, 1]) :=
  ⟨by simp [writer, reader], Access.consume_updates_read⟩

end Controls

end Mettapedia.GSLT.Contracts.ConeCapabilities
