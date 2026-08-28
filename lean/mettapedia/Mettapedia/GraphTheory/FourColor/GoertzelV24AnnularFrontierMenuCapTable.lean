import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierMenuCapMatching
import Mathlib.Data.Fin.VecNotation

/-!
# The complete normalized pentagonal cap table

The source lists the ten good boundary words whose majority colour has been
normalized to `red`.  For each row it gives the unique colouring of the five
cap edges and the cap matchings for the pairs `red/blue` and `red/purple`.

This file checks the whole table as one finite object.  The explicit data are
kept separate from the generic mathematics: uniqueness of the extension is
proved in `GoertzelV24AnnularFrontierMenuCapExtension`, while
`GoertzelV24AnnularFrontierMenuCapMatching.selected_iff` proves for every good
word that the matching depends only on the inactive position.  The finite
calculation below therefore certifies published data; it is not a case split in
the Four-Colour argument.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularFrontierMenuCapTable

open GoertzelV24AnnularFrontierMenuCapExtension
open GoertzelV24AnnularFrontierMenuCapMatching

/-- One displayed matching `ab | cd`, with the two pairs regarded as unordered
blocks. -/
structure PairingCode where
  firstLeft : Fin 5
  firstRight : Fin 5
  secondLeft : Fin 5
  secondRight : Fin 5
  deriving DecidableEq

def PairingCode.blocks (code : PairingCode) : Finset (Finset (Fin 5)) :=
  {{code.firstLeft, code.firstRight}, {code.secondLeft, code.secondRight}}

/-- The two blocks supplied by the generic cap-pairing theorem at inactive
position `v`. -/
def capPairingBlocks (v : Fin 5) : Finset (Finset (Fin 5)) :=
  {{v + 4, v + 1}, {v + 2, v + 3}}

/-- On active positions, `CapPairRel` means exactly membership in a common
block of `capPairingBlocks`. -/
theorem capPairRel_iff_mem_capPairingBlocks {v i j : Fin 5}
    (hi : i ≠ v) (hj : j ≠ v) :
    CapPairRel v i j ↔
      ∃ block ∈ capPairingBlocks v, i ∈ block ∧ j ∈ block := by
  revert v i j
  decide

/-- The ten normalized good boundary words, in the order printed in the
source table. -/
def normalizedTableWord : Fin 10 → CAP5BoundaryWord :=
  ![
    ![red, red, red, blue, purple],
    ![red, red, red, purple, blue],
    ![red, red, blue, purple, red],
    ![red, red, purple, blue, red],
    ![red, blue, purple, red, red],
    ![red, purple, blue, red, red],
    ![blue, red, red, red, purple],
    ![blue, purple, red, red, red],
    ![purple, red, red, red, blue],
    ![purple, blue, red, red, red]
  ]

/-- The ten published cap extensions, in the same row order. -/
def normalizedTableExtension : Fin 10 → CAP5InternalCycleColoring :=
  ![
    ![purple, blue, purple, red, blue],
    ![blue, purple, blue, red, purple],
    ![blue, purple, red, blue, purple],
    ![purple, blue, red, purple, blue],
    ![purple, red, blue, purple, blue],
    ![blue, red, purple, blue, purple],
    ![purple, blue, purple, blue, red],
    ![red, blue, purple, blue, purple],
    ![blue, purple, blue, purple, red],
    ![red, purple, blue, purple, blue]
  ]

/-- Inactive positions for the `red/blue` pair. -/
def normalizedRedBlueInactive : Fin 10 → Fin 5 :=
  ![4, 3, 3, 2, 2, 1, 4, 1, 0, 0]

/-- Inactive positions for the `red/purple` pair. -/
def normalizedRedPurpleInactive : Fin 10 → Fin 5 :=
  ![3, 4, 2, 3, 1, 2, 0, 0, 4, 1]

/-- The displayed `red/blue` matching column. -/
def normalizedRedBluePairing : Fin 10 → PairingCode :=
  ![
    ⟨0, 3, 1, 2⟩,
    ⟨0, 1, 2, 4⟩,
    ⟨0, 1, 2, 4⟩,
    ⟨0, 4, 1, 3⟩,
    ⟨0, 4, 1, 3⟩,
    ⟨0, 2, 3, 4⟩,
    ⟨0, 3, 1, 2⟩,
    ⟨0, 2, 3, 4⟩,
    ⟨1, 4, 2, 3⟩,
    ⟨1, 4, 2, 3⟩
  ]

/-- The displayed `red/purple` matching column. -/
def normalizedRedPurplePairing : Fin 10 → PairingCode :=
  ![
    ⟨0, 1, 2, 4⟩,
    ⟨0, 3, 1, 2⟩,
    ⟨0, 4, 1, 3⟩,
    ⟨0, 1, 2, 4⟩,
    ⟨0, 2, 3, 4⟩,
    ⟨0, 4, 1, 3⟩,
    ⟨1, 4, 2, 3⟩,
    ⟨1, 4, 2, 3⟩,
    ⟨0, 3, 1, 2⟩,
    ⟨0, 2, 3, 4⟩
  ]

/-- Every displayed cap-edge colouring is a proper extension of its displayed
boundary word. -/
theorem normalizedTableExtension_extends (row : Fin 10) :
    CAP5ExtendsAcrossCycleWith (normalizedTableWord row)
      (normalizedTableExtension row) := by
  fin_cases row <;> decide

/-- Hence each displayed extension is the unique extension selected by the
generic cap-extension function. -/
theorem capExtension_normalizedTableWord (row : Fin 10) :
    capExtension (normalizedTableWord row) = normalizedTableExtension row :=
  capExtension_eq (normalizedTableExtension_extends row)

/-- The `red/blue` inactive-position column is correct in every row. -/
theorem normalizedTableWord_inactive_red_blue (row : Fin 10) :
    InactivePosition (normalizedTableWord row) red blue
      (normalizedRedBlueInactive row) := by
  fin_cases row <;> exact ⟨by decide, by decide⟩

/-- The `red/purple` inactive-position column is correct in every row. -/
theorem normalizedTableWord_inactive_red_purple (row : Fin 10) :
    InactivePosition (normalizedTableWord row) red purple
      (normalizedRedPurpleInactive row) := by
  fin_cases row <;> exact ⟨by decide, by decide⟩

/-- The full displayed `red/blue` matching column agrees with the generic
closed form. -/
theorem normalizedRedBluePairing_correct (row : Fin 10) :
    capPairingBlocks (normalizedRedBlueInactive row) =
      (normalizedRedBluePairing row).blocks := by
  fin_cases row <;> decide

/-- The full displayed `red/purple` matching column agrees with the generic
closed form. -/
theorem normalizedRedPurplePairing_correct (row : Fin 10) :
    capPairingBlocks (normalizedRedPurpleInactive row) =
      (normalizedRedPurplePairing row).blocks := by
  fin_cases row <;> decide

/-- **The complete normalized source table is correct.**  This packages the
unique cap extension, both inactive positions, and both displayed matching
columns for each of the ten rows. -/
theorem normalizedCapTable_correct (row : Fin 10) :
    capExtension (normalizedTableWord row) = normalizedTableExtension row ∧
    InactivePosition (normalizedTableWord row) red blue
      (normalizedRedBlueInactive row) ∧
    InactivePosition (normalizedTableWord row) red purple
      (normalizedRedPurpleInactive row) ∧
    capPairingBlocks (normalizedRedBlueInactive row) =
      (normalizedRedBluePairing row).blocks ∧
    capPairingBlocks (normalizedRedPurpleInactive row) =
      (normalizedRedPurplePairing row).blocks :=
  ⟨capExtension_normalizedTableWord row,
    normalizedTableWord_inactive_red_blue row,
    normalizedTableWord_inactive_red_purple row,
    normalizedRedBluePairing_correct row,
    normalizedRedPurplePairing_correct row⟩

/-- The unique cap extension commutes with every zero-fixing permutation of
the colour names.  Together with the normalized table, this transports the
calculation to the unnormalized colour choices in the source. -/
theorem capExtension_map_equiv_of_map_zero {σ : Color ≃ Color}
    (hσ0 : σ 0 = 0) {w : CAP5BoundaryWord}
    (h : CAP5WordExtendsAcrossCycle w) :
    capExtension (cap5MapBoundaryWord σ w) =
      cap5MapInternalCycleColoring σ (capExtension w) :=
  capExtension_eq
    (cap5ExtendsAcrossCycleWith_map_equiv_of_map_zero hσ0
      (capExtension_spec h))

/-- Relabeling the colours relabels the active pair and preserves its inactive
position. -/
theorem inactivePosition_map_equiv {σ : Color ≃ Color}
    {w : CAP5BoundaryWord} {p q : Color} {v : Fin 5}
    (hv : InactivePosition w p q v) :
    InactivePosition (cap5MapBoundaryWord σ w) (σ p) (σ q) v := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change σ (w v) ≠ σ p
    exact fun h => hv.not_active.1 (σ.injective h)
  · change σ (w v) ≠ σ q
    exact fun h => hv.not_active.2 (σ.injective h)
  · intro i hip hiq
    apply hv.eq_of_not_active i
    · intro h
      apply hip
      change σ (w i) = σ p
      exact congrArg σ h
    · intro h
      apply hiq
      change σ (w i) = σ q
      exact congrArg σ h

/-- **The normalized table transports to every choice of colour names.**
For every zero-fixing colour permutation, the displayed extension is relabeled
pointwise, the two inactive positions remain the displayed positions, and the
two matching columns are unchanged as partitions of the cap indices. -/
theorem normalizedCapTable_transport (σ : Color ≃ Color) (hσ0 : σ 0 = 0)
    (row : Fin 10) :
    capExtension (cap5MapBoundaryWord σ (normalizedTableWord row)) =
        cap5MapInternalCycleColoring σ (normalizedTableExtension row) ∧
    InactivePosition (cap5MapBoundaryWord σ (normalizedTableWord row))
      (σ red) (σ blue) (normalizedRedBlueInactive row) ∧
    InactivePosition (cap5MapBoundaryWord σ (normalizedTableWord row))
      (σ red) (σ purple) (normalizedRedPurpleInactive row) ∧
    capPairingBlocks (normalizedRedBlueInactive row) =
      (normalizedRedBluePairing row).blocks ∧
    capPairingBlocks (normalizedRedPurpleInactive row) =
      (normalizedRedPurplePairing row).blocks := by
  have hextends : CAP5WordExtendsAcrossCycle (normalizedTableWord row) :=
    ⟨normalizedTableExtension row, normalizedTableExtension_extends row⟩
  refine ⟨?_,
    inactivePosition_map_equiv (normalizedTableWord_inactive_red_blue row),
    inactivePosition_map_equiv (normalizedTableWord_inactive_red_purple row),
    normalizedRedBluePairing_correct row,
    normalizedRedPurplePairing_correct row⟩
  calc
    capExtension (cap5MapBoundaryWord σ (normalizedTableWord row)) =
        cap5MapInternalCycleColoring σ
          (capExtension (normalizedTableWord row)) :=
      capExtension_map_equiv_of_map_zero hσ0 hextends
    _ = cap5MapInternalCycleColoring σ (normalizedTableExtension row) :=
      congrArg (cap5MapInternalCycleColoring σ)
        (capExtension_normalizedTableWord row)

end GoertzelV24AnnularFrontierMenuCapTable

end Mettapedia.GraphTheory.FourColor
