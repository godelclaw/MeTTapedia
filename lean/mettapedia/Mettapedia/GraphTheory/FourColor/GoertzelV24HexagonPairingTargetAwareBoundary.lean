import Mettapedia.GraphTheory.FourColor.GoertzelV24HexagonPlanarPairingObstruction
import Mettapedia.GraphTheory.FourColor.GoertzelV24TargetAwareReplacementQuantifiers

/-!
# Target-aware boundary for planar pairing replacements of a hexagon

Allowing a replacement to depend on the exterior is useful only when the
exterior ranges over a genuinely restricted physical language.  This file
specializes that quantifier boundary to the five noncrossing pairing caps of
a six-port hexagon, using genuine nonzero Tait boundary words throughout.

Every pairing cap accepts at least one nonzero word which the hexagon does not
accept.  Consequently no pairing-cap support is contained in the hexagon
support.  The complement of the hexagon support is therefore one abstract
zero exterior which meets every pairing support, so even an exterior-dependent
choice among the five caps cannot work against arbitrary exterior supports.

This does not assert that the complement support is realized by a planar
exterior.  It isolates physical realizability as the only remaining loophole
for this particular target-aware repair.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexagonPairingTargetAwareBoundary

open GoertzelV24RawNooseCountPumping
open GoertzelV24TargetAwareReplacementQuantifiers

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Genuine nonzero boundary words on the six cyclic ports. -/
abbrev HexagonTaitWord := CutWord (Fin 6)

/-- Forget the nonzero proofs carried by a genuine Tait word. -/
def rawWord (word : HexagonTaitWord) : HexagonBoundaryWord :=
  fun port => (word port).1

/-- The exact support of the literal hexagon, restricted to genuine Tait
boundary words. -/
def hexagonSupport : Set HexagonTaitWord :=
  {word | ∃ coloring, IsHexagonExtension (rawWord word) coloring}

/-- The support of one of the five noncrossing planar pairing caps. -/
def planarPairingSupport (side : HexagonPlanarPairing) : Set HexagonTaitWord :=
  {word | side.Compatible (rawWord word)}

@[simp] theorem mem_hexagonSupport_iff (word : HexagonTaitWord) :
    word ∈ hexagonSupport ↔
      ∃ coloring, IsHexagonExtension (rawWord word) coloring :=
  Iff.rfl

@[simp] theorem mem_planarPairingSupport_iff
    (side : HexagonPlanarPairing) (word : HexagonTaitWord) :
    word ∈ planarPairingSupport side ↔ side.Compatible (rawWord word) :=
  Iff.rfl

/-- Every planar pairing cap accepts a genuine nonzero boundary word which
does not extend across the hexagon.  This is the support-inclusion obstruction
needed by the target-aware quantifier theorem. -/
theorem every_planarPairing_accepts_nonextension :
    ∀ side : HexagonPlanarPairing,
      ∃ word : HexagonTaitWord,
        side.Compatible (rawWord word) ∧
          ¬ ∃ coloring, IsHexagonExtension (rawWord word) coloring := by
  decide

/-- No one planar pairing cap is a monotone support replacement for the
hexagon. -/
theorem no_planarPairingSupport_subset :
    ∀ side : HexagonPlanarPairing,
      ¬ planarPairingSupport side ⊆ hexagonSupport := by
  intro side hsubset
  obtain ⟨word, hpairing, hhexagon⟩ :=
    every_planarPairing_accepts_nonextension side
  exact hhexagon (hsubset hpairing)

/-- The maximal abstract zero exterior for the hexagon meets every planar
pairing support. -/
theorem complement_hexagonSupport_meets_every_planarPairing :
    Disjoint hexagonSupportᶜ hexagonSupport ∧
      ∀ side : HexagonPlanarPairing,
        ¬ Disjoint hexagonSupportᶜ (planarPairingSupport side) :=
  complement_adversary_of_no_subset
    hexagonSupport planarPairingSupport no_planarPairingSupport_subset

/-- **Unrestricted target-aware planar-pairing reduction fails.**  Even when
the chosen cap may depend on the exterior, one cannot handle every abstract
exterior support having zero Count with the hexagon. -/
theorem no_unrestricted_targetAware_planarPairing_reduction :
    ¬ (∀ exterior : Set HexagonTaitWord,
        Disjoint exterior hexagonSupport →
          ∃ side : HexagonPlanarPairing,
            Disjoint exterior (planarPairingSupport side)) := by
  intro h
  have hsubset :
      ∃ side : HexagonPlanarPairing,
        planarPairingSupport side ⊆ hexagonSupport :=
    (unrestricted_targetAware_iff_exists_subset
      hexagonSupport planarPairingSupport).1 h
  obtain ⟨side, hside⟩ := hsubset
  exact no_planarPairingSupport_subset side hside

/-- The same failure holds for any proposed physical exterior class which
contains the complement of the hexagon support. -/
theorem no_physical_targetAware_planarPairing_reduction_of_complement_mem
    (physicalExterior : Set (Set HexagonTaitWord))
    (hcomplement : hexagonSupportᶜ ∈ physicalExterior) :
    ¬ (∀ exterior ∈ physicalExterior,
        Disjoint exterior hexagonSupport →
          ∃ side : HexagonPlanarPairing,
            Disjoint exterior (planarPairingSupport side)) := by
  intro h
  have hsubset :
      ∃ side : HexagonPlanarPairing,
        planarPairingSupport side ⊆ hexagonSupport :=
    (physical_targetAware_iff_exists_subset_of_compl_mem
      hexagonSupport planarPairingSupport physicalExterior hcomplement).1 h
  obtain ⟨side, hside⟩ := hsubset
  exact no_planarPairingSupport_subset side hside

/-! ## The parity-admissible adversary

The full set complement contains words which no Tait-coloured tangle can
realize, because every physical cut word has zero total Klein sum.  The
following refinement removes that easy objection. -/

/-- Total Klein colour on the six ports, written explicitly so the finite
checker has no enumeration-order dependency. -/
def boundarySum (word : HexagonTaitWord) : Color :=
  (word 0).1 + (word 1).1 + (word 2).1 +
    (word 3).1 + (word 4).1 + (word 5).1

/-- The universal parity language for a six-edge cut. -/
def parityAdmissible : Set HexagonTaitWord :=
  {word | boundarySum word = 0}

/-- Every word accepted by a pairing cap obeys the cut-parity equation. -/
private theorem boundarySum_eq_zero_of_compatible :
    ∀ side : HexagonPlanarPairing, ∀ word : HexagonTaitWord,
      side.Compatible (rawWord word) → boundarySum word = 0 := by
  decide

theorem planarPairingSupport_subset_parityAdmissible :
    ∀ side : HexagonPlanarPairing,
      planarPairingSupport side ⊆ parityAdmissible := by
  intro side word hword
  exact boundarySum_eq_zero_of_compatible side word hword

/-- The parity-admissible part of the hexagon complement. -/
def parityAdversary : Set HexagonTaitWord :=
  parityAdmissible \ hexagonSupport

theorem parityAdversary_subset_parityAdmissible :
    parityAdversary ⊆ parityAdmissible := by
  intro word hword
  exact hword.1

theorem parityAdversary_disjoint_hexagonSupport :
    Disjoint parityAdversary hexagonSupport := by
  rw [Set.disjoint_left]
  intro word hword hhexagon
  exact hword.2 hhexagon

/-- The parity-admissible adversary still meets every planar pairing cap. -/
theorem parityAdversary_meets_every_planarPairing :
    ∀ side : HexagonPlanarPairing,
      ¬ Disjoint parityAdversary (planarPairingSupport side) := by
  intro side hdisjoint
  obtain ⟨word, hpairing, hhexagon⟩ :=
    every_planarPairing_accepts_nonextension side
  have hparity : word ∈ parityAdmissible :=
    planarPairingSupport_subset_parityAdmissible side hpairing
  rw [Set.disjoint_left] at hdisjoint
  exact hdisjoint ⟨hparity, hhexagon⟩ hpairing

/-- **Parity does not rescue target-aware pairing reduction.**  Even after
restricting the exterior language to genuine words with zero total colour,
there is one zero exterior support against which every pairing cap fails. -/
theorem no_parityRestricted_targetAware_planarPairing_reduction :
    ¬ (∀ exterior : Set HexagonTaitWord,
        exterior ⊆ parityAdmissible →
        Disjoint exterior hexagonSupport →
          ∃ side : HexagonPlanarPairing,
            Disjoint exterior (planarPairingSupport side)) := by
  intro h
  obtain ⟨side, hside⟩ :=
    h parityAdversary parityAdversary_subset_parityAdmissible
      parityAdversary_disjoint_hexagonSupport
  exact parityAdversary_meets_every_planarPairing side hside

end GoertzelV24HexagonPairingTargetAwareBoundary

end Mettapedia.GraphTheory.FourColor
