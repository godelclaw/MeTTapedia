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

end GoertzelV24HexagonPairingTargetAwareBoundary

end Mettapedia.GraphTheory.FourColor
