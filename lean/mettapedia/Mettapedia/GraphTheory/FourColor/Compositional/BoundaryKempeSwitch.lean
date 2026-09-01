import Mettapedia.GraphTheory.FourColor.GoertzelV24PortTanglePhysicalKempeClosure

/-!
# Boundary support under physical Kempe switches

The exact boundary support of a finite cubic port tangle is invariant under
switching any union of its literal bichromatic components.  This statement is
independent of the number or cyclic arrangement of the ports; planarity enters
only later, when the component pairing is constrained by a boundary order.

The definitions in this file form the arity-generic semantic layer beneath the
older six-port boundary wrapper.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace BoundaryKempeSwitch

open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24PortTangleCommonKempeWeb
open GoertzelV24PortTangleCutParity
open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTanglePhysicalKempeClosure

universe u v

variable {V I P : Type u}
  [Fintype V] [Fintype I] [Fintype P]
  [DecidableEq V] [DecidableEq I] [DecidableEq P]

/-- Switch a selected set of ports by one pair of nonzero Tait colours. -/
def switchBoundaryWord
    (word : P → {color : Color // color ≠ 0})
    (pair : TaitColorPair) (selected : Finset P) :
    P → {color : Color // color ≠ 0} :=
  fun port =>
    if port ∈ selected then
      ⟨Color.swap pair.colors.1 pair.colors.2 (word port).1,
        pairSwap_ne_zero pair (word port).2⟩
    else word port

/-- A selected port set is a union of complete physical bichromatic
components. -/
def IsPhysicalComponentUnion
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair) (selected : Finset P) : Prop :=
  ∀ port, port ∈ selected ↔
    physicalMate T hcubic coloring hproper pair port ∈ selected

/-- Switching a union of literal bichromatic components preserves the exact
boundary support of a finite cubic port tangle. -/
theorem switchBoundaryWord_mem_taitSupport
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair) (selected : Finset P)
    (hunion : IsPhysicalComponentUnion T hcubic coloring hproper pair selected) :
    switchBoundaryWord (properBoundaryWord coloring hproper) pair selected ∈
      taitSupport T := by
  let selectedDarts := selectedPhysicalComponents T coloring pair selected
  let region := selectedPhysicalComponents_kempeRegion
    T coloring pair selected
  let switched := switchRegion T coloring pair selectedDarts region
  let switchedProper := switchRegion_isProper
    T coloring hproper pair selectedDarts region
  have hmem : properBoundaryWord switched switchedProper ∈ taitSupport T :=
    properBoundaryWord_switchRegion_mem_taitSupport
      T coloring hproper pair selectedDarts region
  have hboundary := properBoundaryWord_switchRegion_eq
    T coloring hproper pair selectedDarts region
  change properBoundaryWord
    (switchRegion T coloring pair selectedDarts region) _ ∈ taitSupport T at hmem
  rw [hboundary] at hmem
  have hwords : switchBoundaryWord (properBoundaryWord coloring hproper)
      pair selected =
      (fun port =>
        if port ∈ selectedPorts selectedDarts then
          ⟨Color.swap pair.colors.1 pair.colors.2
              (properBoundaryWord coloring hproper port).1,
            pairSwap_ne_zero pair
              (properBoundaryWord coloring hproper port).2⟩
        else properBoundaryWord coloring hproper port) := by
    funext port
    have hselectedDart : selectedDarts (Sum.inr port) ↔
        port ∈ selected ∧ pairActiveDart coloring pair (Sum.inr port) :=
      selectedPhysicalComponents_boundary_iff T hcubic coloring hproper pair
        selected hunion port
    have hselectedPort : port ∈ selectedPorts selectedDarts ↔
        port ∈ selected ∧ pairActiveDart coloring pair (Sum.inr port) := by
      simpa [selectedPorts] using hselectedDart
    by_cases hport : port ∈ selected
    · by_cases hactive : pairActiveDart coloring pair (Sum.inr port)
      · simp [switchBoundaryWord, hport, hselectedPort, hactive]
      · have hswap : Color.swap pair.colors.1 pair.colors.2
            (properBoundaryWord coloring hproper port).1 =
            (properBoundaryWord coloring hproper port).1 :=
          pairSwap_eq_self_of_not_active pair _ hactive
        apply Subtype.ext
        simpa [switchBoundaryWord, hport, hselectedPort, hactive] using hswap
    · simp [switchBoundaryWord, hport, hselectedPort]
  rw [hwords]
  exact hmem

/-! ## Boundary coordinates -/

variable {Q : Type v} [Fintype Q] [DecidableEq Q]

/-- Read the exact physical support in any chosen boundary coordinates. -/
def supportInCoordinates (order : Q ≃ P) (T : PortTangle V I P) :
    Set (Q → {color : Color // color ≠ 0}) :=
  {boundary | (fun port => boundary (order.symm port)) ∈ taitSupport T}

/-- Read one proper physical colouring in chosen boundary coordinates. -/
def properBoundaryWordInCoordinates
    (order : Q ≃ P) {T : PortTangle V I P}
    (coloring : Coloring T) (hproper : IsProper coloring) :
    Q → {color : Color // color ≠ 0} :=
  fun coordinate => properBoundaryWord coloring hproper (order coordinate)

theorem properBoundaryWordInCoordinates_mem_support
    (order : Q ≃ P) (T : PortTangle V I P)
    (coloring : Coloring T) (hproper : IsProper coloring) :
    properBoundaryWordInCoordinates order coloring hproper ∈
      supportInCoordinates order T := by
  have hmem := properBoundaryWord_mem_taitSupport T coloring hproper
  change (fun port =>
    properBoundaryWordInCoordinates order coloring hproper
      (order.symm port)) ∈ taitSupport T
  convert hmem using 1
  funext port
  simp [properBoundaryWordInCoordinates]

/-- Read the literal physical component mate in chosen coordinates. -/
noncomputable def physicalMateInCoordinates
    (order : Q ≃ P) (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair) : Q → Q :=
  fun coordinate => order.symm
    (physicalMate T hcubic coloring hproper pair (order coordinate))

/-- Transport a selected coordinate set to the physical port carrier. -/
def selectedPhysicalPorts
    (order : Q ≃ P) (selected : Finset Q) : Finset P :=
  selected.map order.toEmbedding

@[simp]
theorem mem_selectedPhysicalPorts_iff
    (order : Q ≃ P) (selected : Finset Q) (port : P) :
    port ∈ selectedPhysicalPorts order selected ↔
      order.symm port ∈ selected := by
  simp [selectedPhysicalPorts]

/-- A component-union switch remains in the exact support after arbitrary
reindexing of the boundary ports. -/
theorem switchBoundaryWord_mem_supportInCoordinates
    (order : Q ≃ P) (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair) (selected : Finset Q)
    (hunion : ∀ coordinate, coordinate ∈ selected ↔
      physicalMateInCoordinates order T hcubic coloring hproper pair coordinate ∈
        selected) :
    switchBoundaryWord
        (properBoundaryWordInCoordinates order coloring hproper) pair selected ∈
      supportInCoordinates order T := by
  let physical := selectedPhysicalPorts order selected
  have hphysical : IsPhysicalComponentUnion
      T hcubic coloring hproper pair physical := by
    intro port
    simpa [physical, physicalMateInCoordinates] using
      hunion (order.symm port)
  have hmem := switchBoundaryWord_mem_taitSupport
    T hcubic coloring hproper pair physical hphysical
  change (fun port =>
    switchBoundaryWord
      (properBoundaryWordInCoordinates order coloring hproper) pair selected
      (order.symm port)) ∈ taitSupport T
  convert hmem using 1
  funext port
  by_cases hselected : order.symm port ∈ selected
  · simp [switchBoundaryWord, properBoundaryWordInCoordinates,
      physical, hselected]
  · simp [switchBoundaryWord, properBoundaryWordInCoordinates,
      physical, hselected]

end BoundaryKempeSwitch

end Mettapedia.GraphTheory.FourColor.Compositional
