import KrennOfficialGauge

/-!
The semantic vertex symmetry used by the
`X = {01,02,03,04,15}` finite support orbit.

Only vertices 2, 3, and 4 move.  Making the six permutations a finite type
keeps the proof source-faithful: the `pm15` identity is checked for precisely
the group used by the exact orbit census, without importing a generic
perfect-matching enumeration theorem.
-/

namespace Krenn.X5Symmetry

open MonochromaticQuantumGraph
open Krenn.OfficialBridge

inductive LeafSymmetry where
  | identity
  | swap23
  | swap24
  | swap34
  | cycle234
  | cycle243
deriving DecidableEq, Fintype

inductive ColourSymmetry where
  | p012
  | p021
  | p102
  | p120
  | p201
  | p210
deriving DecidableEq, Fintype

def leafEquiv : LeafSymmetry → Equiv.Perm (Fin 6)
  | .identity => Equiv.refl _
  | .swap23 => Equiv.swap 2 3
  | .swap24 => Equiv.swap 2 4
  | .swap34 => Equiv.swap 3 4
  | .cycle234 => (Equiv.swap 2 3).trans (Equiv.swap 3 4)
  | .cycle243 => (Equiv.swap 3 4).trans (Equiv.swap 2 3)

def colourEquiv : ColourSymmetry → Equiv.Perm (Fin 3)
  | .p012 => Equiv.refl _
  | .p021 => Equiv.swap 1 2
  | .p102 => Equiv.swap 0 1
  | .p120 => (Equiv.swap 0 1).trans (Equiv.swap 0 2)
  | .p201 => (Equiv.swap 0 2).trans (Equiv.swap 0 1)
  | .p210 => Equiv.swap 0 2

def LeafSymmetry.inverse : LeafSymmetry → LeafSymmetry
  | .identity => .identity
  | .swap23 => .swap23
  | .swap24 => .swap24
  | .swap34 => .swap34
  | .cycle234 => .cycle243
  | .cycle243 => .cycle234

def ColourSymmetry.inverse : ColourSymmetry → ColourSymmetry
  | .p012 => .p012
  | .p021 => .p021
  | .p102 => .p102
  | .p120 => .p201
  | .p201 => .p120
  | .p210 => .p210

theorem leafEquiv_inverse (leaf : LeafSymmetry) :
    leafEquiv leaf.inverse = (leafEquiv leaf).symm := by
  fin_cases leaf
  all_goals
    ext vertex
    fin_cases vertex <;> decide

theorem colourEquiv_inverse (colour : ColourSymmetry) :
    colourEquiv colour.inverse = (colourEquiv colour).symm := by
  fin_cases colour
  all_goals
    ext value
    fin_cases value <;> decide

/-- The six ordered off-diagonal colour pairs, in the exact order used by
the historical `itertools.product` case generator. -/
def offDiagonalColours : Fin 6 → Fin 3 × Fin 3 :=
  ![(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)]

def supportEndpoints : Fin 5 → Fin 6 × Fin 6 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 5)]

abbrev CaseChoice := Fin 5 → Fin 6

def supportEntry (choice : CaseChoice) (slot : Fin 5) : EdgeN 6 3 :=
  MonochromaticQuantumGraph.mkEdge
    (supportEndpoints slot).1 (supportEndpoints slot).2
    (offDiagonalColours (choice slot)).1
    (offDiagonalColours (choice slot)).2

/-- Action of a colour permutation on the six ordered off-diagonal pairs. -/
def colourChoiceAction : ColourSymmetry → Fin 6 → Fin 6
  | .p012 => ![0, 1, 2, 3, 4, 5]
  | .p021 => ![1, 0, 4, 5, 2, 3]
  | .p102 => ![2, 3, 0, 1, 5, 4]
  | .p120 => ![3, 2, 5, 4, 0, 1]
  | .p201 => ![4, 5, 1, 0, 3, 2]
  | .p210 => ![5, 4, 3, 2, 1, 0]

/-- For a target support slot, return the source slot under the leaf action. -/
def leafSourceSlot : LeafSymmetry → Fin 5 → Fin 5
  | .identity => ![0, 1, 2, 3, 4]
  | .swap23 => ![0, 2, 1, 3, 4]
  | .swap24 => ![0, 3, 2, 1, 4]
  | .swap34 => ![0, 1, 3, 2, 4]
  | .cycle234 => ![0, 2, 3, 1, 4]
  | .cycle243 => ![0, 3, 1, 2, 4]

def actCase (leaf : LeafSymmetry) (colour : ColourSymmetry)
    (choice : CaseChoice) : CaseChoice := fun target =>
  colourChoiceAction colour (choice (leafSourceSlot leaf target))

theorem colourChoiceAction_correct (colour : ColourSymmetry) (pair : Fin 6) :
    offDiagonalColours (colourChoiceAction colour pair) =
      (colourEquiv colour (offDiagonalColours pair).1,
        colourEquiv colour (offDiagonalColours pair).2) := by
  fin_cases colour <;> fin_cases pair <;>
    decide

theorem colourChoiceAction_inverse (colour : ColourSymmetry) (pair : Fin 6) :
    (colourEquiv colour.inverse
        (offDiagonalColours (colourChoiceAction colour pair)).1,
      colourEquiv colour.inverse
        (offDiagonalColours (colourChoiceAction colour pair)).2) =
      offDiagonalColours pair := by
  fin_cases colour <;> fin_cases pair <;>
    decide

@[simp] theorem colourChoiceAction_inverse_left
    (colour : ColourSymmetry) (pair : Fin 6) :
    colourEquiv colour.inverse
        (offDiagonalColours (colourChoiceAction colour pair)).1 =
      (offDiagonalColours pair).1 := by
  exact congrArg Prod.fst (colourChoiceAction_inverse colour pair)

@[simp] theorem colourChoiceAction_inverse_right
    (colour : ColourSymmetry) (pair : Fin 6) :
    colourEquiv colour.inverse
        (offDiagonalColours (colourChoiceAction colour pair)).2 =
      (offDiagonalColours pair).2 := by
  exact congrArg Prod.snd (colourChoiceAction_inverse colour pair)

theorem leafSourceSlot_correct (leaf : LeafSymmetry) (target : Fin 5) :
    let source := leafSourceSlot leaf target
    (leafEquiv leaf (supportEndpoints source).1,
      leafEquiv leaf (supportEndpoints source).2) = supportEndpoints target := by
  fin_cases leaf <;> fin_cases target <;>
    decide

theorem leafInverse_target (leaf : LeafSymmetry) (target : Fin 5) :
    (leafEquiv leaf.inverse (supportEndpoints target).1,
      leafEquiv leaf.inverse (supportEndpoints target).2) =
      supportEndpoints (leafSourceSlot leaf target) := by
  fin_cases leaf <;> fin_cases target <;>
    decide

/-- Pull a weight system back along a vertex permutation.  Reversing the
ordered endpoints also reverses the two channel colours. -/
def relabelVertices (sigma : Equiv.Perm (Fin 6))
    (W : WeightsN 6 3 ℂ) : WeightsN 6 3 ℂ := fun edge =>
  if sigma edge.u < sigma edge.v then
    W (MonochromaticQuantumGraph.mkEdge
      (sigma edge.u) (sigma edge.v) edge.i edge.j)
  else
    W (MonochromaticQuantumGraph.mkEdge
      (sigma edge.v) (sigma edge.u) edge.j edge.i)

set_option maxHeartbeats 5000000 in
theorem pm15_relabelLeaf (symmetry : LeafSymmetry)
    (W : WeightsN 6 3 ℂ) (colouring : Fin 6 → Fin 3) :
    pm15 (relabelVertices (leafEquiv symmetry) W) colouring =
      pm15 W (fun vertex => colouring ((leafEquiv symmetry).symm vertex)) := by
  fin_cases symmetry <;>
    simp [pm15, w, relabelVertices, leafEquiv, Equiv.swap_apply_def,
      MonochromaticQuantumGraph.mkEdge] <;>
    ring

theorem pmSumN_relabelLeaf (symmetry : LeafSymmetry)
    (W : WeightsN 6 3 ℂ) (colouring : Fin 6 → Fin 3) :
    pmSumN 6 3 (relabelVertices (leafEquiv symmetry) W) colouring =
      pmSumN 6 3 W
        (fun vertex => colouring ((leafEquiv symmetry).symm vertex)) := by
  rw [official_pmSum_eq_pm15, pm15_relabelLeaf, official_pmSum_eq_pm15]

theorem allEqual_relabelLeaf_iff (symmetry : LeafSymmetry)
    (colouring : Fin 6 → Fin 3) :
    allEqual (fun vertex => colouring ((leafEquiv symmetry).symm vertex)) ↔
      allEqual colouring := by
  fin_cases symmetry <;>
    simp [allEqual, allEqualList, vertices, leafEquiv,
      Equiv.swap_apply_def] <;> aesop

theorem eqSystemN_relabelLeaf (symmetry : LeafSymmetry)
    (W : WeightsN 6 3 ℂ) (hW : EqSystemN 6 3 W) :
    EqSystemN 6 3 (relabelVertices (leafEquiv symmetry) W) := by
  intro colouring
  rw [pmSumN_relabelLeaf, hW]
  exact if_congr (allEqual_relabelLeaf_iff symmetry colouring) rfl rfl

theorem relabelVertices_entry_eq_zero_iff
    (sigma : Equiv.Perm (Fin 6)) (W : WeightsN 6 3 ℂ)
    (edge : EdgeN 6 3) :
    relabelVertices sigma W edge = 0 ↔
      (if sigma edge.u < sigma edge.v then
        W (MonochromaticQuantumGraph.mkEdge
          (sigma edge.u) (sigma edge.v) edge.i edge.j)
      else
        W (MonochromaticQuantumGraph.mkEdge
          (sigma edge.v) (sigma edge.u) edge.j edge.i)) = 0 := by
  rfl

/-- Transport an official weight system in the direction of `actCase`: an
old selected channel becomes the corresponding selected channel of the acted
case. -/
def transportToAction (leaf : LeafSymmetry) (colour : ColourSymmetry)
    (W : WeightsN 6 3 ℂ) : WeightsN 6 3 ℂ :=
  Krenn.OfficialGauge.relabelColours (colourEquiv colour.inverse)
    (relabelVertices (leafEquiv leaf.inverse) W)

theorem eqSystemN_transportToAction (leaf : LeafSymmetry)
    (colour : ColourSymmetry) (W : WeightsN 6 3 ℂ)
    (hW : EqSystemN 6 3 W) :
    EqSystemN 6 3 (transportToAction leaf colour W) := by
  exact Krenn.OfficialGauge.eqSystemN_relabelColours
    (colourEquiv colour.inverse) _
    (eqSystemN_relabelLeaf leaf.inverse W hW)

theorem transportToAction_supportEntry (leaf : LeafSymmetry)
    (colour : ColourSymmetry) (W : WeightsN 6 3 ℂ)
    (choice : CaseChoice) (target : Fin 5) :
    transportToAction leaf colour W
        (supportEntry (actCase leaf colour choice) target) =
      W (supportEntry choice (leafSourceSlot leaf target)) := by
  fin_cases leaf <;> fin_cases target <;>
    simp [transportToAction, Krenn.OfficialGauge.relabelColours,
      relabelVertices, supportEntry, actCase, leafSourceSlot,
      supportEndpoints, LeafSymmetry.inverse, leafEquiv,
      Equiv.swap_apply_def, MonochromaticQuantumGraph.mkEdge]

#print axioms Krenn.X5Symmetry.pm15_relabelLeaf
#print axioms Krenn.X5Symmetry.eqSystemN_relabelLeaf
#print axioms Krenn.X5Symmetry.transportToAction_supportEntry

end Krenn.X5Symmetry
