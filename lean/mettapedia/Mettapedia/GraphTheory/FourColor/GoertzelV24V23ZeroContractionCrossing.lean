import Mathlib.Tactic
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality
import Mettapedia.GraphTheory.FourColor.GoertzelV24ZeroContractionChirality

/-!
# The v23 zero-contraction does not separate the two colour-pair systems

The CAP5 argument in the original v23 manuscript contracts every edge of one
Tait colour and then treats the other two bichromatic families as mutually
disjoint embedded arc systems.  Edge-disjointness is not enough for that
conclusion: contraction can make the two families meet at the new vertex.

The tetrahedron is the smallest explicit witness.  Give opposite edges the
same Tait colour and contract both red edges.  At either resulting degree-four
vertex the incident colours occur blue, purple, blue, purple.  Thus the blue
through-pair and the purple through-pair have alternating endpoints in the
vertex link.  Each family is noncrossing by itself, but the two families cross
one another at the contracted point.

Both the source tetrahedron and the contracted rotation table are checked
below.  This refutes only the cross-family disjointness assertion; it does not
affect the separately proved noncrossing theorem for one fixed Kempe pair.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24V23ZeroContractionCrossing

open GoertzelV24CurvatureScope
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24ZeroContractionChirality

/-! ## The spherical Tait-coloured tetrahedron -/

inductive TetraVertex
  | a | b | c | d
  deriving DecidableEq, Repr

inductive TetraEdge
  | ab | ac | ad | bc | bd | cd
  deriving DecidableEq, Repr

inductive TetraDart
  | abA | abB
  | acA | acC
  | adA | adD
  | bcB | bcC
  | bdB | bdD
  | cdC | cdD
  deriving DecidableEq, Repr

instance : Fintype TetraVertex :=
  ⟨{.a, .b, .c, .d}, by intro vertex; cases vertex <;> simp⟩

instance : Fintype TetraEdge :=
  ⟨{.ab, .ac, .ad, .bc, .bd, .cd}, by intro edge; cases edge <;> simp⟩

instance : Fintype TetraDart :=
  ⟨{.abA, .abB, .acA, .acC, .adA, .adD,
    .bcB, .bcC, .bdB, .bdD, .cdC, .cdD}, by
      intro dart
      cases dart <;> simp⟩

def tetraEdgeOf : TetraDart → TetraEdge
  | .abA | .abB => .ab
  | .acA | .acC => .ac
  | .adA | .adD => .ad
  | .bcB | .bcC => .bc
  | .bdB | .bdD => .bd
  | .cdC | .cdD => .cd

def tetraVertOf : TetraDart → TetraVertex
  | .abA | .acA | .adA => .a
  | .abB | .bcB | .bdB => .b
  | .acC | .bcC | .cdC => .c
  | .adD | .bdD | .cdD => .d

def tetraAlphaFn : TetraDart → TetraDart
  | .abA => .abB | .abB => .abA
  | .acA => .acC | .acC => .acA
  | .adA => .adD | .adD => .adA
  | .bcB => .bcC | .bcC => .bcB
  | .bdB => .bdD | .bdD => .bdB
  | .cdC => .cdD | .cdD => .cdC

def tetraAlpha : Equiv.Perm TetraDart where
  toFun := tetraAlphaFn
  invFun := tetraAlphaFn
  left_inv := by intro dart; cases dart <;> rfl
  right_inv := by intro dart; cases dart <;> rfl

/-- The standard oriented tetrahedral rotation. -/
def tetraRhoFn : TetraDart → TetraDart
  | .abA => .acA | .acA => .adA | .adA => .abA
  | .abB => .bdB | .bdB => .bcB | .bcB => .abB
  | .acC => .bcC | .bcC => .cdC | .cdC => .acC
  | .adD => .cdD | .cdD => .bdD | .bdD => .adD

def tetraRhoInvFn : TetraDart → TetraDart
  | .abA => .adA | .acA => .abA | .adA => .acA
  | .abB => .bcB | .bdB => .abB | .bcB => .bdB
  | .acC => .cdC | .bcC => .acC | .cdC => .bcC
  | .adD => .bdD | .cdD => .adD | .bdD => .cdD

def tetraRho : Equiv.Perm TetraDart where
  toFun := tetraRhoFn
  invFun := tetraRhoInvFn
  left_inv := by intro dart; cases dart <;> rfl
  right_inv := by intro dart; cases dart <;> rfl

def tetraRotationSystem : RotationSystem TetraVertex TetraEdge where
  D := TetraDart
  edgeOf := tetraEdgeOf
  vertOf := tetraVertOf
  alpha := tetraAlpha
  rho := tetraRho
  alpha_involutive := by intro dart; cases dart <;> rfl
  alpha_fixfree := by intro dart; cases dart <;> decide
  edge_alpha := by intro dart; cases dart <;> rfl
  edge_fiber_two := by intro edge; cases edge <;> decide
  vert_rho := by intro dart; cases dart <;> rfl
  outer := .abA
  no_self_loops := by intro dart; cases dart <;> decide

def tetraEndpoints : TetraEdge → Finset TetraVertex
  | .ab => {.a, .b}
  | .ac => {.a, .c}
  | .ad => {.a, .d}
  | .bc => {.b, .c}
  | .bd => {.b, .d}
  | .cd => {.c, .d}

@[simp] theorem tetra_endpoints_eq (edge : TetraEdge) :
    tetraRotationSystem.endpoints edge = tetraEndpoints edge := by
  cases edge <;> decide

theorem tetra_isCubic : tetraRotationSystem.IsCubic := by
  intro vertex
  cases vertex <;> decide

theorem tetra_faceCycleCount_eq_four :
    (faceCycleLengths tetraRotationSystem).card = 4 := by
  decide

theorem tetra_orbitFaceCount_eq_four :
    Fintype.card (OrbitFace tetraRotationSystem) = 4 := by
  rw [card_orbitFace_eq_faceCycleLengths_card]
  exact tetra_faceCycleCount_eq_four

/-- The explicit rotation table is a cellular embedding of the tetrahedron on
the sphere. -/
def tetraSpherical : OrbitSphericalCubicMapData tetraRotationSystem where
  cubic := tetra_isCubic
  euler := by
    rw [tetra_orbitFaceCount_eq_four]
    decide

theorem tetra_primalConnected :
    (rotationPrimalGraph tetraRotationSystem).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨TetraVertex.a, ?_⟩
  intro vertex
  cases vertex
  · rfl
  · exact SimpleGraph.Adj.reachable ⟨TetraDart.abA, rfl, rfl⟩
  · exact SimpleGraph.Adj.reachable ⟨TetraDart.acA, rfl, rfl⟩
  · exact SimpleGraph.Adj.reachable ⟨TetraDart.adA, rfl, rfl⟩

theorem tetra_euler_nat :
    Fintype.card TetraVertex +
        Fintype.card (OrbitFace tetraRotationSystem) =
      Fintype.card TetraEdge + 2 := by
  rw [tetra_orbitFaceCount_eq_four]
  decide

/-- Opposite tetrahedral edges receive the same nonzero Tait colour. -/
def tetraColor : TetraEdge → Color
  | .ab | .cd => red
  | .ac | .bd => blue
  | .ad | .bc => purple

theorem tetra_not_adjacent_of_same_color {left right : TetraEdge}
    (hcolor : tetraColor left = tetraColor right) :
    ¬ tetraRotationSystem.edgeAdjacencyGraph.Adj left right := by
  intro hadjacent
  rcases (tetraRotationSystem.edgeAdjacencyGraph_adj_iff).1 hadjacent with
    ⟨hne, vertex, hleft, hright⟩
  rw [tetra_endpoints_eq] at hleft hright
  cases left <;> cases right <;> cases vertex <;>
    simp_all [tetraColor, tetraEndpoints, red, blue, purple]

theorem tetra_taitColorable :
    RotationSystemTaitColorable tetraRotationSystem := by
  refine ⟨SimpleGraph.Coloring.mk tetraColor ?_, ?_⟩
  · intro left right hadjacent hcolor
    exact tetra_not_adjacent_of_same_color hcolor hadjacent
  · intro edge
    cases edge <;> decide

/-! ## The literal rotation table after contracting both red edges -/

inductive ContractVertex
  | centerAB | centerCD
  deriving DecidableEq, Repr

inductive ContractEdge
  | ac | ad | bc | bd
  deriving DecidableEq, Repr

inductive ContractDart
  | acZ | acC
  | adZ | adD
  | bcZ | bcC
  | bdZ | bdD
  deriving DecidableEq, Repr

instance : Fintype ContractVertex :=
  ⟨{.centerAB, .centerCD}, by intro vertex; cases vertex <;> simp⟩

instance : Fintype ContractEdge :=
  ⟨{.ac, .ad, .bc, .bd}, by intro edge; cases edge <;> simp⟩

instance : Fintype ContractDart :=
  ⟨{.acZ, .acC, .adZ, .adD, .bcZ, .bcC, .bdZ, .bdD}, by
      intro dart
      cases dart <;> simp⟩

def contractEdgeOf : ContractDart → ContractEdge
  | .acZ | .acC => .ac
  | .adZ | .adD => .ad
  | .bcZ | .bcC => .bc
  | .bdZ | .bdD => .bd

def contractVertOf : ContractDart → ContractVertex
  | .acZ | .adZ | .bcZ | .bdZ => .centerAB
  | .acC | .adD | .bcC | .bdD => .centerCD

def contractAlphaFn : ContractDart → ContractDart
  | .acZ => .acC | .acC => .acZ
  | .adZ => .adD | .adD => .adZ
  | .bcZ => .bcC | .bcC => .bcZ
  | .bdZ => .bdD | .bdD => .bdZ

def contractAlpha : Equiv.Perm ContractDart where
  toFun := contractAlphaFn
  invFun := contractAlphaFn
  left_inv := by intro dart; cases dart <;> rfl
  right_inv := by intro dart; cases dart <;> rfl

/-- Removing `ab` and `cd` joins each pair of punctured vertex rotations.
The two center orders are `ac, ad, bd, bc` and `ac, bc, bd, ad`. -/
def contractRhoFn : ContractDart → ContractDart
  | .acZ => .adZ | .adZ => .bdZ | .bdZ => .bcZ | .bcZ => .acZ
  | .acC => .bcC | .bcC => .bdD | .bdD => .adD | .adD => .acC

def contractRhoInvFn : ContractDart → ContractDart
  | .acZ => .bcZ | .adZ => .acZ | .bdZ => .adZ | .bcZ => .bdZ
  | .acC => .adD | .bcC => .acC | .bdD => .bcC | .adD => .bdD

def contractedRotationSystem : RotationSystem ContractVertex ContractEdge where
  D := ContractDart
  edgeOf := contractEdgeOf
  vertOf := contractVertOf
  alpha :=
    { toFun := contractAlphaFn
      invFun := contractAlphaFn
      left_inv := by intro dart; cases dart <;> rfl
      right_inv := by intro dart; cases dart <;> rfl }
  rho :=
    { toFun := contractRhoFn
      invFun := contractRhoInvFn
      left_inv := by intro dart; cases dart <;> rfl
      right_inv := by intro dart; cases dart <;> rfl }
  alpha_involutive := by intro dart; cases dart <;> rfl
  alpha_fixfree := by intro dart; cases dart <;> decide
  edge_alpha := by intro dart; cases dart <;> rfl
  edge_fiber_two := by intro edge; cases edge <;> decide
  vert_rho := by intro dart; cases dart <;> rfl
  outer := .acZ
  no_self_loops := by intro dart; cases dart <;> decide

theorem contracted_faceCycleCount_eq_four :
    (faceCycleLengths contractedRotationSystem).card = 4 := by
  decide

theorem contracted_orbitFaceCount_eq_four :
    Fintype.card (OrbitFace contractedRotationSystem) = 4 := by
  rw [card_orbitFace_eq_faceCycleLengths_card]
  exact contracted_faceCycleCount_eq_four

/-- Although the contracted map is no longer cubic, its literal rotation
table is still spherical: `2 - 4 + 4 = 2`. -/
theorem contracted_euler :
    Fintype.card ContractVertex +
        Fintype.card (OrbitFace contractedRotationSystem) =
      Fintype.card ContractEdge + 2 := by
  rw [contracted_orbitFaceCount_eq_four]
  decide

theorem contracted_primalConnected :
    (rotationPrimalGraph contractedRotationSystem).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨ContractVertex.centerAB, ?_⟩
  intro vertex
  cases vertex
  · rfl
  · exact SimpleGraph.Adj.reachable ⟨ContractDart.acZ, rfl, rfl⟩

def contractedColor : ContractEdge → Color
  | .ac | .bd => blue
  | .ad | .bc => purple

/-- Inclusion of the four surviving edges into the tetrahedron. -/
def remainingEdge : ContractEdge → TetraEdge
  | .ac => .ac
  | .ad => .ad
  | .bc => .bc
  | .bd => .bd

/-- Every contracted dart remembers the tetrahedral dart from which it came.
The four center darts remember whether they came from endpoint `a` or `b` of
the contracted red edge. -/
def uncontractDart : ContractDart → TetraDart
  | .acZ => .acA | .acC => .acC
  | .adZ => .adA | .adD => .adD
  | .bcZ => .bcB | .bcC => .bcC
  | .bdZ => .bdB | .bdD => .bdD

theorem uncontractDart_edge_not_red (dart : ContractDart) :
    tetraColor (tetraEdgeOf (uncontractDart dart)) ≠ red := by
  cases dart <;> decide

def contractDartOfRemaining :
    {dart : TetraDart // tetraColor (tetraEdgeOf dart) ≠ red} → ContractDart
  | ⟨.abA, h⟩ => (h rfl).elim
  | ⟨.abB, h⟩ => (h rfl).elim
  | ⟨.acA, _⟩ => .acZ
  | ⟨.acC, _⟩ => .acC
  | ⟨.adA, _⟩ => .adZ
  | ⟨.adD, _⟩ => .adD
  | ⟨.bcB, _⟩ => .bcZ
  | ⟨.bcC, _⟩ => .bcC
  | ⟨.bdB, _⟩ => .bdZ
  | ⟨.bdD, _⟩ => .bdD
  | ⟨.cdC, h⟩ => (h rfl).elim
  | ⟨.cdD, h⟩ => (h rfl).elim

/-- The contracted dart carrier is exactly the tetrahedral dart carrier with
the four darts of the two red edges removed. -/
def remainingDartEquiv :
    ContractDart ≃
      {dart : TetraDart // tetraColor (tetraEdgeOf dart) ≠ red} where
  toFun dart := ⟨uncontractDart dart, uncontractDart_edge_not_red dart⟩
  invFun := contractDartOfRemaining
  left_inv := by intro dart; cases dart <;> rfl
  right_inv := by
    rintro ⟨dart, hdart⟩
    cases dart <;>
      first | exact (hdart rfl).elim | rfl

theorem uncontractDart_edgeOf (dart : ContractDart) :
    tetraEdgeOf (uncontractDart dart) =
      remainingEdge (contractedRotationSystem.edgeOf dart) := by
  cases dart <;> rfl

theorem contractedColor_eq_tetraColor (edge : ContractEdge) :
    contractedColor edge = tetraColor (remainingEdge edge) := by
  cases edge <;> rfl

theorem uncontractDart_alpha (dart : ContractDart) :
    uncontractDart (contractedRotationSystem.alpha dart) =
      tetraRotationSystem.alpha (uncontractDart dart) := by
  cases dart <;> rfl

/-- First-return vertex rotation after deleting the contracted red edges.  If
the next tetrahedral dart is red, cross that edge and rotate once more;
otherwise take the ordinary next dart. -/
def skipContractedRed (dart : TetraDart) : TetraDart :=
  let next := tetraRotationSystem.rho dart
  if tetraColor (tetraRotationSystem.edgeOf next) = red then
    tetraRotationSystem.rho (tetraRotationSystem.alpha next)
  else
    next

/-- This is the exact combinatorial edge-contraction law for the displayed
rotation tables. -/
theorem uncontractDart_rho (dart : ContractDart) :
    uncontractDart (contractedRotationSystem.rho dart) =
      skipContractedRed (uncontractDart dart) := by
  cases dart <;> rfl

/-- The link of the contracted vertex in its positive cyclic order. -/
def centerDart : Fin 4 → ContractDart
  | 0 => .acZ
  | 1 => .adZ
  | 2 => .bdZ
  | 3 => .bcZ

theorem centerDart_rho (position : Fin 4) :
    contractedRotationSystem.rho (centerDart position) =
      centerDart ⟨(position.1 + 1) % 4, by omega⟩ := by
  fin_cases position <;> rfl

def centerColor (position : Fin 4) : Color :=
  contractedColor (contractedRotationSystem.edgeOf (centerDart position))

theorem center_colors_alternate :
    centerColor 0 = blue ∧ centerColor 1 = purple ∧
      centerColor 2 = blue ∧ centerColor 3 = purple := by
  decide

/-- The two occurrences of each surviving colour are paired through the
contracted point. -/
def sameColorMate : Fin 4 → Fin 4
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1

theorem sameColorMate_involutive (position : Fin 4) :
    sameColorMate (sameColorMate position) = position := by
  fin_cases position <;> rfl

theorem sameColorMate_fixfree (position : Fin 4) :
    sameColorMate position ≠ position := by
  fin_cases position <;> decide

theorem centerColor_sameColorMate (position : Fin 4) :
    centerColor (sameColorMate position) = centerColor position := by
  fin_cases position <;> rfl

/-- The blue pair `(0,2)` and purple pair `(1,3)` cross in the link of the
contracted vertex.  This is the precise failure of the v23 inference from
edge-disjointness to mutual topological disjointness. -/
theorem contracted_colour_pair_chords_cross :
    ChordsCross4 0 (sameColorMate 0) 1 (sameColorMate 1) := by
  decide

/-- Consumer-facing checked witness: contracting all red edges of a spherical,
properly Tait-coloured tetrahedron makes the two surviving colour-pair
through-connections alternate at a contracted point. -/
theorem exists_spherical_tait_zero_contraction_with_crossing_pair_systems :
    RotationSystemTaitColorable tetraRotationSystem ∧
      (Fintype.card TetraVertex +
          Fintype.card (OrbitFace tetraRotationSystem) =
        Fintype.card TetraEdge + 2) ∧
      (rotationPrimalGraph tetraRotationSystem).Connected ∧
      (Fintype.card ContractVertex +
          Fintype.card (OrbitFace contractedRotationSystem) =
        Fintype.card ContractEdge + 2) ∧
      (rotationPrimalGraph contractedRotationSystem).Connected ∧
      Nonempty (ContractDart ≃
        {dart : TetraDart // tetraColor (tetraEdgeOf dart) ≠ red}) ∧
      (∀ edge, contractedColor edge = tetraColor (remainingEdge edge)) ∧
      (∀ dart, uncontractDart (contractedRotationSystem.alpha dart) =
        tetraRotationSystem.alpha (uncontractDart dart)) ∧
      centerColor 0 = blue ∧ centerColor 2 = blue ∧
      centerColor 1 = purple ∧ centerColor 3 = purple ∧
      (∀ dart, uncontractDart (contractedRotationSystem.rho dart) =
        skipContractedRed (uncontractDart dart)) ∧
      ChordsCross4 0 (sameColorMate 0) 1 (sameColorMate 1) := by
  refine ⟨tetra_taitColorable, tetra_euler_nat, tetra_primalConnected,
    contracted_euler, contracted_primalConnected, ?_⟩
  exact ⟨⟨remainingDartEquiv⟩, contractedColor_eq_tetraColor,
    uncontractDart_alpha, by decide, by decide, by decide, by decide,
    uncontractDart_rho, contracted_colour_pair_chords_cross⟩

end GoertzelV24V23ZeroContractionCrossing

end Mettapedia.GraphTheory.FourColor
