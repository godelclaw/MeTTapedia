import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# A triangular-prism counterexample to the v23 annular spanning statement

Take the triangular prism as an annulus whose two triangular cycles are the
boundary components and whose three rectangular faces are internal.  All six
vertices lie on the boundary, so the source's Kirchhoff condition at interior
vertices is vacuous.  A vector supported on one spoke is therefore in the
boundary-zero space.

This file implements the source's Definition 4.8 literally, but allows *all*
proper Tait colorings rather than merely one Kempe closure.  A linear
functional annihilates every resulting face generator and is nonzero on the
chosen spoke vector.  Hence that boundary-zero vector is not in even this
larger generator span.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24V23TriangularPrismSpanningCounterexample

abbrev F₂ := ZMod 2
abbrev Edge := Fin 9
abbrev Color := Fin 3
abbrev Face := Fin 3
abbrev Pair := Fin 3
abbrev Coord := Fin 2
abbrev Coloring := Edge → Color
abbrev Chain := Edge → Coord → F₂

def next (index : Fin 3) : Fin 3 :=
  ⟨(index + 1) % 3, Nat.mod_lt _ (by omega)⟩

def previous (index : Fin 3) : Fin 3 :=
  ⟨(index + 2) % 3, Nat.mod_lt _ (by omega)⟩

def topEdge (index : Fin 3) : Edge := ⟨index, by omega⟩
def bottomEdge (index : Fin 3) : Edge := ⟨index + 3, by omega⟩
def spoke (index : Fin 3) : Edge := ⟨index + 6, by omega⟩

/-- Properness at the six cubic vertices of the triangular prism. -/
def Proper (coloring : Coloring) : Prop :=
  ∀ index : Fin 3,
    (coloring (topEdge (previous index)) ≠ coloring (topEdge index) ∧
      coloring (topEdge (previous index)) ≠ coloring (spoke index) ∧
      coloring (topEdge index) ≠ coloring (spoke index)) ∧
    (coloring (bottomEdge (previous index)) ≠ coloring (bottomEdge index) ∧
      coloring (bottomEdge (previous index)) ≠ coloring (spoke index) ∧
      coloring (bottomEdge index) ≠ coloring (spoke index))

/-- Rectangle `i` has top edge `i`, bottom edge `i`, and its two incident
spokes. -/
def OnFace (face : Face) (edge : Edge) : Bool :=
  decide (edge = topEdge face ∨ edge = bottomEdge face ∨
    edge = spoke face ∨ edge = spoke (next face))

/-- Pair 0 is `{0,1}`, pair 1 is `{0,2}`, and pair 2 is `{1,2}`. -/
def InPair (pair : Pair) (color : Color) : Bool :=
  decide ((pair = 0 ∧ (color = 0 ∨ color = 1)) ∨
  (pair = 1 ∧ (color = 0 ∨ color = 2)) ∨
  (pair = 2 ∧ (color = 1 ∨ color = 2)))

def thirdColor (pair : Pair) : Color :=
  if pair = 0 then 2 else if pair = 1 then 1 else 0

/-- Klein-four coordinates of the three nonzero colors. -/
def colorCoord (color : Color) (coord : Coord) : F₂ :=
  if color = 0 then
    if coord = 0 then 1 else 0
  else if color = 1 then
    if coord = 0 then 0 else 1
  else
    1

/-- The v23 Definition-4.8 face generator: the third-color coefficient on
exactly the face edges colored in the selected pair. -/
def generator (coloring : Coloring) (face : Face) (pair : Pair) : Chain :=
  fun edge coord =>
    if OnFace face edge && InPair pair (coloring edge) then
      colorCoord (thirdColor pair) coord
    else
      0

/-- We use every proper coloring, a superset of the Kempe closure appearing
in the source theorem. -/
def generatorSet : Set Chain :=
  {value | ∃ coloring face pair,
    Proper coloring ∧ value = generator coloring face pair}

def generatorSpan : Submodule F₂ Chain :=
  Submodule.span F₂ generatorSet

/-- Sum the first Klein coordinate on the three top edges and three spokes. -/
def separator : Chain →ₗ[F₂] F₂ where
  toFun value :=
    value 0 0 + value 1 0 + value 2 0 +
      value 6 0 + value 7 0 + value 8 0
  map_add' left right := by
    simp only [Pi.add_apply]
    ring
  map_smul' scalar value := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- In a three-element color set, the two missing colors at consecutive
vertices of a properly colored triangle are distinct. -/
theorem missingColors_distinct
    (before shared after firstMissing secondMissing : Color)
    (hBeforeShared : before ≠ shared)
    (hSharedAfter : shared ≠ after)
    (hBeforeAfter : before ≠ after)
    (hFirstBefore : firstMissing ≠ before)
    (hFirstShared : firstMissing ≠ shared)
    (hSecondShared : secondMissing ≠ shared)
    (hSecondAfter : secondMissing ≠ after) :
    firstMissing ≠ secondMissing := by
  fin_cases before <;> fin_cases shared <;> fin_cases after <;>
    fin_cases firstMissing <;> fin_cases secondMissing <;> simp_all

theorem face_top_spokes_pairwise
    (coloring : Coloring) (hproper : Proper coloring) (face : Face) :
    coloring (topEdge face) ≠ coloring (spoke face) ∧
    coloring (topEdge face) ≠ coloring (spoke (next face)) ∧
    coloring (spoke face) ≠ coloring (spoke (next face)) := by
  have h0 := hproper (0 : Fin 3)
  have h1 := hproper (1 : Fin 3)
  have h2 := hproper (2 : Fin 3)
  simp only [previous, topEdge, bottomEdge, spoke] at h0 h1 h2
  fin_cases face
  · simp only [topEdge, spoke, next]
    refine ⟨h0.1.2.2, h1.1.2.1, ?_⟩
    exact missingColors_distinct
      (coloring 2) (coloring 0) (coloring 1)
      (coloring 6) (coloring 7)
      h0.1.1 h1.1.1 h2.1.1.symm
      h0.1.2.1.symm h0.1.2.2.symm
      h1.1.2.1.symm h1.1.2.2.symm
  · simp only [topEdge, spoke, next]
    refine ⟨h1.1.2.2, h2.1.2.1, ?_⟩
    exact missingColors_distinct
      (coloring 0) (coloring 1) (coloring 2)
      (coloring 7) (coloring 8)
      h1.1.1 h2.1.1 h0.1.1.symm
      h1.1.2.1.symm h1.1.2.2.symm
      h2.1.2.1.symm h2.1.2.2.symm
  · simp only [topEdge, spoke, next]
    refine ⟨h2.1.2.2, h0.1.2.1, ?_⟩
    exact missingColors_distinct
      (coloring 1) (coloring 2) (coloring 0)
      (coloring 8) (coloring 6)
      h2.1.1 h0.1.1 h1.1.1.symm
      h2.1.2.1.symm h2.1.2.2.symm
      h0.1.2.1.symm h0.1.2.2.symm

/-- A color pair contains exactly two of three pairwise-distinct nonzero
colors, so adding its third-color coefficient three times conditionally gives
zero. -/
theorem selectedThree_sum_eq_zero
    (first second third : Color) (pair : Pair)
    (hFirstSecond : first ≠ second)
    (hFirstThird : first ≠ third)
    (hSecondThird : second ≠ third) :
    (if InPair pair first then colorCoord (thirdColor pair) 0 else 0) +
      (if InPair pair second then colorCoord (thirdColor pair) 0 else 0) +
      (if InPair pair third then colorCoord (thirdColor pair) 0 else 0) = 0 := by
  fin_cases first <;> fin_cases second <;> fin_cases third <;>
    fin_cases pair <;> simp_all [InPair, thirdColor, colorCoord] <;> decide

/-- Every source face generator from every proper prism coloring lies in the
kernel of the separator. -/
theorem separator_generator_eq_zero
    (coloring : Coloring) (hproper : Proper coloring)
    (face : Face) (pair : Pair) :
    separator (generator coloring face pair) = 0 := by
  obtain ⟨hfirst, hsecond, hthird⟩ :=
    face_top_spokes_pairwise coloring hproper face
  have hsum := selectedThree_sum_eq_zero
    (coloring (topEdge face)) (coloring (spoke face))
    (coloring (spoke (next face))) pair hfirst hsecond hthird
  fin_cases face
  · simp only [topEdge, spoke, next] at hsum
    calc
      separator (generator coloring 0 pair) =
          (if InPair pair (coloring 0) then colorCoord (thirdColor pair) 0 else 0) +
          (if InPair pair (coloring 6) then colorCoord (thirdColor pair) 0 else 0) +
          (if InPair pair (coloring 7) then colorCoord (thirdColor pair) 0 else 0) := by
            simp [separator, generator, OnFace, topEdge, bottomEdge, spoke, next]
      _ = 0 := hsum
  · simp only [topEdge, spoke, next] at hsum
    calc
      separator (generator coloring 1 pair) =
          (if InPair pair (coloring 1) then colorCoord (thirdColor pair) 0 else 0) +
          (if InPair pair (coloring 7) then colorCoord (thirdColor pair) 0 else 0) +
          (if InPair pair (coloring 8) then colorCoord (thirdColor pair) 0 else 0) := by
            simp [separator, generator, OnFace, topEdge, bottomEdge, spoke, next]
      _ = 0 := hsum
  · simp only [topEdge, spoke, next] at hsum
    calc
      separator (generator coloring 2 pair) =
          (if InPair pair (coloring 2) then colorCoord (thirdColor pair) 0 else 0) +
          (if InPair pair (coloring 8) then colorCoord (thirdColor pair) 0 else 0) +
          (if InPair pair (coloring 6) then colorCoord (thirdColor pair) 0 else 0) := by
            simp [separator, generator, OnFace, topEdge, bottomEdge, spoke, next]
            ring
      _ = 0 := hsum

theorem generatorSpan_le_separator_ker :
    generatorSpan ≤ LinearMap.ker separator := by
  apply Submodule.span_le.mpr
  intro value hvalue
  rcases hvalue with ⟨coloring, face, pair, hproper, rfl⟩
  exact LinearMap.mem_ker.mpr
    (separator_generator_eq_zero coloring hproper face pair)

/-- The first Klein coordinate on the first spoke. -/
def spokeWitness : Chain :=
  fun edge coord => if edge = spoke 0 ∧ coord = 0 then 1 else 0

/-- Boundary edges are exactly the first six edges; the witness vanishes on
both boundary cycles. -/
def BoundaryZero (value : Chain) : Prop :=
  ∀ edge : Edge, edge.val < 6 → ∀ coord, value edge coord = 0

instance (value : Chain) : Decidable (BoundaryZero value) := by
  unfold BoundaryZero
  infer_instance

theorem spokeWitness_boundaryZero : BoundaryZero spokeWitness := by
  decide

theorem separator_spokeWitness : separator spokeWitness = 1 := by
  decide

/-- **Counterexample to v23 Theorem 4.9 under its literal annulus and
generator definitions.** -/
theorem spokeWitness_not_mem_generatorSpan :
    spokeWitness ∉ generatorSpan := by
  intro hwitness
  have hkernel := generatorSpan_le_separator_ker hwitness
  have hzero : separator spokeWitness = 0 := LinearMap.mem_ker.mp hkernel
  rw [separator_spokeWitness] at hzero
  exact one_ne_zero hzero

/-- The consumer-facing counterexample: a boundary-zero chain outside the
span generated from every proper triangular-prism coloring. -/
theorem exists_boundaryZero_not_mem_generatorSpan :
    ∃ value : Chain, BoundaryZero value ∧ value ∉ generatorSpan := by
  exact ⟨spokeWitness, spokeWitness_boundaryZero,
    spokeWitness_not_mem_generatorSpan⟩

end GoertzelV24V23TriangularPrismSpanningCounterexample

end Mettapedia.GraphTheory.FourColor
