import Mettapedia.GraphTheory.Embedding.FaceCut

/-!
# Gauge normalization of binary face cuts

An exact binary face cut is determined by its selected primal edges only up
to adding the same constant to every face label.  On a connected two-sided
facial dual, choosing one root face removes this global gauge freedom.

This is generic combinatorial-map theory.  It is independent of the route
that constructs a cut and provides a canonical comparison surface for
compositional arguments that obtain the two shores by different choices.
-/

namespace Mettapedia.GraphTheory.Embedding

open Mettapedia.GraphTheory.FourColor
open Mettapedia.GraphTheory.FourColor.GoertzelV24FaceBoundaryLinearAlgebra
open Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness
open Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitIncidence
open Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceTwoSided
open Mettapedia.GraphTheory.FourColor.SimpleGraphDartRotation

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
  {RS : RotationSystem V E} {selected : E → Prop}

namespace ExactFaceCut

/-- Build a binary face cut from a set of faces when the selected primal
edges are exactly those with one incident face in the set. -/
def ofFinset (faces : Finset (OrbitFace RS))
    (hseparates : ∀ dart : RS.D,
      selected (RS.edgeOf dart) ↔
        ((dartOrbitFace RS dart ∈ faces ∧
            dartOrbitFace RS (RS.alpha dart) ∉ faces) ∨
          (dartOrbitFace RS dart ∉ faces ∧
            dartOrbitFace RS (RS.alpha dart) ∈ faces))) :
    ExactFaceCut RS selected F2 where
  label face := if face ∈ faces then 1 else 0
  separates := by
    intro dart
    rw [hseparates dart]
    by_cases hleft : dartOrbitFace RS dart ∈ faces <;>
      by_cases hright : dartOrbitFace RS (RS.alpha dart) ∈ faces <;>
      simp [hleft, hright]

@[simp]
theorem ofFinset_label_eq_one_iff (faces : Finset (OrbitFace RS))
    (hseparates : ∀ dart : RS.D,
      selected (RS.edgeOf dart) ↔
        ((dartOrbitFace RS dart ∈ faces ∧
            dartOrbitFace RS (RS.alpha dart) ∉ faces) ∨
          (dartOrbitFace RS dart ∉ faces ∧
            dartOrbitFace RS (RS.alpha dart) ∈ faces)))
    (face : OrbitFace RS) :
    (ofFinset faces hseparates).label face = 1 ↔ face ∈ faces := by
  simp [ofFinset]

/-- Normalize a binary face cut by requiring the chosen root face to have
label zero. -/
def basedLabel (cut : ExactFaceCut RS selected F2)
    (root face : OrbitFace RS) : F2 :=
  cut.label face - cut.label root

@[simp]
theorem basedLabel_root (cut : ExactFaceCut RS selected F2)
    (root : OrbitFace RS) :
    cut.basedLabel root root = 0 := by
  simp [basedLabel]

/-- Equal facial-boundary vectors give equal root-normalized labels on a
connected two-sided facial dual. -/
theorem basedLabel_eq_of_boundary_eq
    (htwoSided : OrbitFacesTwoSided RS)
    (hdual : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Connected)
    (first second : ExactFaceCut RS selected F2)
    (hboundary : orbitFaceBoundaryLinearMap RS first.label =
      orbitFaceBoundaryLinearMap RS second.label)
    (root face : OrbitFace RS) :
    first.basedLabel root face = second.basedLabel root face := by
  let difference : OrbitFace RS → F2 := first.label - second.label
  have hkernel : difference ∈
      LinearMap.ker (orbitFaceBoundaryLinearMap RS) := by
    rw [LinearMap.mem_ker]
    change orbitFaceBoundaryLinearMap RS (first.label - second.label) = 0
    rw [map_sub, hboundary, sub_self]
  have hconstant :=
    (mem_ker_orbitFaceBoundaryLinearMap_iff_constant
      RS htwoSided hdual difference).1 hkernel face root
  dsimp only [difference, Pi.sub_apply] at hconstant
  unfold basedLabel
  linear_combination hconstant

/-- Two exact binary cuts selecting the same primal edges have the same
facial-boundary vector. -/
theorem boundary_eq
    (htwoSided : OrbitFacesTwoSided RS)
    (first second : ExactFaceCut RS selected F2) :
    orbitFaceBoundaryLinearMap RS first.label =
      orbitFaceBoundaryLinearMap RS second.label := by
  funext edge
  obtain ⟨dart, hdart⟩ := RS.dartsOn_nonempty edge
  have hedge : RS.edgeOf dart = edge := (RS.mem_dartsOn).1 hdart
  rw [← hedge,
    orbitFaceBoundaryLinearMap_apply_edgeOf RS htwoSided,
    orbitFaceBoundaryLinearMap_apply_edgeOf RS htwoSided]
  by_cases hselected : selected (RS.edgeOf dart)
  · have hfirst : first.label (dartOrbitFace RS dart) +
        first.label (dartOrbitFace RS (RS.alpha dart)) = 1 :=
      (f2_add_eq_one_iff_ne _ _).2 ((first.separates dart).2 hselected)
    have hsecond : second.label (dartOrbitFace RS dart) +
        second.label (dartOrbitFace RS (RS.alpha dart)) = 1 :=
      (f2_add_eq_one_iff_ne _ _).2 ((second.separates dart).2 hselected)
    rw [hfirst, hsecond]
  · have hfirst : first.label (dartOrbitFace RS dart) =
        first.label (dartOrbitFace RS (RS.alpha dart)) := by
      by_contra hne
      exact hselected ((first.separates dart).1 hne)
    have hsecond : second.label (dartOrbitFace RS dart) =
        second.label (dartOrbitFace RS (RS.alpha dart)) := by
      by_contra hne
      exact hselected ((second.separates dart).1 hne)
    rw [hfirst, hsecond, zmod2_add_self, zmod2_add_self]

/-- Root normalization makes an exact binary face cut uniquely determined by
its selected primal edges. -/
theorem basedLabel_eq
    (htwoSided : OrbitFacesTwoSided RS)
    (hdual : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Connected)
    (first second : ExactFaceCut RS selected F2)
    (root face : OrbitFace RS) :
    first.basedLabel root face = second.basedLabel root face :=
  basedLabel_eq_of_boundary_eq htwoSided hdual first second
    (boundary_eq htwoSided first second) root face

end ExactFaceCut

namespace FaceCutGauge

/-- Module-facing form of root-normalized uniqueness for exact binary face
cuts.  The method-style theorem lives in `ExactFaceCut`; this declaration is
the stable citation surface for the gauge-normalization module. -/
theorem basedLabel_eq
    (htwoSided : OrbitFacesTwoSided RS)
    (hdual : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Connected)
    (first second : ExactFaceCut RS selected F2)
    (root face : OrbitFace RS) :
    first.basedLabel root face = second.basedLabel root face :=
  ExactFaceCut.basedLabel_eq htwoSided hdual first second root face

end FaceCutGauge

end

end Mettapedia.GraphTheory.Embedding
