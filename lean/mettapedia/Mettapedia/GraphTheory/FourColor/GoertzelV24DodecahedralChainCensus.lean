import Mettapedia.GraphTheory.FourColor.GoertzelV24CurvatureScope

/-!
# The dodecahedral-chain face census

This file checks the arithmetic attached to a geometric counterfamily used in
the living proof.  Join `seams + 1` copies of the dodecahedral map in a chain:
at each join delete a pair of designated opposite vertices and match their
three incident half-edges in orientation-reversing cyclic order.  The ordinary
topological proof constructs the spherical cubic map and shows that each join
replaces six pentagonal face wedges by three octagonal faces.

The declarations below certify the resulting vertex, edge, and face counts and
their curvature consequences.  They deliberately do **not** claim to construct
the parametric rotation system; that geometric realization remains a separate
formalization task.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelV24DodecahedralChainCensus

open GoertzelV24CurvatureScope

/-- Vertex count after `seams` dodecahedral three-edge sums. -/
def sphereVertexCount (seams : Nat) : Nat := 18 * seams + 20

/-- Edge count after `seams` dodecahedral three-edge sums. -/
def sphereEdgeCount (seams : Nat) : Nat := 27 * seams + 30

/-- Pentagon count after `seams` dodecahedral three-edge sums. -/
def spherePentagonCount (seams : Nat) : Nat := 6 * seams + 12

/-- Octagon count after `seams` dodecahedral three-edge sums. -/
def sphereOctagonCount (seams : Nat) : Nat := 3 * seams

/-- Face count after `seams` dodecahedral three-edge sums. -/
def sphereFaceCount (seams : Nat) : Nat := 9 * seams + 12

/-- The face-size list predicted by the geometric chain construction. -/
def sphereFaceSizes (seams : Nat) : List Nat :=
  List.replicate (spherePentagonCount seams) 5 ++
    List.replicate (sphereOctagonCount seams) 8

theorem sphere_cubic_incidence (seams : Nat) :
    3 * sphereVertexCount seams = 2 * sphereEdgeCount seams := by
  simp [sphereVertexCount, sphereEdgeCount]
  omega

theorem sphere_euler (seams : Nat) :
    sphereVertexCount seams + sphereFaceCount seams =
      sphereEdgeCount seams + 2 := by
  simp [sphereVertexCount, sphereEdgeCount, sphereFaceCount]
  omega

theorem sphereFaceSizes_length (seams : Nat) :
    (sphereFaceSizes seams).length = sphereFaceCount seams := by
  simp [sphereFaceSizes, spherePentagonCount, sphereOctagonCount,
    sphereFaceCount]
  omega

theorem sphereFaceSizes_minimumFive (seams : Nat) :
    NormalFormFaceSizeConsequences (sphereFaceSizes seams) := by
  intro n hn
  simp only [sphereFaceSizes, List.mem_append, List.mem_replicate] at hn
  rcases hn with hn | hn <;> omega

theorem sphereFaceSizes_pentagonCount (seams : Nat) :
    (sphereFaceSizes seams).count 5 = spherePentagonCount seams := by
  simp [sphereFaceSizes, spherePentagonCount, sphereOctagonCount,
    List.count_replicate]

theorem sphereFaceSizes_octagonCount (seams : Nat) :
    (sphereFaceSizes seams).count 8 = sphereOctagonCount seams := by
  simp [sphereFaceSizes, spherePentagonCount, sphereOctagonCount,
    List.count_replicate]

theorem sphereFaceSizes_hexagonCount (seams : Nat) :
    (sphereFaceSizes seams).count 6 = 0 := by
  simp [sphereFaceSizes, List.count_replicate]

theorem sphereFaceSizes_curvature (seams : Nat) :
    faceSizeCurvatureSum (sphereFaceSizes seams) = 12 := by
  simp [faceSizeCurvatureSum, sphereFaceSizes, spherePentagonCount,
    sphereOctagonCount]
  ring

theorem sphereFaceSizes_negativeCurvatureWeight (seams : Nat) :
    negativeCurvatureWeight (sphereFaceSizes seams) = 6 * seams := by
  simp [negativeCurvatureWeight, sphereFaceSizes, spherePentagonCount,
    sphereOctagonCount]
  omega

/-- Remove one untouched pentagonal cap face from each end of the chain. -/
def annularInternalFaceSizes (seams : Nat) : List Nat :=
  List.replicate (6 * seams + 10) 5 ++ List.replicate (3 * seams) 8

theorem annularInternalFaceSizes_length (seams : Nat) :
    (annularInternalFaceSizes seams).length = 9 * seams + 10 := by
  simp [annularInternalFaceSizes]
  omega

theorem annularInternalFaceSizes_minimumFive (seams : Nat) :
    NormalFormFaceSizeConsequences (annularInternalFaceSizes seams) := by
  simp [NormalFormFaceSizeConsequences, annularInternalFaceSizes]

theorem annularInternalFaceSizes_hexagonCount (seams : Nat) :
    (annularInternalFaceSizes seams).count 6 = 0 := by
  simp [annularInternalFaceSizes, List.count_replicate]

/-- The two-cap annulus has constant signed internal curvature even though
its number of nonhexagonal internal faces grows without bound. -/
theorem annularInternalFaceSizes_curvature (seams : Nat) :
    faceSizeCurvatureSum (annularInternalFaceSizes seams) = 10 := by
  simp [faceSizeCurvatureSum, annularInternalFaceSizes]
  ring

theorem annularInternalFaceSizes_negativeCurvatureWeight (seams : Nat) :
    negativeCurvatureWeight (annularInternalFaceSizes seams) = 6 * seams := by
  simp [negativeCurvatureWeight, annularInternalFaceSizes]
  omega

/-- The census itself gives arbitrarily many internal faces, constant signed
curvature, and no hexagonal face.  The accompanying prose construction is
what realizes these lists by embedded cubic maps. -/
theorem exists_arbitrarily_large_annular_census_without_hexagons
    (bound : Nat) :
    exists faceSizes : List Nat,
      NormalFormFaceSizeConsequences faceSizes /\
      faceSizeCurvatureSum faceSizes = 10 /\
      faceSizes.count 6 = 0 /\
      bound <= faceSizes.length /\
      bound <= negativeCurvatureWeight faceSizes := by
  refine ⟨annularInternalFaceSizes bound,
    annularInternalFaceSizes_minimumFive bound,
    annularInternalFaceSizes_curvature bound,
    annularInternalFaceSizes_hexagonCount bound, ?_, ?_⟩
  · rw [annularInternalFaceSizes_length]
    omega
  · rw [annularInternalFaceSizes_negativeCurvatureWeight]
    omega

end GoertzelV24DodecahedralChainCensus
end Mettapedia.GraphTheory.FourColor
