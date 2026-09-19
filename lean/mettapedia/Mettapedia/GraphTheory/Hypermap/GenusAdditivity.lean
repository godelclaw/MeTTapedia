import Mettapedia.GraphTheory.Hypermap.Euler
import Mettapedia.GraphTheory.Hypermap.Connectivity
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitCountCongr
import Mettapedia.GraphTheory.FourColor.InvolutionEulerTransport

/-!
# Genus additivity under gluing

Cutting a hypermap along a ring produces two hypermaps, each carrying its own
copy of the ring; gluing is the inverse operation.  The theorem that matters is
that the genus is *additive* under that operation, and in particular that the
glued map is planar exactly when both pieces are.

This module supplies two things.

## The arithmetic core, unconditionally

`genus_add_of_orbit_counts` is the whole numeric content of genus additivity,
proved outright.  It takes the five counting statements that a gluing produces
— how the dart count, the three orbit counts and the component count of the two
pieces compare with those of the glued map — and concludes

    genus G = genus Gd + genus Gr.

This is not a repackaging of the definition.  `genus` is a *truncated* halving,
so additivity of the halves does not follow from additivity of the doubles
without knowing that no truncation occurs anywhere; that is exactly what
`Hypermap.even_genus` supplies, and it is used three times here, once for each
map.  The lemma is stated with the border contributions as parameters `b` (the
number of border orbits absorbed, `1` for a genuine ring, `0` for none) and `r`
(the ring length), and the proof shows that they cancel: *any* pair `(b, r)`
satisfying the five hypotheses gives additivity.  That cancellation is the
reason genus additivity holds at all.

## The empty-border case, outright

When the ring is empty the gluing is a disjoint union, and the five hypotheses
become available.  `genus_disjointSum` and `planar_disjointSum` are then
unconditional theorems: the genus of a disjoint union is the sum of the genera,
and a disjoint union is planar exactly when both summands are.

## The nonempty-border case

The nonempty-ring case needs the five counting statements themselves, and those
are a substantial piece of combinatorics: one has to show, for instance, that
the disk side's edge orbits are the glued map's edge orbits lying off the
remainder *plus exactly one* — the ring, which is a single edge orbit on the
disk side and a single node orbit on the remainder side.  Each of the five
requires transporting an orbit count along an injection that is equivariant
only away from the ring, and splitting an orbit count over a pair of
complementary invariant sets. These tools and the gluing predicate are now
available: `Hypermap.Patch` derives the counts and consumes
`genus_add_of_orbit_counts`. Component counting itself lives in the lighter
`Hypermap.Connectivity` module so consumers need not import gluing theory.
-/

namespace Mettapedia.GraphTheory

open Mettapedia.GraphTheory.FourColor

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery GoertzelV24WordReachability

namespace Hypermap

variable {D : Type*} [Fintype D] [DecidableEq D]


/-! ## The arithmetic of genus additivity -/

/-- **Genus additivity, given the counting statements a gluing produces.**

`b` counts the border orbits the gluing absorbs — one edge orbit on the disk
side, one node orbit on the remainder side, one component — and `r` is the ring
length, which is how many face orbits and how many darts are duplicated.  The
proof shows both cancel, so no relation between `b` and `r` is needed.

The three uses of `even_genus` are essential: `genus` halves with truncation,
and additivity of the halved quantities is not formal. -/
theorem genus_add_of_orbit_counts
    {Dg Dd Dr : Type*} [Fintype Dg] [DecidableEq Dg] [Fintype Dd] [DecidableEq Dd]
    [Fintype Dr] [DecidableEq Dr]
    {G : Hypermap Dg} {Hd : Hypermap Dd} {Hr : Hypermap Dr} {b r : ℕ}
    (hcard : Fintype.card Dd + Fintype.card Dr = r + Fintype.card Dg)
    (hE : orbitCount Hd.edge + orbitCount Hr.edge = b + orbitCount G.edge)
    (hN : orbitCount Hd.node + orbitCount Hr.node = b + orbitCount G.node)
    (hF : orbitCount Hd.face + orbitCount Hr.face = r + orbitCount G.face)
    (hC : compCount Hd + compCount Hr = b + compCount G) :
    genus G = genus Hd + genus Hr := by
  have eg := even_genus G
  have ed := even_genus Hd
  have er := even_genus Hr
  rw [eulerRhs_eq_card_add_two_mul_compCount, eulerLhs_eq_orbit_sum] at eg ed er
  omega

/-- The same statement in planarity form: with the counting statements in hand,
a gluing is planar exactly when both of its pieces are. -/
theorem planar_of_orbit_counts
    {Dg Dd Dr : Type*} [Fintype Dg] [DecidableEq Dg] [Fintype Dd] [DecidableEq Dd]
    [Fintype Dr] [DecidableEq Dr]
    {G : Hypermap Dg} {Hd : Hypermap Dd} {Hr : Hypermap Dr} {b r : ℕ}
    (hcard : Fintype.card Dd + Fintype.card Dr = r + Fintype.card Dg)
    (hE : orbitCount Hd.edge + orbitCount Hr.edge = b + orbitCount G.edge)
    (hN : orbitCount Hd.node + orbitCount Hr.node = b + orbitCount G.node)
    (hF : orbitCount Hd.face + orbitCount Hr.face = r + orbitCount G.face)
    (hC : compCount Hd + compCount Hr = b + compCount G) :
    Planar G ↔ Planar Hd ∧ Planar Hr := by
  have h := genus_add_of_orbit_counts hcard hE hN hF hC
  rw [planar_iff_genus_eq_zero, planar_iff_genus_eq_zero, planar_iff_genus_eq_zero]
  omega

/-! ## The empty-border case: disjoint unions -/

variable {D₁ D₂ : Type*} [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]

/-- The disjoint union of two hypermaps: gluing along an empty ring. -/
def disjointSum (H₁ : Hypermap D₁) (H₂ : Hypermap D₂) : Hypermap (D₁ ⊕ D₂) where
  edge := Equiv.sumCongr H₁.edge H₂.edge
  node := Equiv.sumCongr H₁.node H₂.node
  face := Equiv.sumCongr H₁.face H₂.face
  cancel3 := by
    rintro (d | d)
    · exact congrArg Sum.inl (H₁.cancel3 d)
    · exact congrArg Sum.inr (H₂.cancel3 d)

@[simp] theorem disjointSum_edge (H₁ : Hypermap D₁) (H₂ : Hypermap D₂) :
    (disjointSum H₁ H₂).edge = Equiv.sumCongr H₁.edge H₂.edge := rfl

@[simp] theorem disjointSum_node (H₁ : Hypermap D₁) (H₂ : Hypermap D₂) :
    (disjointSum H₁ H₂).node = Equiv.sumCongr H₁.node H₂.node := rfl

@[simp] theorem disjointSum_face (H₁ : Hypermap D₁) (H₂ : Hypermap D₂) :
    (disjointSum H₁ H₂).face = Equiv.sumCongr H₁.face H₂.face := rfl

theorem compCount_disjointSum (H₁ : Hypermap D₁) (H₂ : Hypermap D₂) :
    compCount (disjointSum H₁ H₂) = compCount H₁ + compCount H₂ := by
  rw [compCount_eq_pair, compCount_eq_pair, compCount_eq_pair,
    disjointSum_face, disjointSum_edge]
  exact InvolutionEulerDefect.pair_count_sum H₁.face H₁.edge H₂.face H₂.edge

/-- **Genus is additive over disjoint unions.**  This is the empty-ring case of
genus additivity under gluing. -/
theorem genus_disjointSum (H₁ : Hypermap D₁) (H₂ : Hypermap D₂) :
    genus (disjointSum H₁ H₂) = genus H₁ + genus H₂ := by
  refine genus_add_of_orbit_counts (b := 0) (r := 0) ?_ ?_ ?_ ?_ ?_
  · simp [Fintype.card_sum]
  · simp [GoertzelV24OrbitCountCongr.orbitCount_sumCongr]
  · simp [GoertzelV24OrbitCountCongr.orbitCount_sumCongr]
  · simp [GoertzelV24OrbitCountCongr.orbitCount_sumCongr]
  · simp [compCount_disjointSum]

/-- **A disjoint union is planar exactly when both pieces are.**  This is the
empty-ring case of the planarity form of genus additivity. -/
theorem planar_disjointSum (H₁ : Hypermap D₁) (H₂ : Hypermap D₂) :
    Planar (disjointSum H₁ H₂) ↔ Planar H₁ ∧ Planar H₂ := by
  rw [planar_iff_genus_eq_zero, planar_iff_genus_eq_zero, planar_iff_genus_eq_zero,
    genus_disjointSum]
  omega

end Hypermap

end Mettapedia.GraphTheory
