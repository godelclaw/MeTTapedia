import Mettapedia.GraphTheory.OrbitCountSplitting
import Mettapedia.GraphTheory.FourColor.VertexSideEulerMass

/-!
# The splitting and transport tools, against arguments already made by hand

Results proved elsewhere in this development by building an explicit
equivalence of quotients are re-derived here from the two generic instruments
of `Mettapedia.GraphTheory.OrbitCountSplitting`.  The point is calibration: the
instruments are stated correctly exactly when the existing statements are
instances of them.

| existing result | proved there by | proved here from |
| --- | --- | --- |
| `orbitCount_rho_eq_card_vertex` | `rhoOrbitEquivVertex` | complete invariant |
| `cycle_count_retainedRho` | `retainedRhoOrbitEquiv` | complete invariant |
| `wordOrbitCount_capped` | `componentEquiv`, an `Equiv.ofBijective` | complete invariant |
| `cycle_count_cappedPhi` | `sideSplitEquiv` + `cappedPhi_split` + a disjoint-sum law | Tool A + Tool B twice |

(`orbitCount_sumCongr`, whose hand proof builds `sumOrbitEquiv`, is re-derived
in the generic module itself, where it needs no four-colour import.)

The last one is the substantive check.  `cappedPhi` is the face walk of a map
whose edges outside a chosen vertex side have been capped off; the existing
proof exhibits the carrier as a literal `Equiv.sumCompl` and rewrites the
permutation across it.  Here the side darts are simply observed to be
`cappedPhi`-invariant (Tool A), and each of the two restrictions is matched
with its native permutation by the subtype inclusion, which is equivariant on
its side and says nothing at all about the other (Tool B).

Nothing here is deleted or weakened elsewhere; these are second proofs.
-/

namespace Mettapedia.GraphTheory.OrbitCountSplittingApplications

open Equiv Equiv.Perm
open Mettapedia.GraphTheory.OrbitCountSplitting
open Mettapedia.GraphTheory.FourColor
open GoertzelV24PermutationOrbitSurgery GoertzelV24WordReachability
open GoertzelV24RotationCutDartDecomposition GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24FaceDualConnectedness GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24MapEulerBound GoertzelV24InvolutionEdgeList
open SphericalNestedBoundaryOrder VertexSideCappedComponents
open OpenTangleMarkedFace

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Rotation orbits are vertices

`orbitCount_rho_eq_card_vertex` and `cycle_count_retainedRho` both say that the
rotation's orbits are counted by the vertices they sit over.  Both are the
complete-invariant corollary applied to `vertOf`. -/

section Vertices

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The base vertex is a complete invariant of the rotation's orbits. -/
theorem sameCycle_rho_iff_vertOf_eq (RS : RotationSystem V E)
    (hrot : VertexRotationCyclic RS) (x y : RS.D) :
    RS.rho.SameCycle x y ↔ RS.vertOf x = RS.vertOf y :=
  ⟨GoertzelV24StellarRotationSystem.vertOf_eq_of_rho_sameCycle RS, hrot x y⟩

/-- **`orbitCount_rho_eq_card_vertex`, from the complete-invariant tool.** -/
theorem orbitCount_rho_eq_card_vertex_of_invariant (RS : RotationSystem V E)
    (hrot : VertexRotationCyclic RS) (hsurj : Function.Surjective RS.vertOf) :
    orbitCount RS.rho = Fintype.card V := by
  rw [← Nat.card_eq_fintype_card]
  exact orbitCount_eq_card_of_completeInvariant RS.vertOf
    (sameCycle_rho_iff_vertOf_eq RS hrot) hsurj

/-- **`cycle_count_retainedRho`, from the complete-invariant tool.**  The
rotation restricted to the darts over a set of vertices has one orbit per
vertex of that set. -/
theorem orbitCount_retainedRho_eq_card (RS : RotationSystem V E)
    (hrot : VertexRotationCyclic RS) (hsurj : Function.Surjective RS.vertOf)
    (keep : V → Prop) :
    orbitCount (retainedRho RS keep) = Fintype.card {v // keep v} := by
  rw [← Nat.card_eq_fintype_card]
  refine orbitCount_eq_card_of_completeInvariant
    (fun d : RetainedDart RS keep => (⟨RS.vertOf d.val, d.2⟩ : {v // keep v})) ?_ ?_
  · intro x y
    constructor
    · intro h
      exact Subtype.ext ((sameCycle_rho_iff_vertOf_eq RS hrot _ _).1
        (sameCycle_subtypePerm.mp h))
    · intro h
      exact SameCycle.subtypePerm
        ((sameCycle_rho_iff_vertOf_eq RS hrot _ _).2 (congrArg Subtype.val h))
  · rintro ⟨v, hv⟩
    obtain ⟨d, hd⟩ := hsurj v
    exact ⟨⟨d, by rw [hd]; exact hv⟩, Subtype.ext hd⟩

end Vertices

/-! ## Components of a capped side

`wordOrbitCount_capped` computes the components of the map obtained by deleting
every edge that leaves a chosen vertex side.  The existing proof builds the
quotient equivalence by hand out of `word_iff_label` and `label_surjective`;
those two facts are exactly the hypotheses of the complete-invariant tool. -/

section Capped

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **`wordOrbitCount_capped`, from the complete-invariant tool.** -/
theorem wordOrbitCount_capped_of_invariant (RS : RotationSystem V E)
    (hrot : VertexRotationCyclic RS) (hsurj : Function.Surjective RS.vertOf)
    (side : V → Prop) :
    wordOrbitCount (RS.rho :: swapGenerators (edgeList (cappedAlpha RS side))) =
      Fintype.card (SideGraph RS side).ConnectedComponent + Fintype.card {v // ¬ side v} := by
  have h := wordOrbitCount_eq_card_of_completeInvariant (label RS side)
    (word_iff_label RS hrot side) (label_surjective RS hsurj side)
  rw [h, Nat.card_eq_fintype_card]
  exact Fintype.card_sum

/-! ### Splitting the capped face walk

The side darts are `cappedPhi`-invariant, because the capped flip never crosses
the side boundary and the rotation never changes base vertex.  That is the
whole input to Tool A. -/

/-- The capped face walk fixes the base-vertex side. -/
theorem side_cappedPhi (RS : RotationSystem V E) (side : V → Prop) (d : RS.D) :
    side (RS.vertOf (cappedPhi RS side d)) ↔ side (RS.vertOf d) := by
  have hvert : RS.vertOf (cappedPhi RS side d) = RS.vertOf (cappedAlpha RS side d) := by
    show RS.vertOf (RS.rho (cappedAlpha RS side d)) = _
    rw [RS.vert_rho]
  rw [hvert, cappedAlpha_apply]
  by_cases h : InsideEdge RS side d
  · rw [if_pos h]
    exact ⟨fun _ => h.1, fun _ => h.2⟩
  · rw [if_neg h]

/-- Off the side, the capped face walk is the bare rotation: the capped flip
has nothing to do there. -/
theorem cappedPhi_apply_of_not_side (RS : RotationSystem V E) (side : V → Prop)
    {d : RS.D} (hd : ¬ side (RS.vertOf d)) :
    cappedPhi RS side d = RS.rho d := by
  show RS.rho (cappedAlpha RS side d) = RS.rho d
  rw [cappedAlpha_apply, if_neg (fun h => hd h.1)]

/-- The darts sitting over the chosen side. -/
def sideDarts (RS : RotationSystem V E) (side : V → Prop) : Set RS.D :=
  {d | side (RS.vertOf d)}

/-- **Tool B on the side.**  The subtype inclusion of the retained darts is
equivariant for `cappedPhi` against the retained-side face walk — and says
nothing about the darts outside the side. -/
theorem orbitCountOn_cappedPhi_side (RS : RotationSystem V E) (side : V → Prop) :
    orbitCountOn (cappedPhi RS side) (sideDarts RS side) =
      orbitCount (retainedCappedFacePerm RS side) :=
  orbitCountOn_eq_orbitCount_of_equivariantOn
    (σ := cappedPhi RS side) (σ' := retainedCappedFacePerm RS side)
    (h := fun y : RetainedDart RS side => y.val) (S := sideDarts RS side)
    (fun x hx => (side_cappedPhi RS side x).2 hx)
    (fun y => y.2)
    (fun _ _ hxy => Subtype.ext hxy)
    (fun y => (cappedPhi_retained RS side y).symm)
    (fun x hx => ⟨⟨x, hx⟩, SameCycle.refl _ x⟩)

/-- **Tool B off the side.**  The same inclusion for the complementary darts,
where `cappedPhi` degenerates to the rotation. -/
theorem orbitCountOn_cappedPhi_compl (RS : RotationSystem V E) (side : V → Prop) :
    orbitCountOn (cappedPhi RS side) (sideDarts RS side)ᶜ =
      orbitCount (retainedRho RS (fun v => ¬ side v)) :=
  orbitCountOn_eq_orbitCount_of_equivariantOn
    (σ := cappedPhi RS side) (σ' := retainedRho RS (fun v => ¬ side v))
    (h := fun y : RetainedDart RS (fun v => ¬ side v) => y.val)
    (S := (sideDarts RS side)ᶜ)
    (fun x hx hc => hx ((side_cappedPhi RS side x).1 hc))
    (fun y => y.2)
    (fun _ _ hxy => Subtype.ext hxy)
    (fun y => (cappedPhi_apply_of_not_side RS side y.2).symm)
    (fun x hx => ⟨⟨x, hx⟩, SameCycle.refl _ x⟩)

/-- **The splitting of the capped face walk**, from Tool A and Tool B. -/
theorem orbitCount_cappedPhi_split (RS : RotationSystem V E) (side : V → Prop) :
    orbitCount (cappedPhi RS side) =
      orbitCount (retainedCappedFacePerm RS side) +
        orbitCount (retainedRho RS (fun v => ¬ side v)) := by
  have hsplit := orbitCount_eq_orbitCountOn_add_compl (cappedPhi RS side)
    (S := sideDarts RS side) (fun x hx => (side_cappedPhi RS side x).2 hx)
  rw [hsplit, orbitCountOn_cappedPhi_side, orbitCountOn_cappedPhi_compl]

/-- **`cycle_count_cappedPhi`, from the two tools.**  Identical statement to the
one proved by hand in `VertexSideEulerMass`. -/
theorem cycle_count_cappedPhi_of_splitting (RS : RotationSystem V E)
    (hrot : VertexRotationCyclic RS) (hsurj : Function.Surjective RS.vertOf)
    (side : V → Prop) (outer : RetainedDart RS side) :
    orbitCount (cappedPhi RS side) =
      (openPhi (GoertzelV24OpenTangleComposition.OpenTangleData.ofVertexSide RS side outer)).partition.parts.card +
        Fintype.card {v // ¬ side v} := by
  have hopen : (openPhi
      (GoertzelV24OpenTangleComposition.OpenTangleData.ofVertexSide RS side outer)).partition.parts.card
      = orbitCount (retainedCappedFacePerm RS side) := by
    rw [← card_permOrbit_eq_card_partition_parts, VertexSideEulerMass.openPhi_ofVertexSide]
    exact orbitCount_eq_of_equivariant_bijection
      (σ := (retainedDartEquivInternalSumBoundary RS side).permCongr
        (retainedCappedFacePerm RS side))
      (σ' := retainedCappedFacePerm RS side)
      (retainedDartEquivInternalSumBoundary RS side)
      (retainedDartEquivInternalSumBoundary RS side).bijective
      (fun y => by simp [Equiv.permCongr_apply])
  rw [orbitCount_cappedPhi_split, hopen,
    orbitCount_retainedRho_eq_card RS hrot hsurj (fun v => ¬ side v)]

end Capped

/-! ## Statement identity

Each equation below typechecks only if the re-derived theorem has exactly the
type of the existing one; proof irrelevance then closes it by `rfl`.  These are
the regression guard for the table in the module docstring: if either side's
statement drifts, this file stops compiling. -/

section StatementIdentity

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

example (σ : Perm α) (τ : Perm β) :
    GoertzelV24OrbitCountCongr.orbitCount_sumCongr σ τ =
      orbitCount_sumCongr_of_splitting σ τ := rfl

example (RS : RotationSystem V E) (hrot : VertexRotationCyclic RS)
    (hsurj : Function.Surjective RS.vertOf) :
    GoertzelV24StellarDualStructure.orbitCount_rho_eq_card_vertex RS hrot hsurj =
      orbitCount_rho_eq_card_vertex_of_invariant RS hrot hsurj := rfl

example (RS : RotationSystem V E) (hrot : VertexRotationCyclic RS)
    (hsurj : Function.Surjective RS.vertOf) (side : V → Prop) :
    wordOrbitCount_capped RS hrot hsurj side =
      wordOrbitCount_capped_of_invariant RS hrot hsurj side := rfl

/-- `cycle_count_retainedRho` is stated in partition-parts form; it is the
orbit-count re-derivation read through the existing partition bridge. -/
example (RS : RotationSystem V E) (hrot : VertexRotationCyclic RS)
    (hsurj : Function.Surjective RS.vertOf) (side : V → Prop) :
    VertexSideEulerMass.cycle_count_retainedRho RS hrot hsurj side =
      (card_permOrbit_eq_card_partition_parts (retainedRho RS side)).symm.trans
        (orbitCount_retainedRho_eq_card RS hrot hsurj side) := rfl

example (RS : RotationSystem V E) (hrot : VertexRotationCyclic RS)
    (hsurj : Function.Surjective RS.vertOf) (side : V → Prop)
    (outer : RetainedDart RS side) :
    VertexSideEulerMass.cycle_count_cappedPhi RS hrot hsurj side outer =
      cycle_count_cappedPhi_of_splitting RS hrot hsurj side outer := rfl

end StatementIdentity

end

end Mettapedia.GraphTheory.OrbitCountSplittingApplications
