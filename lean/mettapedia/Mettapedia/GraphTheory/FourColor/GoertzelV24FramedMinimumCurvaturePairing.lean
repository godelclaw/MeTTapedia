import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCurvaturePairing

/-!
# A geometry-sensitive pairing for framed curvature

Weighted L9 supplies equal finite credit and debt cardinalities, but an
arbitrary equivalence between those carriers forgets all planar geometry.
This file chooses, among the same finite equivalences, one minimizing the
total internal-dual distance from every negative-curvature token that is paid
by a pentagon.  Source-foot payments contribute zero.

This is an L6 repair layer.  The construction does not yet prove that the
chosen routes are laminar.  It provides the finite optimality inequality needed for the subsequent uncrossing
argument; in particular it does not assume a bounded number of pentagons.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceOrbitIncidence
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace FiniteAssignment

variable {A B : Type*} [Fintype A] [DecidableEq A]

/-- Total cost of a finite bijective assignment. -/
def assignmentCost (cost : A → B → Nat) (assignment : A ≃ B) : Nat :=
  ∑ input : A, cost input (assignment input)

/-- Swap the two outputs assigned to distinct inputs. -/
def swapAt (assignment : A ≃ B) (first second : A) : A ≃ B :=
  (Equiv.swap first second).trans assignment

/-- Exact cost accounting for a two-assignment exchange. -/
theorem assignmentCost_swapAt (cost : A → B → Nat)
    (assignment : A ≃ B) {first second : A} (hne : first ≠ second) :
    assignmentCost cost (swapAt assignment first second) +
          cost first (assignment first) + cost second (assignment second) =
      assignmentCost cost assignment +
          cost first (assignment second) + cost second (assignment first) := by
  classical
  let rest : Finset A := (Finset.univ.erase first).erase second
  have hsecond : second ∈ Finset.univ.erase first := by
    simp [hne.symm]
  have splitSum (f : A → Nat) :
      (∑ input : A, f input) =
        f first + f second + ∑ input ∈ rest, f input := by
    rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ first)]
    rw [← Finset.add_sum_erase (Finset.univ.erase first) f hsecond]
    simp only [rest]
    omega
  have hrest :
      (∑ input ∈ rest, cost input ((swapAt assignment first second) input)) =
        ∑ input ∈ rest, cost input (assignment input) := by
    apply Finset.sum_congr rfl
    intro input hinput
    have hfirst : input ≠ first := by
      exact fun heq => (Finset.mem_erase.1
        (Finset.mem_erase.1 hinput).2).1 heq
    have hsecond' : input ≠ second := (Finset.mem_erase.1 hinput).1
    simp [swapAt, Equiv.swap_apply_of_ne_of_ne hfirst hsecond']
  rw [assignmentCost, assignmentCost, splitSum, splitSum, hrest]
  simp [swapAt, Equiv.swap_apply_left, Equiv.swap_apply_right]
  omega

/-- A globally minimum finite assignment is locally optimal under every
two-output exchange. -/
theorem pair_cost_le_swapped_of_minimum
    (cost : A → B → Nat) (assignment : A ≃ B)
    (hminimum : ∀ other : A ≃ B,
      assignmentCost cost assignment ≤ assignmentCost cost other)
    {first second : A} (hne : first ≠ second) :
    cost first (assignment first) + cost second (assignment second) ≤
      cost first (assignment second) + cost second (assignment first) := by
  have htotal := hminimum (swapAt assignment first second)
  have haccount := assignmentCost_swapAt cost assignment hne
  omega

end FiniteAssignment

namespace SourceTrail

namespace AnnularEmbedding

/-- The internal face represented by a negative-curvature token. -/
def InteriorNegativeCurvatureToken.face
    {source : SourceTrail G} {embedded : source.AnnularEmbedding}
    (token : embedded.InteriorNegativeCurvatureToken) :
    AmbientFace embedded.cellulation.interiorFaces :=
  token.1

/-- View an internal pentagon token as an internal ambient face. -/
def InteriorPentagonToken.face
    {source : SourceTrail G} {embedded : source.AnnularEmbedding}
    (token : embedded.InteriorPentagonToken) :
    AmbientFace embedded.cellulation.interiorFaces :=
  ⟨token.1, (embedded.mem_interiorPentagonFaces_iff token.1).1 token.2 |>.1⟩

/-- The geometric contribution of one negative-curvature debt under a
credit/debt pairing.  Only pentagon-paid debt has a dual distance; the fixed
source-foot exceptional class contributes zero. -/
def curvatureDebtPairingCost
    {source : SourceTrail G} (embedded : source.AnnularEmbedding)
    (pairing : embedded.PositiveCurvatureCredit ≃
      embedded.NegativeCurvatureDebt)
    (token : embedded.InteriorNegativeCurvatureToken) : Nat :=
  match pairing.symm (Sum.inl token) with
  | Sum.inl pentagon =>
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).dist token.face pentagon.face
  | Sum.inr _ => 0

/-- The same geometric cost with credits as the assignment inputs. -/
def curvatureCreditPairingCost
    {source : SourceTrail G} (embedded : source.AnnularEmbedding)
    (credit : embedded.PositiveCurvatureCredit)
    (debt : embedded.NegativeCurvatureDebt) : Nat :=
  match credit, debt with
  | Sum.inl pentagon, Sum.inl token =>
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).dist token.face pentagon.face
  | _, _ => 0

/-- Total internal-dual distance of all pentagon-paid negative-curvature
tokens. -/
def curvaturePairingCost
    {source : SourceTrail G} (embedded : source.AnnularEmbedding)
    (pairing : embedded.PositiveCurvatureCredit ≃
      embedded.NegativeCurvatureDebt) : Nat :=
  ∑ debt : embedded.NegativeCurvatureDebt,
    match debt with
    | Sum.inl token => embedded.curvatureDebtPairingCost pairing token
    | Sum.inr _ => 0

/-- The total debt-indexed cost agrees with the ordinary credit-indexed
finite assignment cost. -/
theorem curvaturePairingCost_eq_assignmentCost
    {source : SourceTrail G} (embedded : source.AnnularEmbedding)
    (pairing : embedded.PositiveCurvatureCredit ≃
      embedded.NegativeCurvatureDebt) :
    embedded.curvaturePairingCost pairing =
      FiniteAssignment.assignmentCost embedded.curvatureCreditPairingCost
        pairing := by
  classical
  rw [curvaturePairingCost, FiniteAssignment.assignmentCost]
  rw [← pairing.symm.sum_comp]
  apply Fintype.sum_congr
  intro debt
  simp only [Equiv.apply_symm_apply]
  cases debt with
  | inl token =>
      cases hcredit : pairing.symm (Sum.inl token) <;>
        simp [curvatureDebtPairingCost, curvatureCreditPairingCost, hcredit]
  | inr boundary =>
      simp [curvatureCreditPairingCost]

/-- A credit/debt equivalence minimizing the geometric pairing cost.  The
already-proved weighted-L9 equivalence witnesses that the finite search space
is nonempty. -/
noncomputable def minimumCurvatureCreditDebtEquiv
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    embedded.PositiveCurvatureCredit ≃ embedded.NegativeCurvatureDebt := by
  let seed := embedded.curvatureCreditDebtEquiv hsource geometry
  let candidates : Finset
      (embedded.PositiveCurvatureCredit ≃ embedded.NegativeCurvatureDebt) :=
    Finset.univ
  exact Classical.choose
    (candidates.exists_min_image (embedded.curvaturePairingCost)
      ⟨seed, Finset.mem_univ seed⟩)

/-- The chosen geometric pairing costs no more than any other weighted-L9
pairing. -/
theorem minimumCurvatureCreditDebtEquiv_cost_le
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (other : embedded.PositiveCurvatureCredit ≃
      embedded.NegativeCurvatureDebt) :
    embedded.curvaturePairingCost
        (embedded.minimumCurvatureCreditDebtEquiv hsource geometry) ≤
      embedded.curvaturePairingCost other := by
  let seed := embedded.curvatureCreditDebtEquiv hsource geometry
  let candidates : Finset
      (embedded.PositiveCurvatureCredit ≃ embedded.NegativeCurvatureDebt) :=
    Finset.univ
  exact Classical.choose_spec
    (candidates.exists_min_image (embedded.curvaturePairingCost)
      ⟨seed, Finset.mem_univ seed⟩) |>.2 other (Finset.mem_univ other)

/-- Local two-pair optimality of the geometry-sensitive L9 pairing.  This is
the exchange inequality used by an uncrossing proof; no planarity conclusion
is asserted here. -/
theorem minimumCurvatureCreditDebtEquiv_pair_cost_le_swapped
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    {first second : embedded.PositiveCurvatureCredit}
    (hne : first ≠ second) :
    embedded.curvatureCreditPairingCost first
          (embedded.minimumCurvatureCreditDebtEquiv hsource geometry first) +
        embedded.curvatureCreditPairingCost second
          (embedded.minimumCurvatureCreditDebtEquiv hsource geometry second) ≤
      embedded.curvatureCreditPairingCost first
          (embedded.minimumCurvatureCreditDebtEquiv hsource geometry second) +
        embedded.curvatureCreditPairingCost second
          (embedded.minimumCurvatureCreditDebtEquiv hsource geometry first) := by
  apply FiniteAssignment.pair_cost_le_swapped_of_minimum
    embedded.curvatureCreditPairingCost
    (embedded.minimumCurvatureCreditDebtEquiv hsource geometry)
  · intro other
    rw [← embedded.curvaturePairingCost_eq_assignmentCost,
      ← embedded.curvaturePairingCost_eq_assignmentCost]
    exact embedded.minimumCurvatureCreditDebtEquiv_cost_le
      hsource geometry other
  · exact hne

/-- The exchange inequality in its geometric form: if two distinct pentagon
credits are assigned to two negative-curvature tokens, their present total
dual distance is no larger than the crossed assignment. -/
theorem minimumCurvatureCreditDebtEquiv_pentagon_exchange
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (firstPentagon secondPentagon : embedded.InteriorPentagonToken)
    (firstDebt secondDebt : embedded.InteriorNegativeCurvatureToken)
    (hne : firstPentagon ≠ secondPentagon)
    (hfirst : embedded.minimumCurvatureCreditDebtEquiv hsource geometry
        (Sum.inl firstPentagon) = Sum.inl firstDebt)
    (hsecond : embedded.minimumCurvatureCreditDebtEquiv hsource geometry
        (Sum.inl secondPentagon) = Sum.inl secondDebt) :
    (interiorDualGraph
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          embedded.cellulation.interiorFaces).dist
        firstDebt.face firstPentagon.face +
      (interiorDualGraph
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          embedded.cellulation.interiorFaces).dist
        secondDebt.face secondPentagon.face ≤
    (interiorDualGraph
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          embedded.cellulation.interiorFaces).dist
        secondDebt.face firstPentagon.face +
      (interiorDualGraph
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          embedded.cellulation.interiorFaces).dist
        firstDebt.face secondPentagon.face := by
  have hcreditNe :
      (Sum.inl firstPentagon : embedded.PositiveCurvatureCredit) ≠
        Sum.inl secondPentagon := by
    intro heq
    exact hne (Sum.inl.inj heq)
  have hexchange :=
    embedded.minimumCurvatureCreditDebtEquiv_pair_cost_le_swapped
      hsource geometry hcreditNe
  simpa [curvatureCreditPairingCost, hfirst, hsecond] using hexchange

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
