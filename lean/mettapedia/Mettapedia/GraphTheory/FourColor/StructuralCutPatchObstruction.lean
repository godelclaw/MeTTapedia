import Mettapedia.GraphTheory.Hypermap.Patch
import Mettapedia.GraphTheory.FourColor.GoertzelV24SeamExchange
import Mettapedia.GraphTheory.FourColor.GoertzelV24V23ZeroContractionCrossing

/-!
# A plain capped shore is not Gonthier's snip disk

The route closes an open shore by pairing each boundary dart with a new hub
dart.  Its edge permutation is therefore an involution.  In the Coq snip/patch
presentation the disk border is instead one orbit of the *edge* permutation;
the snip construction rewires this permutation around the whole ring.

The distinction matters for a cut with at least three ports: an involution
cannot have a three-element orbit.  The theorem below rules out a direct
`Patch` instance on the route's hub closure.  A useful adapter must construct
the snipped hypermap separately and compare its disk with the route's capped
shore, rather than identify the two structures definitionally.
-/

namespace Mettapedia.GraphTheory.FourColor.StructuralCutPatchObstruction

open Equiv Equiv.Perm
open Mettapedia.GraphTheory
open Mettapedia.GraphTheory.FourColor.GoertzelV24OpenTangleComposition
open Mettapedia.GraphTheory.FourColor.GoertzelV24SeamExchange
open Mettapedia.GraphTheory.FourColor.GoertzelV24RotationCutDartDecomposition

variable {Dg Dd Dr : Type*} [Fintype Dg] [DecidableEq Dg]
  [Fintype Dd] [DecidableEq Dd] [Fintype Dr] [DecidableEq Dr]

omit [DecidableEq Dd] in
private theorem sameCycle_eq_or_apply_of_involutive
    (σ : Perm Dd) (hinv : Function.Involutive σ)
    {x y : Dd} (hcycle : σ.SameCycle x y) : y = x ∨ y = σ x := by
  have hsq : σ ^ 2 = 1 := by
    ext d
    simpa [pow_succ, Perm.mul_apply] using hinv d
  have horder : orderOf σ ≤ 2 :=
    Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one hsq)
  obtain ⟨n, hn, hxy⟩ := hcycle.exists_pow_eq'
  have hn2 : n < 2 := lt_of_lt_of_le hn horder
  have hn01 : n = 0 ∨ n = 1 := by omega
  rcases hn01 with rfl | rfl
  · left
    simpa using hxy.symm
  · right
    simpa using hxy.symm

/-- A patch border of a disk with an involutive edge permutation has at most
two distinct darts.  This is a direct consequence of `Patch.edgeCycle_d`,
independent of the other patch hypotheses. -/
theorem no_three_distinct_disk_border
    {G : Hypermap Dg} {Hd : Hypermap Dd} {Hr : Hypermap Dr}
    {hd : Dd → Dg} {hr : Dr → Dg} {bd : Set Dd} {br : Set Dr}
    (P : Hypermap.Patch G Hd Hr hd hr bd br)
    (hinv : Function.Involutive Hd.edge)
    {x y z : Dd} (hx : x ∈ bd) (hy : y ∈ bd) (hz : z ∈ bd)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : False := by
  have hcy : Hd.edge.SameCycle x y := (P.edgeCycle_d x y hx).2 hy
  have hcz : Hd.edge.SameCycle x z := (P.edgeCycle_d x z hx).2 hz
  rcases sameCycle_eq_or_apply_of_involutive Hd.edge hinv hcy with hyx | hyedge
  · exact hxy hyx.symm
  rcases sameCycle_eq_or_apply_of_involutive Hd.edge hinv hcz with hzx | hzedge
  · exact hxz hzx.symm
  · exact hyz (hyedge.trans hzedge.symm)

section Hub

variable {V I B : Type*} [Fintype I] [DecidableEq I]
  [Fintype B] [DecidableEq B]

/-- The hypermap underlying the route's ordinary capped shore.  Its edge
permutation still pairs each real boundary dart with one hub dart. -/
def hubHypermap (T : OpenTangleData V I B) (ρ : Perm B) :
    Hypermap ((I ⊕ B) ⊕ B) where
  edge := hubAlpha T
  node := (Equiv.sumCongr T.rho ρ)⁻¹
  face := hubPhi T ρ
  cancel3 := by
    intro d
    have hα : (hubAlpha T) ((hubAlpha T) d) = d := by
      simpa only [hubAlpha_apply] using hubAlphaFun_involutive T d
    change (Equiv.sumCongr T.rho ρ)⁻¹
      ((Equiv.sumCongr T.rho ρ * hubAlpha T) (hubAlpha T d)) = d
    rw [Perm.mul_apply, hα]
    exact (Equiv.sumCongr T.rho ρ).symm_apply_apply d

@[simp] theorem hubHypermap_edge (T : OpenTangleData V I B) (ρ : Perm B) :
    (hubHypermap T ρ).edge = hubAlpha T := rfl

theorem hubHypermap_edge_involutive (T : OpenTangleData V I B) (ρ : Perm B) :
    Function.Involutive (hubHypermap T ρ).edge := by
  intro d
  simpa [hubHypermap_edge, hubAlpha_apply] using hubAlphaFun_involutive T d

/-- Three distinct hub darts cannot all lie on the disk border of a `Patch`
whose disk is the ordinary route cap.  This is not restricted to a particular
port index type or a particular choice of hub rotation. -/
theorem no_direct_patch_three_hub_darts
    (T : OpenTangleData V I B) (ρ : Perm B)
    {G : Hypermap Dg} {Hr : Hypermap Dr}
    {hd : ((I ⊕ B) ⊕ B) → Dg} {hr : Dr → Dg}
    {bd : Set ((I ⊕ B) ⊕ B)} {br : Set Dr}
    (P : Hypermap.Patch G (hubHypermap T ρ) Hr hd hr bd br)
    {b₁ b₂ b₃ : B} (h₁ : (Sum.inr b₁ : ((I ⊕ B) ⊕ B)) ∈ bd)
    (h₂ : (Sum.inr b₂ : ((I ⊕ B) ⊕ B)) ∈ bd)
    (h₃ : (Sum.inr b₃ : ((I ⊕ B) ⊕ B)) ∈ bd)
    (h₁₂ : b₁ ≠ b₂) (h₁₃ : b₁ ≠ b₃) (h₂₃ : b₂ ≠ b₃) :
    False := by
  exact no_three_distinct_disk_border P (hubHypermap_edge_involutive T ρ)
    h₁ h₂ h₃ (by simpa using h₁₂) (by simpa using h₁₃) (by simpa using h₂₃)

end Hub

/-! The hypothesis is realized by a bona-fide spherical cubic graph: the
vertex shore consisting of one tetrahedron vertex has three crossing darts.
This does not claim that Gonthier's *snip* fails; it certifies that the route's
plain capped vertex shore and the snipped disk are distinct constructions. -/

section Tetrahedron

open GoertzelV24V23ZeroContractionCrossing
open GoertzelV24FaceDualConnectedness

def tetraKeepA : TetraVertex → Prop := fun v => v = .a

def tetraPortAB : BoundaryDart tetraRotationSystem tetraKeepA :=
  ⟨⟨.abA, by rfl⟩, by
    change TetraVertex.b ≠ TetraVertex.a
    decide⟩

def tetraPortAC : BoundaryDart tetraRotationSystem tetraKeepA :=
  ⟨⟨.acA, by rfl⟩, by
    change TetraVertex.c ≠ TetraVertex.a
    decide⟩

def tetraPortAD : BoundaryDart tetraRotationSystem tetraKeepA :=
  ⟨⟨.adA, by rfl⟩, by
    change TetraVertex.d ≠ TetraVertex.a
    decide⟩

def tetraOuter : RetainedDart tetraRotationSystem tetraKeepA :=
  ⟨.abA, by rfl⟩

noncomputable def tetraStar :
    OpenTangleData {v : TetraVertex // tetraKeepA v}
      (InternalDart tetraRotationSystem tetraKeepA)
      (BoundaryDart tetraRotationSystem tetraKeepA) :=
  OpenTangleData.ofVertexSide tetraRotationSystem tetraKeepA tetraOuter

/-- The one-vertex side of this tetrahedral cut is connected. -/
theorem tetraKeepA_connected :
    ((rotationPrimalGraph tetraRotationSystem).induce
      {v | tetraKeepA v}).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨TetraVertex.a, rfl⟩, ?_⟩
  rintro ⟨v, hv⟩
  change v = TetraVertex.a at hv
  subst v
  rfl

/-- Its complementary triangular side is connected as well, so the three
ports are not an artefact of a disconnected deletion. -/
theorem tetraComplement_connected :
    ((rotationPrimalGraph tetraRotationSystem).induce
      {v | ¬tetraKeepA v}).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨TetraVertex.b, by
    change TetraVertex.b ≠ TetraVertex.a
    decide⟩, ?_⟩
  rintro ⟨v, hv⟩
  cases v with
  | a => exact (hv rfl).elim
  | b => rfl
  | c =>
      apply SimpleGraph.Adj.reachable
      change (rotationPrimalGraph tetraRotationSystem).Adj .b .c
      exact ⟨TetraDart.bcB, rfl, rfl⟩
  | d =>
      apply SimpleGraph.Adj.reachable
      change (rotationPrimalGraph tetraRotationSystem).Adj .b .d
      exact ⟨TetraDart.bdB, rfl, rfl⟩

/-- A three-port shore with both primal sides connected occurs already in the
tetrahedral spherical cubic map.
Any proposed `Patch` with the three hub copies on its disk border contradicts
the edge-orbit condition of `Patch`.  The ambient and remainder hypermaps are
otherwise arbitrary. -/
theorem tetraStar_no_direct_patch
    (ρ : Perm (BoundaryDart tetraRotationSystem tetraKeepA))
    {G : Hypermap Dg} {Hr : Hypermap Dr}
    {hd : ((InternalDart tetraRotationSystem tetraKeepA ⊕
        BoundaryDart tetraRotationSystem tetraKeepA) ⊕
        BoundaryDart tetraRotationSystem tetraKeepA) → Dg}
    {hr : Dr → Dg}
    {bd : Set ((InternalDart tetraRotationSystem tetraKeepA ⊕
        BoundaryDart tetraRotationSystem tetraKeepA) ⊕
        BoundaryDart tetraRotationSystem tetraKeepA)}
    {br : Set Dr}
    (P : Hypermap.Patch G (hubHypermap tetraStar ρ) Hr hd hr bd br)
    (hAB : (Sum.inr tetraPortAB :
      ((InternalDart tetraRotationSystem tetraKeepA ⊕
        BoundaryDart tetraRotationSystem tetraKeepA) ⊕
        BoundaryDart tetraRotationSystem tetraKeepA)) ∈ bd)
    (hAC : (Sum.inr tetraPortAC :
      ((InternalDart tetraRotationSystem tetraKeepA ⊕
        BoundaryDart tetraRotationSystem tetraKeepA) ⊕
        BoundaryDart tetraRotationSystem tetraKeepA)) ∈ bd)
    (hAD : (Sum.inr tetraPortAD :
      ((InternalDart tetraRotationSystem tetraKeepA ⊕
        BoundaryDart tetraRotationSystem tetraKeepA) ⊕
        BoundaryDart tetraRotationSystem tetraKeepA)) ∈ bd) :
    False := by
  exact no_direct_patch_three_hub_darts tetraStar ρ P hAB hAC hAD
    (by intro h; cases congrArg (fun d : BoundaryDart tetraRotationSystem tetraKeepA =>
      d.1.1) h)
    (by intro h; cases congrArg (fun d : BoundaryDart tetraRotationSystem tetraKeepA =>
      d.1.1) h)
    (by intro h; cases congrArg (fun d : BoundaryDart tetraRotationSystem tetraKeepA =>
      d.1.1) h)

end Tetrahedron

end Mettapedia.GraphTheory.FourColor.StructuralCutPatchObstruction
