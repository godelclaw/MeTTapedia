import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionRotation
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutFaceOrbit

/-!
# Untouched faces of a literal open region

Opening a vertex region replaces every edge leaving the retained side by a
fresh degree-one stub.  A face whose complete ambient dart orbit stays on the
retained side should therefore remain literally unchanged.  This file proves
that statement at the face-permutation level.

This is generic rotation-system transport, not an assumption about the source
annulus.  A later source construction may use it to carry closed-map facial
geometry into the actual open annulus, once it proves that the relevant face
orbit is retained.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenRegionFaceTransport

open GoertzelV24OpenRegionRotation
open GoertzelV24OrderedCutFaceOrbit
open GoertzelV24RotationCutDartDecomposition

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- An ambient face is fully retained when every dart on its face orbit is
based at a retained vertex.  The condition on the opposite endpoint needed
for the next open face step follows by applying this predicate to `RS.phi`.
-/
def FaceFullyRetained (RS : RotationSystem V E) (keep : V → Prop)
    (root : RS.D) : Prop :=
  ∀ point, RS.phi.SameCycle root point → keep (RS.vertOf point)

/-- The ambient face permutation restricts to its own complete orbit. -/
def ambientFacePerm (RS : RotationSystem V E) (root : RS.D) :
    Equiv.Perm {point // RS.phi.SameCycle root point} :=
  RS.phi.subtypePerm (fun _ => Equiv.Perm.sameCycle_apply_right)

@[simp]
theorem ambientFacePerm_val (RS : RotationSystem V E) (root : RS.D)
    (point : {point // RS.phi.SameCycle root point}) :
    (ambientFacePerm RS root point).1 = RS.phi point.1 :=
  rfl

/-- The chosen ambient face root, regarded as an old dart of the open
region. -/
def openFaceRoot (RS : RotationSystem V E) (keep : V → Prop)
    (root : RS.D) (hface : FaceFullyRetained RS keep root) :
    Dart RS keep :=
  Sum.inl ⟨root,
    hface root (Equiv.Perm.SameCycle.refl RS.phi root)⟩

/-- Every dart of a fully retained face becomes an old dart of the literal
open region. -/
def openFaceDart (RS : RotationSystem V E) (keep : V → Prop)
    (root : RS.D) (hface : FaceFullyRetained RS keep root)
    (point : {point // RS.phi.SameCycle root point}) :
    (rotationSystem RS keep (openFaceRoot RS keep root hface)).D :=
  Sum.inl ⟨point.1, hface point.1 point.2⟩

/-- Forget the open-region tag of a dart, sending a fresh boundary stub to
the old dart to which it was attached. -/
def forgetOpenDart (RS : RotationSystem V E) (keep : V → Prop) :
    Dart RS keep → RS.D
  | Sum.inl old => old.1
  | Sum.inr boundary => boundary.1.1

@[simp]
theorem forgetOpenDart_openFaceDart
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : RS.D) (hface : FaceFullyRetained RS keep root)
    (point : {point // RS.phi.SameCycle root point}) :
    forgetOpenDart RS keep (openFaceDart RS keep root hface point) = point.1 :=
  rfl

theorem openFaceDart_injective
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : RS.D) (hface : FaceFullyRetained RS keep root) :
    Function.Injective (openFaceDart RS keep root hface) := by
  intro left right heq
  apply Subtype.ext
  exact congrArg (forgetOpenDart RS keep) heq

/-- The opposite endpoint of a dart on a fully retained face is retained.
Equivalently, following this face never reaches a newly created boundary stub.
-/
theorem alpha_endpoint_keep_of_faceFullyRetained
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : RS.D) (hface : FaceFullyRetained RS keep root)
    (point : {point // RS.phi.SameCycle root point}) :
    keep (RS.vertOf (RS.alpha point.1)) := by
  have hnext : RS.phi.SameCycle root (RS.phi point.1) :=
    point.2.trans
      (Mettapedia.GraphTheory.EquivPermSameCycle.step_right RS.phi point.1)
  have hkeep := hface (RS.phi point.1) hnext
  rwa [RS.vert_phi_eq_vert_alpha] at hkeep

/-- On a fully retained ambient face, one literal-open face step is exactly
the old ambient face step after embedding old darts into the open carrier. -/
theorem openFaceDart_phi
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : RS.D) (hface : FaceFullyRetained RS keep root)
    (point : {point // RS.phi.SameCycle root point}) :
    let openRoot := openFaceRoot RS keep root hface
    (rotationSystem RS keep openRoot).phi
        (openFaceDart RS keep root hface point) =
      openFaceDart RS keep root hface (ambientFacePerm RS root point) := by
  dsimp only
  rw [RotationSystem.phi_apply]
  change
    (rotationSystem RS keep (openFaceRoot RS keep root hface)).rho
      ((rotationSystem RS keep (openFaceRoot RS keep root hface)).alpha
        (Sum.inl ⟨point.1, hface point.1 point.2⟩)) = _
  rw [rotationSystem_alpha_old_of_internal RS keep _ _
    (alpha_endpoint_keep_of_faceFullyRetained RS keep root hface point),
    rotationSystem_rho_old]
  apply congrArg Sum.inl
  apply Subtype.ext
  rfl

/-- Embedding all darts of a fully retained ambient face into the literal
open region. -/
def openFaceCycleMap
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : RS.D) (hface : FaceFullyRetained RS keep root) :
    {point // RS.phi.SameCycle root point} →
      {point //
        (rotationSystem RS keep
          (openFaceRoot RS keep root hface)).phi.SameCycle
          (openFaceRoot RS keep root hface)
          point} := by
  intro point
  refine ⟨openFaceDart RS keep root hface point, ?_⟩
  have hsource : (ambientFacePerm RS root).SameCycle
      ⟨root, Equiv.Perm.SameCycle.refl RS.phi root⟩ point :=
    Equiv.Perm.SameCycle.subtypePerm point.2
  rcases hsource.exists_nat_pow_eq with ⟨power, hpower⟩
  have htransport := map_pow_of_map_apply_on_cycle
    (ambientFacePerm RS root)
    (rotationSystem RS keep
      (openFaceRoot RS keep root hface)).phi
    (openFaceDart RS keep root hface)
    ⟨root, Equiv.Perm.SameCycle.refl RS.phi root⟩
    (fun candidate _ =>
      (openFaceDart_phi RS keep root hface candidate).symm)
    power
  rw [hpower] at htransport
  rw [htransport]
  exact (Equiv.Perm.sameCycle_pow_right).2
    (Equiv.Perm.SameCycle.refl _
      (openFaceDart RS keep root hface
        ⟨root, Equiv.Perm.SameCycle.refl RS.phi root⟩))

theorem openFaceCycleMap_injective
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : RS.D) (hface : FaceFullyRetained RS keep root) :
    Function.Injective (openFaceCycleMap RS keep root hface) := by
  intro left right heq
  apply Subtype.ext
  exact congrArg (forgetOpenDart RS keep) (congrArg Subtype.val heq)

/-- A fully retained ambient face and its literal-open image have exactly the
same complete dart cycle.  Surjectivity is not postulated: it follows from
finite-cycle cardinality and the one-step commutation theorem above. -/
def openFaceCycleEquiv
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : RS.D) (hface : FaceFullyRetained RS keep root) :
    {point // RS.phi.SameCycle root point} ≃
      {point //
        (rotationSystem RS keep
          (openFaceRoot RS keep root hface)).phi.SameCycle
          (openFaceRoot RS keep root hface)
          point} := by
  let map := openFaceCycleMap RS keep root hface
  have hinjective : Function.Injective map :=
    openFaceCycleMap_injective RS keep root hface
  have hcard := card_sameCycle_eq_of_injective_map_apply
    (ambientFacePerm RS root)
    (rotationSystem RS keep
      (openFaceRoot RS keep root hface)).phi
    (openFaceDart RS keep root hface)
    (openFaceDart_injective RS keep root hface)
    ⟨root, Equiv.Perm.SameCycle.refl RS.phi root⟩
    (fun candidate _ =>
      (openFaceDart_phi RS keep root hface candidate).symm)
  have hsourceAll :
      (Finset.univ.filter fun point =>
        (ambientFacePerm RS root).SameCycle
          ⟨root, Equiv.Perm.SameCycle.refl RS.phi root⟩ point) =
        Finset.univ := by
    ext point
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hsource : (ambientFacePerm RS root).SameCycle
        ⟨root, Equiv.Perm.SameCycle.refl RS.phi root⟩ point :=
      Equiv.Perm.SameCycle.subtypePerm point.2
    exact iff_true_intro hsource
  have hcardTypes : Fintype.card {point // RS.phi.SameCycle root point} =
      Fintype.card {point //
        (rotationSystem RS keep
          (openFaceRoot RS keep root hface)).phi.SameCycle
          (openFaceRoot RS keep root hface)
          point} := by
    calc
      Fintype.card {point // RS.phi.SameCycle root point} =
          (Finset.univ.filter fun point =>
            (ambientFacePerm RS root).SameCycle
              ⟨root, Equiv.Perm.SameCycle.refl RS.phi root⟩ point).card := by
        rw [hsourceAll]
        simp
      _ = (Finset.univ.filter fun point =>
          (rotationSystem RS keep
            (openFaceRoot RS keep root hface)).phi.SameCycle
            (openFaceRoot RS keep root hface) point).card := hcard
      _ = Fintype.card {point //
          (rotationSystem RS keep
            (openFaceRoot RS keep root hface)).phi.SameCycle
            (openFaceRoot RS keep root hface) point} := by
        rw [Fintype.card_subtype]
  exact Equiv.ofBijective map
    ((Fintype.bijective_iff_injective_and_card map).2
      ⟨hinjective, hcardTypes⟩)

end

end GoertzelV24OpenRegionFaceTransport

end Mettapedia.GraphTheory.FourColor
