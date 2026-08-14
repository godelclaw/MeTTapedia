import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionRotation
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutFaceOrbit
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitIncidence

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
open GoertzelV24FaceOrbitIncidence

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

/-- Full retention is a property of the ambient face orbit, rather than of
the dart chosen to name that face. -/
theorem faceFullyRetained_of_dartOrbitFace_eq
    (RS : RotationSystem V E) (keep : V → Prop)
    {leftRoot rightRoot : RS.D}
    (hleft : FaceFullyRetained RS keep leftRoot)
    (hfaces : dartOrbitFace RS leftRoot = dartOrbitFace RS rightRoot) :
    FaceFullyRetained RS keep rightRoot := by
  intro point hrightPoint
  apply hleft point
  exact (Quotient.exact hfaces).trans hrightPoint

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
    Dart RS keep :=
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
    (outer : Dart RS keep)
    (root : RS.D) (hface : FaceFullyRetained RS keep root)
    (point : {point // RS.phi.SameCycle root point}) :
    (rotationSystem RS keep outer).phi
        (openFaceDart RS keep root hface point) =
      openFaceDart RS keep root hface (ambientFacePerm RS root point) := by
  rw [RotationSystem.phi_apply]
  change
    (rotationSystem RS keep outer).rho
      ((rotationSystem RS keep outer).alpha
        (Sum.inl ⟨point.1, hface point.1 point.2⟩)) = _
  rw [rotationSystem_alpha_old_of_internal RS keep outer _
    (alpha_endpoint_keep_of_faceFullyRetained RS keep root hface point),
    rotationSystem_rho_old]
  apply congrArg Sum.inl
  apply Subtype.ext
  rfl

/-- Embedding all darts of a fully retained ambient face into the literal
open region. -/
def openFaceCycleMap
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (root : RS.D) (hface : FaceFullyRetained RS keep root) :
    {point // RS.phi.SameCycle root point} →
      {point //
        (rotationSystem RS keep outer).phi.SameCycle
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
    (rotationSystem RS keep outer).phi
    (openFaceDart RS keep root hface)
    ⟨root, Equiv.Perm.SameCycle.refl RS.phi root⟩
    (fun candidate _ =>
      (openFaceDart_phi RS keep outer root hface candidate).symm)
    power
  rw [hpower] at htransport
  rw [htransport]
  exact (Equiv.Perm.sameCycle_pow_right).2
    (Equiv.Perm.SameCycle.refl _
      (openFaceDart RS keep root hface
        ⟨root, Equiv.Perm.SameCycle.refl RS.phi root⟩))

theorem openFaceCycleMap_injective
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (root : RS.D) (hface : FaceFullyRetained RS keep root) :
    Function.Injective (openFaceCycleMap RS keep outer root hface) := by
  intro left right heq
  apply Subtype.ext
  exact congrArg (forgetOpenDart RS keep) (congrArg Subtype.val heq)

/-- A fully retained ambient face and its literal-open image have exactly the
same complete dart cycle.  Surjectivity is not postulated: it follows from
finite-cycle cardinality and the one-step commutation theorem above. -/
def openFaceCycleEquiv
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (root : RS.D) (hface : FaceFullyRetained RS keep root) :
    {point // RS.phi.SameCycle root point} ≃
      {point //
        (rotationSystem RS keep outer).phi.SameCycle
          (openFaceRoot RS keep root hface)
          point} := by
  let map := openFaceCycleMap RS keep outer root hface
  have hinjective : Function.Injective map :=
    openFaceCycleMap_injective RS keep outer root hface
  have hcard := card_sameCycle_eq_of_injective_map_apply
    (ambientFacePerm RS root)
    (rotationSystem RS keep outer).phi
    (openFaceDart RS keep root hface)
    (openFaceDart_injective RS keep root hface)
    ⟨root, Equiv.Perm.SameCycle.refl RS.phi root⟩
    (fun candidate _ =>
      (openFaceDart_phi RS keep outer root hface candidate).symm)
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
        (rotationSystem RS keep outer).phi.SameCycle
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
          (rotationSystem RS keep outer).phi.SameCycle
            (openFaceRoot RS keep root hface) point).card := hcard
      _ = Fintype.card {point //
          (rotationSystem RS keep outer).phi.SameCycle
            (openFaceRoot RS keep root hface) point} := by
        rw [Fintype.card_subtype]
  exact Equiv.ofBijective map
    ((Fintype.bijective_iff_injective_and_card map).2
      ⟨hinjective, hcardTypes⟩)

/-- The face of one fixed literal-open rotation system occupied by a fully
retained ambient face.  The fixed `outer` dart is essential: it puts every
transported face in the same quotient type, so distinctness and dual
adjacency can be compared across different ambient faces. -/
def openFaceOrbit
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (root : RS.D) (hface : FaceFullyRetained RS keep root) :
    OrbitFace (rotationSystem RS keep outer) :=
  dartOrbitFace (rotationSystem RS keep outer)
    (openFaceRoot RS keep root hface)

/-- Two distinct fully retained ambient faces remain distinct after the
literal opening.  No new boundary stub can fuse two old complete face
cycles. -/
theorem openFaceOrbit_ne_of_ambient_ne
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (leftRoot rightRoot : RS.D)
    (hleft : FaceFullyRetained RS keep leftRoot)
    (hright : FaceFullyRetained RS keep rightRoot)
    (hne : dartOrbitFace RS leftRoot ≠ dartOrbitFace RS rightRoot) :
    openFaceOrbit RS keep outer leftRoot hleft ≠
      openFaceOrbit RS keep outer rightRoot hright := by
  intro hopenFaces
  have hopenCycle :
      (rotationSystem RS keep outer).phi.SameCycle
        (openFaceRoot RS keep leftRoot hleft)
        (openFaceRoot RS keep rightRoot hright) :=
    Quotient.exact hopenFaces
  let target : {point //
      (rotationSystem RS keep outer).phi.SameCycle
        (openFaceRoot RS keep leftRoot hleft) point} :=
    ⟨openFaceRoot RS keep rightRoot hright, hopenCycle⟩
  rcases (openFaceCycleEquiv RS keep outer leftRoot hleft).surjective target with
    ⟨source, hsource⟩
  have hambientRoot : source.1 = rightRoot := by
    have hopenDart :
        openFaceDart RS keep leftRoot hleft source =
          openFaceRoot RS keep rightRoot hright :=
      congrArg Subtype.val hsource
    exact congrArg (forgetOpenDart RS keep) hopenDart
  apply hne
  change Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) leftRoot =
    Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) rightRoot
  apply Quotient.sound
  change RS.phi.SameCycle leftRoot rightRoot
  simpa only [hambientRoot] using source.2

/-- Equality of fully retained open-face images reflects equality of their
ambient face orbits.  Literal opening therefore does not identify two old
complete faces. -/
theorem ambientFaceOrbit_eq_of_openFaceOrbit_eq
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep) (leftRoot rightRoot : RS.D)
    (hleft : FaceFullyRetained RS keep leftRoot)
    (hright : FaceFullyRetained RS keep rightRoot)
    (hopen : openFaceOrbit RS keep outer leftRoot hleft =
      openFaceOrbit RS keep outer rightRoot hright) :
    dartOrbitFace RS leftRoot = dartOrbitFace RS rightRoot := by
  by_contra hambient
  exact (openFaceOrbit_ne_of_ambient_ne RS keep outer leftRoot rightRoot
    hleft hright hambient) hopen

/-- Fully retained roots of the same ambient face determine the same face in
one fixed literal opening.  The proof uses the computed complete-cycle map;
it is not a cardinality identification of unrelated face carriers. -/
theorem openFaceOrbit_eq_of_ambientFaceOrbit_eq
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep) (leftRoot rightRoot : RS.D)
    (hleft : FaceFullyRetained RS keep leftRoot)
    (hright : FaceFullyRetained RS keep rightRoot)
    (hfaces : dartOrbitFace RS leftRoot = dartOrbitFace RS rightRoot) :
    openFaceOrbit RS keep outer leftRoot hleft =
      openFaceOrbit RS keep outer rightRoot hright := by
  apply Quotient.sound
  have hcycle : RS.phi.SameCycle leftRoot rightRoot := Quotient.exact hfaces
  let rightPoint : {point // RS.phi.SameCycle leftRoot point} :=
    ⟨rightRoot, hcycle⟩
  have hmapped : (rotationSystem RS keep outer).phi.SameCycle
      (openFaceRoot RS keep leftRoot hleft)
      (openFaceDart RS keep leftRoot hleft rightPoint) :=
    (openFaceCycleMap RS keep outer leftRoot hleft rightPoint).2
  have hroot : openFaceDart RS keep leftRoot hleft rightPoint =
      openFaceRoot RS keep rightRoot hright := by
    apply congrArg Sum.inl
    apply Subtype.ext
    rfl
  rw [hroot] at hmapped
  exact hmapped

/-- Exact face-equality reflection for fully retained ambient faces in one
literal opened rotation system. -/
theorem openFaceOrbit_eq_iff_ambientFaceOrbit_eq
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep) (leftRoot rightRoot : RS.D)
    (hleft : FaceFullyRetained RS keep leftRoot)
    (hright : FaceFullyRetained RS keep rightRoot) :
    openFaceOrbit RS keep outer leftRoot hleft =
        openFaceOrbit RS keep outer rightRoot hright ↔
      dartOrbitFace RS leftRoot = dartOrbitFace RS rightRoot :=
  ⟨ambientFaceOrbit_eq_of_openFaceOrbit_eq
      RS keep outer leftRoot rightRoot hleft hright,
    openFaceOrbit_eq_of_ambientFaceOrbit_eq
      RS keep outer leftRoot rightRoot hleft hright⟩

/-- The literal-open edge met by one dart of a fully retained ambient face. -/
def openFaceEdge
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (root : RS.D) (hface : FaceFullyRetained RS keep root)
    (point : {point // RS.phi.SameCycle root point}) :
    (rewiredDartSystem RS keep outer).Edge :=
  (rewiredDartSystem RS keep outer).edgeOf
      (openFaceDart RS keep root hface point)

/-- Equal ambient edges on a fully retained face remain the same computed
edge after literally opening the retained region. -/
theorem openFaceEdge_eq_of_ambient_edge_eq
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (root : RS.D) (hface : FaceFullyRetained RS keep root)
    (left right : {point // RS.phi.SameCycle root point})
    (hedge : RS.edgeOf left.1 = RS.edgeOf right.1) :
    openFaceEdge RS keep outer root hface left =
      openFaceEdge RS keep outer root hface right := by
  rcases RS.edge_fiber_two_cases (e := RS.edgeOf left.1)
      (d := left.1) (y := right.1) rfl hedge.symm with hsame | hopposite
  · apply congrArg (openFaceEdge RS keep outer root hface)
    exact Subtype.ext hsame.symm
  · have hdarts : openFaceDart RS keep root hface right =
        (rotationSystem RS keep outer).alpha
          (openFaceDart RS keep root hface left) := by
      change (Sum.inl ⟨right.1, hface right.1 right.2⟩ : Dart RS keep) =
        alpha RS keep (Sum.inl ⟨left.1, hface left.1 left.2⟩)
      rw [alpha_old_of_internal RS keep _
        (alpha_endpoint_keep_of_faceFullyRetained RS keep root hface left)]
      apply congrArg Sum.inl
      apply Subtype.ext
      exact hopposite
    change (rewiredDartSystem RS keep outer).edgeOf
          (openFaceDart RS keep root hface left) =
      (rewiredDartSystem RS keep outer).edgeOf
          (openFaceDart RS keep root hface right)
    rw [hdarts]
    change (rewiredDartSystem RS keep outer).edgeOf
          (openFaceDart RS keep root hface left) =
      (rewiredDartSystem RS keep outer).edgeOf
          ((rewiredDartSystem RS keep outer).alpha
              (openFaceDart RS keep root hface left))
    exact ((rewiredDartSystem RS keep outer).edgeOf_alpha _).symm

/-- Equal ambient edges belonging to two possibly different fully retained
faces become the same edge of one fixed literal-open rotation system.  This
is the cross-face form needed to transport facial-dual adjacency. -/
theorem openFaceEdge_eq_of_ambient_edge_eq_two_faces
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (leftRoot rightRoot : RS.D)
    (hleft : FaceFullyRetained RS keep leftRoot)
    (hright : FaceFullyRetained RS keep rightRoot)
    (left : {point // RS.phi.SameCycle leftRoot point})
    (right : {point // RS.phi.SameCycle rightRoot point})
    (hedge : RS.edgeOf left.1 = RS.edgeOf right.1) :
    openFaceEdge RS keep outer leftRoot hleft left =
      openFaceEdge RS keep outer rightRoot hright right := by
  rcases RS.edge_fiber_two_cases (e := RS.edgeOf left.1)
      (d := left.1) (y := right.1) rfl hedge.symm with hsame | hopposite
  · apply congrArg (rewiredDartSystem RS keep outer).edgeOf
    apply congrArg Sum.inl
    apply Subtype.ext
    exact hsame.symm
  · have hdarts : openFaceDart RS keep rightRoot hright right =
        (rotationSystem RS keep outer).alpha
          (openFaceDart RS keep leftRoot hleft left) := by
      change (Sum.inl ⟨right.1, hright right.1 right.2⟩ : Dart RS keep) =
        alpha RS keep (Sum.inl ⟨left.1, hleft left.1 left.2⟩)
      rw [alpha_old_of_internal RS keep _
        (alpha_endpoint_keep_of_faceFullyRetained
          RS keep leftRoot hleft left)]
      apply congrArg Sum.inl
      apply Subtype.ext
      exact hopposite
    change (rewiredDartSystem RS keep outer).edgeOf
          (openFaceDart RS keep leftRoot hleft left) =
      (rewiredDartSystem RS keep outer).edgeOf
          (openFaceDart RS keep rightRoot hright right)
    rw [hdarts]
    exact ((rewiredDartSystem RS keep outer).edgeOf_alpha _).symm

/-- Conversely, the literal opening does not identify ambient edges that
belong to two different fully retained faces. -/
theorem ambient_edge_eq_of_openFaceEdge_eq_two_faces
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (leftRoot rightRoot : RS.D)
    (hleft : FaceFullyRetained RS keep leftRoot)
    (hright : FaceFullyRetained RS keep rightRoot)
    (left : {point // RS.phi.SameCycle leftRoot point})
    (right : {point // RS.phi.SameCycle rightRoot point})
    (hedge : openFaceEdge RS keep outer leftRoot hleft left =
      openFaceEdge RS keep outer rightRoot hright right) :
    RS.edgeOf left.1 = RS.edgeOf right.1 := by
  have hcases := ((rewiredDartSystem RS keep outer).edgeOf_eq_edgeOf_iff
      (openFaceDart RS keep leftRoot hleft left)
      (openFaceDart RS keep rightRoot hright right)).1 hedge
  rcases hcases with hsame | hopposite
  · change (Sum.inl ⟨left.1, hleft left.1 left.2⟩ : Dart RS keep) =
      Sum.inl ⟨right.1, hright right.1 right.2⟩ at hsame
    have hvalues : left.1 = right.1 := by
      exact congrArg Subtype.val (Sum.inl.inj hsame)
    rw [hvalues]
  · change (Sum.inl ⟨left.1, hleft left.1 left.2⟩ : Dart RS keep) =
      alpha RS keep (Sum.inl ⟨right.1, hright right.1 right.2⟩) at hopposite
    rw [alpha_old_of_internal RS keep _
      (alpha_endpoint_keep_of_faceFullyRetained
        RS keep rightRoot hright right)] at hopposite
    have hvalues : left.1 = RS.alpha right.1 := by
      exact congrArg Subtype.val (Sum.inl.inj hopposite)
    rw [hvalues, RS.edge_alpha]

/-- Exact cross-face edge-incidence preservation for two fully retained
ambient faces. -/
theorem openFaceEdge_eq_iff_ambient_edge_eq_two_faces
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (leftRoot rightRoot : RS.D)
    (hleft : FaceFullyRetained RS keep leftRoot)
    (hright : FaceFullyRetained RS keep rightRoot)
    (left : {point // RS.phi.SameCycle leftRoot point})
    (right : {point // RS.phi.SameCycle rightRoot point}) :
    openFaceEdge RS keep outer leftRoot hleft left =
        openFaceEdge RS keep outer rightRoot hright right ↔
      RS.edgeOf left.1 = RS.edgeOf right.1 :=
  ⟨ambient_edge_eq_of_openFaceEdge_eq_two_faces
      RS keep outer leftRoot rightRoot hleft hright left right,
    openFaceEdge_eq_of_ambient_edge_eq_two_faces
      RS keep outer leftRoot rightRoot hleft hright left right⟩

/-- The literal opening does not identify two distinct old ambient edges on
a fully retained face. -/
theorem ambient_edge_eq_of_openFaceEdge_eq
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (root : RS.D) (hface : FaceFullyRetained RS keep root)
    (left right : {point // RS.phi.SameCycle root point})
    (hedge : openFaceEdge RS keep outer root hface left =
      openFaceEdge RS keep outer root hface right) :
    RS.edgeOf left.1 = RS.edgeOf right.1 := by
  have hcases := ((rewiredDartSystem RS keep outer).edgeOf_eq_edgeOf_iff
      (openFaceDart RS keep root hface left)
      (openFaceDart RS keep root hface right)).1 hedge
  rcases hcases with hsame | hopposite
  · change (Sum.inl ⟨left.1, hface left.1 left.2⟩ : Dart RS keep) =
      Sum.inl ⟨right.1, hface right.1 right.2⟩ at hsame
    have hretained :
        (⟨left.1, hface left.1 left.2⟩ : RetainedDart RS keep) =
          ⟨right.1, hface right.1 right.2⟩ :=
      Sum.inl.inj hsame
    have hvalues : left.1 = right.1 :=
      congrArg (fun dart : RetainedDart RS keep => dart.1) hretained
    rw [hvalues]
  · change (Sum.inl ⟨left.1, hface left.1 left.2⟩ : Dart RS keep) =
      alpha RS keep (Sum.inl ⟨right.1, hface right.1 right.2⟩) at hopposite
    rw [alpha_old_of_internal RS keep _
      (alpha_endpoint_keep_of_faceFullyRetained
        RS keep root hface right)] at hopposite
    have hvalues : left.1 = RS.alpha right.1 := by
      exact congrArg Subtype.val (Sum.inl.inj hopposite)
    rw [hvalues, RS.edge_alpha]

/-- Exact edge-incidence preservation for a fully retained face. -/
theorem openFaceEdge_eq_iff_ambient_edge_eq
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (root : RS.D) (hface : FaceFullyRetained RS keep root)
    (left right : {point // RS.phi.SameCycle root point}) :
    openFaceEdge RS keep outer root hface left =
        openFaceEdge RS keep outer root hface right ↔
      RS.edgeOf left.1 = RS.edgeOf right.1 :=
  ⟨ambient_edge_eq_of_openFaceEdge_eq RS keep outer root hface left right,
    openFaceEdge_eq_of_ambient_edge_eq RS keep outer root hface left right⟩

/-- A shared ambient edge between two distinct fully retained faces remains
an edge of the facial dual after the literal opening.  Thus the opening does
not merely preserve each face separately: it preserves the corresponding
dual adjacency inside one fixed opened map. -/
theorem openFaceOrbit_adj_of_shared_ambient_edge
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (leftRoot rightRoot : RS.D)
    (hleft : FaceFullyRetained RS keep leftRoot)
    (hright : FaceFullyRetained RS keep rightRoot)
    (hne : dartOrbitFace RS leftRoot ≠ dartOrbitFace RS rightRoot)
    (left : {point // RS.phi.SameCycle leftRoot point})
    (right : {point // RS.phi.SameCycle rightRoot point})
    (hedge : RS.edgeOf left.1 = RS.edgeOf right.1) :
    (interiorDualGraph
      (orbitFaceBoundary (rotationSystem RS keep outer))
      (Finset.univ : Finset (OrbitFace (rotationSystem RS keep outer)))).Adj
        ⟨openFaceOrbit RS keep outer leftRoot hleft, Finset.mem_univ _⟩
        ⟨openFaceOrbit RS keep outer rightRoot hright, Finset.mem_univ _⟩ := by
  apply interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
    (orbitFaceBoundary (rotationSystem RS keep outer))
    (Finset.univ : Finset (OrbitFace (rotationSystem RS keep outer)))
    (orbitFace_incidence_le_two (rotationSystem RS keep outer))
    (openFaceOrbit_ne_of_ambient_ne
      RS keep outer leftRoot rightRoot hleft hright hne)
  · change openFaceEdge RS keep outer leftRoot hleft left ∈
      orbitFaceBoundary (rotationSystem RS keep outer)
        (openFaceOrbit RS keep outer leftRoot hleft)
    rw [mem_orbitFaceBoundary_iff]
    refine ⟨openFaceDart RS keep leftRoot hleft left, ?_, rfl⟩
    rw [mem_orbitFaceDarts_iff]
    apply Quotient.sound
    exact (openFaceCycleMap RS keep outer leftRoot hleft left).2.symm
  · change openFaceEdge RS keep outer leftRoot hleft left ∈
      orbitFaceBoundary (rotationSystem RS keep outer)
        (openFaceOrbit RS keep outer rightRoot hright)
    rw [openFaceEdge_eq_of_ambient_edge_eq_two_faces
      RS keep outer leftRoot rightRoot hleft hright left right hedge]
    rw [mem_orbitFaceBoundary_iff]
    refine ⟨openFaceDart RS keep rightRoot hright right, ?_, rfl⟩
    rw [mem_orbitFaceDarts_iff]
    apply Quotient.sound
    exact (openFaceCycleMap RS keep outer rightRoot hright right).2.symm

/-- Every open dual adjacency between two fully retained face images comes
from a shared ambient edge occurrence.  The cycle equivalences rule out a
new adjacency manufactured solely by the boundary stubs. -/
theorem exists_shared_ambient_edge_of_openFaceOrbit_adj
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (leftRoot rightRoot : RS.D)
    (hleft : FaceFullyRetained RS keep leftRoot)
    (hright : FaceFullyRetained RS keep rightRoot)
    (hadj :
      (interiorDualGraph
        (orbitFaceBoundary (rotationSystem RS keep outer))
        (Finset.univ : Finset (OrbitFace (rotationSystem RS keep outer)))).Adj
          ⟨openFaceOrbit RS keep outer leftRoot hleft, Finset.mem_univ _⟩
          ⟨openFaceOrbit RS keep outer rightRoot hright, Finset.mem_univ _⟩) :
    ∃ left : {point // RS.phi.SameCycle leftRoot point},
      ∃ right : {point // RS.phi.SameCycle rightRoot point},
        RS.edgeOf left.1 = RS.edgeOf right.1 := by
  rcases (interiorDualGraph_adj_iff
      (orbitFaceBoundary (rotationSystem RS keep outer))
      (Finset.univ : Finset (OrbitFace (rotationSystem RS keep outer)))).1 hadj with
    ⟨_, edge, _, hedgeLeft, hedgeRight⟩
  rw [mem_orbitFaceBoundary_iff] at hedgeLeft hedgeRight
  rcases hedgeLeft with ⟨leftDart, hleftDartFace, hleftEdge⟩
  rcases hedgeRight with ⟨rightDart, hrightDartFace, hrightEdge⟩
  have hleftCycle :
      (rotationSystem RS keep outer).phi.SameCycle
        (openFaceRoot RS keep leftRoot hleft) leftDart := by
    rw [mem_orbitFaceDarts_iff] at hleftDartFace
    exact (Quotient.exact hleftDartFace).symm
  have hrightCycle :
      (rotationSystem RS keep outer).phi.SameCycle
        (openFaceRoot RS keep rightRoot hright) rightDart := by
    rw [mem_orbitFaceDarts_iff] at hrightDartFace
    exact (Quotient.exact hrightDartFace).symm
  rcases (openFaceCycleEquiv RS keep outer leftRoot hleft).surjective
      ⟨leftDart, hleftCycle⟩ with ⟨left, hleftImage⟩
  rcases (openFaceCycleEquiv RS keep outer rightRoot hright).surjective
      ⟨rightDart, hrightCycle⟩ with ⟨right, hrightImage⟩
  have hleftImageDart : openFaceDart RS keep leftRoot hleft left = leftDart :=
    congrArg Subtype.val hleftImage
  have hrightImageDart : openFaceDart RS keep rightRoot hright right = rightDart :=
    congrArg Subtype.val hrightImage
  refine ⟨left, right, ?_⟩
  apply ambient_edge_eq_of_openFaceEdge_eq_two_faces
    RS keep outer leftRoot rightRoot hleft hright left right
  calc
    openFaceEdge RS keep outer leftRoot hleft left = edge := by
      unfold openFaceEdge
      rw [hleftImageDart]
      exact hleftEdge
    _ = openFaceEdge RS keep outer rightRoot hright right := by
      unfold openFaceEdge
      rw [hrightImageDart]
      exact hrightEdge.symm

/-- Exact facial-dual adjacency transport for two distinct fully retained
ambient faces. -/
theorem openFaceOrbit_adj_iff_exists_shared_ambient_edge
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (leftRoot rightRoot : RS.D)
    (hleft : FaceFullyRetained RS keep leftRoot)
    (hright : FaceFullyRetained RS keep rightRoot)
    (hne : dartOrbitFace RS leftRoot ≠ dartOrbitFace RS rightRoot) :
    (interiorDualGraph
      (orbitFaceBoundary (rotationSystem RS keep outer))
      (Finset.univ : Finset (OrbitFace (rotationSystem RS keep outer)))).Adj
        ⟨openFaceOrbit RS keep outer leftRoot hleft, Finset.mem_univ _⟩
        ⟨openFaceOrbit RS keep outer rightRoot hright, Finset.mem_univ _⟩ ↔
      ∃ left : {point // RS.phi.SameCycle leftRoot point},
        ∃ right : {point // RS.phi.SameCycle rightRoot point},
          RS.edgeOf left.1 = RS.edgeOf right.1 := by
  constructor
  · exact exists_shared_ambient_edge_of_openFaceOrbit_adj
      RS keep outer leftRoot rightRoot hleft hright
  · rintro ⟨left, right, hedge⟩
    exact openFaceOrbit_adj_of_shared_ambient_edge
      RS keep outer leftRoot rightRoot hleft hright hne left right hedge

/-- On the induced family of fully retained faces, literal opening preserves
the facial-dual graph exactly.  This packages the edge-occurrence statement
above in the graph language used by the source crosscuts: neither an ambient
adjacency is lost nor a new one is created between retained face images. -/
theorem openFaceOrbit_adj_iff_ambientFaceOrbit_adj
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (leftRoot rightRoot : RS.D)
    (hleft : FaceFullyRetained RS keep leftRoot)
    (hright : FaceFullyRetained RS keep rightRoot)
    (hne : dartOrbitFace RS leftRoot ≠ dartOrbitFace RS rightRoot) :
    (interiorDualGraph
      (orbitFaceBoundary (rotationSystem RS keep outer))
      (Finset.univ : Finset (OrbitFace (rotationSystem RS keep outer)))).Adj
        ⟨openFaceOrbit RS keep outer leftRoot hleft, Finset.mem_univ _⟩
        ⟨openFaceOrbit RS keep outer rightRoot hright, Finset.mem_univ _⟩ ↔
      (interiorDualGraph (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).Adj
          ⟨dartOrbitFace RS leftRoot, Finset.mem_univ _⟩
          ⟨dartOrbitFace RS rightRoot, Finset.mem_univ _⟩ := by
  rw [openFaceOrbit_adj_iff_exists_shared_ambient_edge
    RS keep outer leftRoot rightRoot hleft hright hne]
  constructor
  · rintro ⟨left, right, hedge⟩
    apply interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      (orbitFace_incidence_le_two RS) hne
    · rw [mem_orbitFaceBoundary_iff]
      exact ⟨left.1, by
        rw [mem_orbitFaceDarts_iff]
        exact Quotient.sound left.2.symm, rfl⟩
    · rw [mem_orbitFaceBoundary_iff]
      exact ⟨right.1, by
        rw [mem_orbitFaceDarts_iff]
        exact Quotient.sound right.2.symm, hedge.symm⟩
  · intro hadj
    rcases (interiorDualGraph_adj_iff
        (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).1 hadj with
      ⟨_, edge, _, hedgeLeft, hedgeRight⟩
    rw [mem_orbitFaceBoundary_iff] at hedgeLeft hedgeRight
    rcases hedgeLeft with ⟨leftDart, hleftDart, hleftEdge⟩
    rcases hedgeRight with ⟨rightDart, hrightDart, hrightEdge⟩
    have hleftCycle : RS.phi.SameCycle leftRoot leftDart := by
      rw [mem_orbitFaceDarts_iff] at hleftDart
      exact Quotient.exact hleftDart.symm
    have hrightCycle : RS.phi.SameCycle rightRoot rightDart := by
      rw [mem_orbitFaceDarts_iff] at hrightDart
      exact Quotient.exact hrightDart.symm
    exact ⟨⟨leftDart, hleftCycle⟩, ⟨rightDart, hrightCycle⟩,
      hleftEdge.trans hrightEdge.symm⟩

end

end GoertzelV24OpenRegionFaceTransport

end Mettapedia.GraphTheory.FourColor
