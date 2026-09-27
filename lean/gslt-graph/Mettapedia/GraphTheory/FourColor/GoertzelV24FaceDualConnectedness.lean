import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitPartitionBridge

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FaceDualConnectedness

open GoertzelV24FaceOrbitIncidence

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- The primal simple graph computed from the endpoint data of a rotation
system. -/
def rotationPrimalGraph (RS : RotationSystem V E) : SimpleGraph V where
  Adj left right :=
    ∃ dart : RS.D,
      RS.vertOf dart = left ∧ RS.vertOf (RS.alpha dart) = right
  symm := ⟨by
    rintro left right ⟨dart, hleft, hright⟩
    refine ⟨RS.alpha dart, hright, ?_⟩
    rw [RS.alpha_involutive, hleft]⟩
  loopless := ⟨by
    rintro vertex ⟨dart, hleft, hright⟩
    exact RS.no_self_loops dart (hleft.trans hright.symm)⟩

theorem rotationPrimalGraph_adj_iff (RS : RotationSystem V E)
    {left right : V} :
    (rotationPrimalGraph RS).Adj left right ↔
      ∃ dart : RS.D,
        RS.vertOf dart = left ∧ RS.vertOf (RS.alpha dart) = right := by
  rfl

/-- The stored vertex permutation is genuinely one cyclic order on every
nonempty dart fiber. This supplies the mathematical condition omitted by the
bare `RotationSystem` record's vertex-preservation field. -/
def VertexRotationCyclic (RS : RotationSystem V E) : Prop :=
  ∀ left right : RS.D,
    RS.vertOf left = RS.vertOf right → RS.rho.SameCycle left right

/-- A quotient face packaged as a vertex of the full facial dual. -/
def orbitFaceVertex (RS : RotationSystem V E) (dart : RS.D) :
    AmbientFace (Finset.univ : Finset (OrbitFace RS)) :=
  ⟨dartOrbitFace RS dart, Finset.mem_univ _⟩

theorem edgeOf_mem_orbitFaceBoundary_dartOrbitFace
    (RS : RotationSystem V E) (dart : RS.D) :
    RS.edgeOf dart ∈ orbitFaceBoundary RS (dartOrbitFace RS dart) := by
  exact (mem_orbitFaceBoundary_iff RS _ _).2
    ⟨dart, (mem_orbitFaceDarts_iff RS _ _).2 rfl, rfl⟩

/-- Crossing one primal edge either stays in the same quotient face or gives
one edge of the full facial dual. -/
theorem orbitFaceVertex_reachable_alpha
    (RS : RotationSystem V E) (dart : RS.D) :
    (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Reachable
        (orbitFaceVertex RS dart) (orbitFaceVertex RS (RS.alpha dart)) := by
  by_cases hsame :
      dartOrbitFace RS dart = dartOrbitFace RS (RS.alpha dart)
  · have hvertices :
        orbitFaceVertex RS dart = orbitFaceVertex RS (RS.alpha dart) :=
      Subtype.ext hsame
    rw [hvertices]
  · apply SimpleGraph.Adj.reachable
    apply interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
      (orbitFace_incidence_le_two RS) hsame
    · exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS dart
    · change RS.edgeOf dart ∈
        orbitFaceBoundary RS (dartOrbitFace RS (RS.alpha dart))
      simpa [RS.edge_alpha] using
        edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha dart)

theorem dartOrbitFace_alpha_eq_dartOrbitFace_rho
    (RS : RotationSystem V E) (dart : RS.D) :
    dartOrbitFace RS (RS.alpha dart) = dartOrbitFace RS (RS.rho dart) := by
  apply Quotient.sound
  change RS.phi.SameCycle (RS.alpha dart) (RS.rho dart)
  refine ⟨1, ?_⟩
  simp [RotationSystem.phi_apply, RS.alpha_involutive]

theorem orbitFaceVertex_alpha_eq_orbitFaceVertex_rho
    (RS : RotationSystem V E) (dart : RS.D) :
    orbitFaceVertex RS (RS.alpha dart) =
      orbitFaceVertex RS (RS.rho dart) :=
  Subtype.ext (dartOrbitFace_alpha_eq_dartOrbitFace_rho RS dart)

theorem orbitFaceVertex_reachable_rho
    (RS : RotationSystem V E) (dart : RS.D) :
    (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Reachable
        (orbitFaceVertex RS dart) (orbitFaceVertex RS (RS.rho dart)) := by
  rw [← orbitFaceVertex_alpha_eq_orbitFaceVertex_rho RS dart]
  exact orbitFaceVertex_reachable_alpha RS dart

theorem orbitFaceVertex_reachable_rho_symm
    (RS : RotationSystem V E) (dart : RS.D) :
    (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Reachable
        (orbitFaceVertex RS dart) (orbitFaceVertex RS (RS.rho.symm dart)) := by
  have hcross := orbitFaceVertex_reachable_alpha RS (RS.rho.symm dart)
  have hcross' :
      (interiorDualGraph (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).Reachable
          (orbitFaceVertex RS (RS.rho.symm dart))
          (orbitFaceVertex RS dart) := by
    rw [orbitFaceVertex_alpha_eq_orbitFaceVertex_rho] at hcross
    simpa using hcross
  exact hcross'.symm

/-- Darts in the same stored vertex-rotation cycle have faces connected in
the full facial dual. -/
theorem orbitFaceVertex_reachable_of_rho_sameCycle
    (RS : RotationSystem V E) {left right : RS.D}
    (hsame : RS.rho.SameCycle left right) :
    (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Reachable
        (orbitFaceVertex RS left) (orbitFaceVertex RS right) := by
  rcases hsame with ⟨power, hpower⟩
  have hpowers :
      (interiorDualGraph (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).Reachable
          (orbitFaceVertex RS left)
          (orbitFaceVertex RS ((RS.rho ^ power) left)) := by
    exact zpow_induction_left (g := RS.rho)
      (P := fun permutation =>
        (interiorDualGraph (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS))).Reachable
            (orbitFaceVertex RS left)
            (orbitFaceVertex RS (permutation left)))
      (by simp)
      (fun permutation hreach => hreach.trans (by
        simpa using orbitFaceVertex_reachable_rho RS (permutation left)))
      (fun permutation hreach => hreach.trans (by
        simpa using orbitFaceVertex_reachable_rho_symm RS (permutation left)))
      power
  rw [hpower] at hpowers
  exact hpowers

theorem exists_dart_vertOf_eq_of_isCubic
    (RS : RotationSystem V E) (hcubic : RS.IsCubic) (vertex : V) :
    ∃ dart : RS.D, RS.vertOf dart = vertex := by
  have hnonempty : (RS.dartsAt vertex).Nonempty := by
    rw [← Finset.card_pos, hcubic vertex]
    omega
  rcases hnonempty with ⟨dart, hdart⟩
  exact ⟨dart, by simpa [RotationSystem.dartsAt] using hdart⟩

/-- A primal walk can be lifted to facial-dual reachability. Local changes of
the dart chosen at an intermediate vertex are supplied by the actual cyclic
vertex rotation. -/
theorem orbitFaceVertex_reachable_of_primalReachable
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) {left right : RS.D}
    (hprimal : (rotationPrimalGraph RS).Reachable
      (RS.vertOf left) (RS.vertOf right)) :
    (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Reachable
        (orbitFaceVertex RS left) (orbitFaceVertex RS right) := by
  let FaceReachableAt : V → V → Prop := fun leftVertex rightVertex =>
    ∀ leftDart rightDart : RS.D,
      RS.vertOf leftDart = leftVertex →
      RS.vertOf rightDart = rightVertex →
      (interiorDualGraph (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).Reachable
          (orbitFaceVertex RS leftDart) (orbitFaceVertex RS rightDart)
  have hrefl : ∀ vertex, FaceReachableAt vertex vertex := by
    intro vertex leftDart rightDart hleft hright
    apply orbitFaceVertex_reachable_of_rho_sameCycle RS
    exact hrotation leftDart rightDart (hleft.trans hright.symm)
  have hadj : ∀ {leftVertex rightVertex},
      (rotationPrimalGraph RS).Adj leftVertex rightVertex →
        FaceReachableAt leftVertex rightVertex := by
    rintro leftVertex rightVertex ⟨crossing, hleftCrossing, hrightCrossing⟩
    intro leftDart rightDart hleft hright
    have htoCrossing := orbitFaceVertex_reachable_of_rho_sameCycle RS
      (hrotation leftDart crossing (hleft.trans hleftCrossing.symm))
    have hacross := orbitFaceVertex_reachable_alpha RS crossing
    have hfromCrossing := orbitFaceVertex_reachable_of_rho_sameCycle RS
      (hrotation (RS.alpha crossing) rightDart
        (hrightCrossing.trans hright.symm))
    exact (htoCrossing.trans hacross).trans hfromCrossing
  have hclosure : Relation.ReflTransGen (rotationPrimalGraph RS).Adj
      (RS.vertOf left) (RS.vertOf right) :=
    (SimpleGraph.reachable_iff_reflTransGen _ _).mp hprimal
  have hfaceRelation : FaceReachableAt (RS.vertOf left) (RS.vertOf right) := by
    refine Relation.ReflTransGen.trans_induction_on
      (motive := fun {leftVertex rightVertex} _ =>
        FaceReachableAt leftVertex rightVertex)
      hclosure hrefl (fun h => hadj h) ?_
    intro leftVertex middleVertex rightVertex _ _ hleft hright
      leftDart rightDart hleftDart hrightDart
    obtain ⟨middleDart, hmiddleDart⟩ :=
      exists_dart_vertOf_eq_of_isCubic RS hcubic middleVertex
    exact (hleft leftDart middleDart hleftDart hmiddleDart).trans
      (hright middleDart rightDart hmiddleDart hrightDart)
  exact hfaceRelation left right rfl rfl

/-- Connectedness of the computed primal graph and genuine cyclic vertex
rotations imply connectedness of the full quotient facial dual. -/
theorem orbitFaceInteriorDual_connected
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hprimal : (rotationPrimalGraph RS).Connected)
    (hrotation : VertexRotationCyclic RS) :
    (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Connected := by
  letI : Nonempty (AmbientFace (Finset.univ : Finset (OrbitFace RS))) :=
    ⟨orbitFaceVertex RS RS.outer⟩
  constructor
  intro leftFace rightFace
  obtain ⟨leftDart, hleftDart⟩ :=
    exists_dartOrbitFace_eq RS leftFace.1
  obtain ⟨rightDart, hrightDart⟩ :=
    exists_dartOrbitFace_eq RS rightFace.1
  have hreach := orbitFaceVertex_reachable_of_primalReachable
    RS hcubic hrotation
      (hprimal (RS.vertOf leftDart) (RS.vertOf rightDart))
  have hleftVertex : orbitFaceVertex RS leftDart = leftFace :=
    Subtype.ext hleftDart
  have hrightVertex : orbitFaceVertex RS rightDart = rightFace :=
    Subtype.ext hrightDart
  rwa [hleftVertex, hrightVertex] at hreach

end GoertzelV24FaceDualConnectedness

end Mettapedia.GraphTheory.FourColor
