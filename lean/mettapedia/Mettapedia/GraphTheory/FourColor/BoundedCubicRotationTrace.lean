import Mettapedia.GraphTheory.FourColor.BoundedCubicTraceTopology
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitCountCongr
import Mathlib.Data.Fintype.Perm

/-!
# Finite traces of the supplied cubic rotation and its spherical Euler count

The incidence code is augmented by its edge-flip and vertex-rotation
permutations on the three positions at each vertex. All validation tests and
the full facial-cycle count are executable. The encoding transports the
actual supplied rotation, rather than searching for a preferred embedding.
No finite-base audit or global reduction theorem is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundedCubicColourTrace

open GoertzelV24FaceDualConnectedness GoertzelV24RotationEdgeBridge
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24TwoEdgeCutMinimality
open GoertzelV24OrbitCountCongr GoertzelV24PermutationOrbitSurgery

abbrev Position (n : Nat) := Fin n × Fin 3

abbrev RotationCode (n m : Nat) :=
  Code n m × Equiv.Perm (Position n) × Equiv.Perm (Position n)

namespace RotationCode

def incidence {n m : Nat} (code : RotationCode n m) : Code n m := code.1
def alpha {n m : Nat} (code : RotationCode n m) : Equiv.Perm (Position n) := code.2.1
def rho {n m : Nat} (code : RotationCode n m) : Equiv.Perm (Position n) := code.2.2
def edge {n m : Nat} (code : RotationCode n m) (d : Position n) : Fin m :=
  code.incidence d.1 d.2

/-- Local incidence compatibility, including one cyclic order per vertex. -/
def Valid {n m : Nat} (code : RotationCode n m) : Prop :=
  BoundedCubicColourTrace.Valid code.incidence ∧
  (∀ d, code.alpha (code.alpha d) = d) ∧
  (∀ d, code.alpha d ≠ d) ∧
  (∀ d, code.edge (code.alpha d) = code.edge d) ∧
  (∀ d, d.1 ≠ (code.alpha d).1) ∧
  (∀ d, (code.rho d).1 = d.1) ∧
  (∀ d e, d.1 = e.1 → code.rho.SameCycle d e)

instance {n m : Nat} (code : RotationCode n m) : Decidable code.Valid := by
  unfold Valid
  infer_instance

/-- All facial cycles, including singleton cycles. -/
def faceCount {n m : Nat} (code : RotationCode n m) : Nat :=
  (code.rho * code.alpha).partition.parts.card

def euler {n m : Nat} (code : RotationCode n m) : Int :=
  (n : Int) - m + code.faceCount

def admissible {n m : Nat} (code : RotationCode n m) : Bool :=
  decide code.Valid && connected code.incidence && bridgeFree code.incidence &&
    decide (code.euler = 2)

end RotationCode

section Encoding

universe u v
variable {V : Type u} {E : Type v} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E) (hc : RS.IsCubic)

/-- Locate a source dart at its vertex and incident-edge position. -/
noncomputable def dartPosition (d : RS.D) : Position (Fintype.card V) :=
  ⟨Fintype.equivFin V (RS.vertOf d),
    (starEquiv RS hc (RS.vertOf d)).symm
      ⟨RS.edgeOf d, RS.mem_incidentEdges_iff.2 ⟨d, rfl, rfl⟩⟩⟩

@[simp] theorem dartPosition_fst (d : RS.D) :
    (dartPosition RS hc d).1 = Fintype.equivFin V (RS.vertOf d) := rfl

theorem dartPosition_edge (d : RS.D) :
    encode RS hc (dartPosition RS hc d).1 (dartPosition RS hc d).2 =
      Fintype.equivFin E (RS.edgeOf d) := by
  change encode RS hc (Fintype.equivFin V (RS.vertOf d))
    ((starEquiv RS hc (RS.vertOf d)).symm _) = _
  rw [encode_vertex]
  apply congrArg (Fintype.equivFin E)
  exact congrArg Subtype.val ((starEquiv RS hc (RS.vertOf d)).apply_symm_apply _)

theorem dartPosition_injective : Function.Injective (dartPosition RS hc) := by
  intro d e h
  have hv : RS.vertOf d = RS.vertOf e :=
    (Fintype.equivFin V).injective (congrArg Prod.fst h)
  have he := congrArg (fun p => encode RS hc p.1 p.2) h
  rw [dartPosition_edge, dartPosition_edge] at he
  exact RS.edgeOf_injOn_dartsAt (RS.vertOf d)
    (by simp [RotationSystem.dartsAt]) (by simp [RotationSystem.dartsAt, hv])
    ((Fintype.equivFin E).injective he)

theorem dartPosition_surjective : Function.Surjective (dartPosition RS hc) := by
  rintro ⟨v, i⟩
  obtain ⟨d, hd, hv⟩ := RS.mem_incidentEdges_iff.1
    (starEdge_mem RS hc ((Fintype.equivFin V).symm v) i)
  have hfst : (dartPosition RS hc d).1 = v := by simp [hv]
  refine ⟨d, Prod.ext hfst ?_⟩
  apply encode_injective RS hc v
  have hedge := dartPosition_edge RS hc d
  rw [hfst] at hedge
  simpa [encode, hd, hv] using hedge

noncomputable def dartPositionEquiv : RS.D ≃ Position (Fintype.card V) :=
  Equiv.ofBijective (dartPosition RS hc)
    ⟨dartPosition_injective RS hc, dartPosition_surjective RS hc⟩

@[simp] theorem dartPositionEquiv_apply (d : RS.D) :
    dartPositionEquiv RS hc d = dartPosition RS hc d := rfl

noncomputable def encodeRotation : RotationCode (Fintype.card V) (Fintype.card E) :=
  let e := dartPositionEquiv RS hc
  ⟨encode RS hc, (e.symm.trans RS.alpha).trans e, (e.symm.trans RS.rho).trans e⟩

@[simp] theorem encodeRotation_incidence :
    (encodeRotation RS hc).incidence = encode RS hc := rfl

@[simp] theorem encodeRotation_alpha (d : RS.D) :
    (encodeRotation RS hc).alpha (dartPositionEquiv RS hc d) =
      dartPositionEquiv RS hc (RS.alpha d) := by
  change dartPositionEquiv RS hc (RS.alpha ((dartPositionEquiv RS hc).symm
    (dartPositionEquiv RS hc d))) = _
  simp only [Equiv.symm_apply_apply]

@[simp] theorem encodeRotation_rho (d : RS.D) :
    (encodeRotation RS hc).rho (dartPositionEquiv RS hc d) =
      dartPositionEquiv RS hc (RS.rho d) := by
  change dartPositionEquiv RS hc (RS.rho ((dartPositionEquiv RS hc).symm
    (dartPositionEquiv RS hc d))) = _
  simp only [Equiv.symm_apply_apply]

@[simp] theorem encodeRotation_edge (d : RS.D) :
    (encodeRotation RS hc).edge (dartPositionEquiv RS hc d) =
      Fintype.equivFin E (RS.edgeOf d) := dartPosition_edge RS hc d

theorem encodeRotation_valid (hcyclic : VertexRotationCyclic RS) :
    (encodeRotation RS hc).Valid := by
  refine ⟨encode_valid RS hc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    obtain ⟨d, rfl⟩ := (dartPositionEquiv RS hc).surjective p
    rw [encodeRotation_alpha, encodeRotation_alpha, RS.alpha_involutive]
  · intro p
    obtain ⟨d, rfl⟩ := (dartPositionEquiv RS hc).surjective p
    rw [encodeRotation_alpha]
    exact fun h => RS.alpha_fixfree d ((dartPositionEquiv RS hc).injective h)
  · intro p
    obtain ⟨d, rfl⟩ := (dartPositionEquiv RS hc).surjective p
    rw [encodeRotation_alpha, encodeRotation_edge, encodeRotation_edge, RS.edge_alpha]
  · intro p
    obtain ⟨d, rfl⟩ := (dartPositionEquiv RS hc).surjective p
    rw [encodeRotation_alpha]
    exact fun h => RS.no_self_loops d ((Fintype.equivFin V).injective h)
  · intro p
    obtain ⟨d, rfl⟩ := (dartPositionEquiv RS hc).surjective p
    rw [encodeRotation_rho]
    exact congrArg (Fintype.equivFin V) (RS.vert_rho d)
  · intro p q hpq
    obtain ⟨d, rfl⟩ := (dartPositionEquiv RS hc).surjective p
    obtain ⟨e, rfl⟩ := (dartPositionEquiv RS hc).surjective q
    apply (sameCycle_conjEquiv_iff (dartPositionEquiv RS hc) RS.rho d e).2
    exact hcyclic d e ((Fintype.equivFin V).injective hpq)

theorem encodeRotation_phi :
    (encodeRotation RS hc).rho * (encodeRotation RS hc).alpha =
      ((dartPositionEquiv RS hc).symm.trans RS.phi).trans (dartPositionEquiv RS hc) := by
  ext p : 1
  obtain ⟨d, rfl⟩ := (dartPositionEquiv RS hc).surjective p
  simp only [Equiv.Perm.mul_apply, encodeRotation_alpha, encodeRotation_rho]
  change _ = dartPositionEquiv RS hc (RS.phi ((dartPositionEquiv RS hc).symm
    (dartPositionEquiv RS hc d)))
  simp only [Equiv.symm_apply_apply]
  rfl

theorem encodeRotation_faceCount :
    (encodeRotation RS hc).faceCount = Fintype.card (OrbitFace RS) := by
  unfold RotationCode.faceCount
  rw [encodeRotation_phi, ← card_permOrbit_eq_card_partition_parts]
  exact orbitCount_conjEquiv (dartPositionEquiv RS hc) RS.phi

theorem encodeRotation_euler :
    (encodeRotation RS hc).euler =
      (Fintype.card V : Int) - Fintype.card E + Fintype.card (OrbitFace RS) := by
  unfold RotationCode.euler
  rw [encodeRotation_faceCount]

theorem encodeRotation_admissible (h : BridgelessSphericalCubicMapData RS) :
    (encodeRotation RS hc).admissible = true := by
  simp only [RotationCode.admissible, Bool.and_eq_true, decide_eq_true_eq,
    encodeRotation_incidence, connected_encode_iff, bridgeFree_encode_iff,
    encodeRotation_euler]
  exact ⟨⟨⟨encodeRotation_valid RS hc h.vertexRotationCyclic,
    h.primalConnected⟩, h.edgeBridgeFree⟩, h.spherical.euler⟩

/-- On an actual cubic rotation map, the Boolean check reflects the full
structural target class, not just its Euler equation. -/
theorem encodeRotation_admissible_iff :
    (encodeRotation RS hc).admissible = true ↔
      Nonempty (BridgelessSphericalCubicMapData RS) := by
  constructor
  · intro h
    simp only [RotationCode.admissible, Bool.and_eq_true, decide_eq_true_eq,
      encodeRotation_incidence, connected_encode_iff, bridgeFree_encode_iff,
      encodeRotation_euler] at h
    refine ⟨⟨⟨hc, h.2⟩, h.1.1.2, ?_, h.1.2⟩⟩
    intro d e hde
    have hv := h.1.1.1.2.2.2.2.2.2
      (dartPositionEquiv RS hc d) (dartPositionEquiv RS hc e)
      (congrArg (Fintype.equivFin V) hde)
    exact (sameCycle_conjEquiv_iff (dartPositionEquiv RS hc) RS.rho d e).1 hv
  · rintro ⟨h⟩
    exact encodeRotation_admissible RS hc h

end Encoding

abbrev BoundedRotationCode (bound : Nat) :=
  Σ n : Fin (bound + 1), Σ m : Fin (3 * bound / 2 + 1), RotationCode n.val m.val

/-- Size of the deliberately uncompressed raw code space, before validation. -/
theorem card_rotationCode (n m : Nat) :
    Fintype.card (RotationCode n m) =
      m ^ (3 * n) * (Nat.factorial (3 * n)) ^ 2 := by
  simp only [RotationCode, Code, Position, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_perm, ← pow_mul, Nat.mul_comm n 3, pow_two]

theorem card_boundedRotationCode (bound : Nat) :
    Fintype.card (BoundedRotationCode bound) =
      ∑ n : Fin (bound + 1), ∑ m : Fin (3 * bound / 2 + 1),
        (m : Nat) ^ (3 * (n : Nat)) * (Nat.factorial (3 * (n : Nat))) ^ 2 := by
  simp only [BoundedRotationCode, Fintype.card_sigma, card_rotationCode]

theorem raw_code_count_two : Fintype.card (BoundedRotationCode 2) = 411610900 := by
  rw [card_boundedRotationCode]
  decide +kernel

def sphericalEnvelope (bound : Nat) : Finset (BoundedRotationCode bound) :=
  Finset.univ.filter fun code => code.2.2.admissible = true

noncomputable def rotationTrace
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (hc : RS.IsCubic)
    {bound : Nat} (hb : Fintype.card V ≤ bound) : BoundedRotationCode bound :=
  ⟨⟨Fintype.card V, by omega⟩,
    ⟨Fintype.card E, by have := edge_count_le_of_vertex_bound RS hc hb; omega⟩,
    encodeRotation RS hc⟩

theorem rotationTrace_mem_sphericalEnvelope
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (h : BridgelessSphericalCubicMapData RS)
    {bound : Nat} (hb : Fintype.card V ≤ bound) :
    rotationTrace RS h.spherical.cubic hb ∈ sphericalEnvelope bound := by
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
    encodeRotation_admissible RS h.spherical.cubic h⟩

theorem rotationTrace_bad_iff
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (hc : RS.IsCubic)
    {bound : Nat} (hb : Fintype.card V ≤ bound) :
    hasColouring (rotationTrace RS hc hb).2.2.incidence = false ↔
      ¬ RotationSystemTaitColorable RS := trace_bad_iff RS hc hb

namespace Controls

def parallelAlpha : Equiv.Perm (Position 2) :=
  Equiv.prodCongr (Equiv.swap 0 1) (Equiv.refl _)

def parallelForward : Equiv.Perm (Position 2) where
  toFun d := (d.1, d.2 + 1)
  invFun d := (d.1, d.2 - 1)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def parallelOpposite : Equiv.Perm (Position 2) where
  toFun d := (d.1, if d.1 = 0 then d.2 + 1 else d.2 - 1)
  invFun d := (d.1, if d.1 = 0 then d.2 - 1 else d.2 + 1)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def parallelSphere : RotationCode 2 3 :=
  ⟨parallelTriple, parallelAlpha, parallelOpposite⟩

def parallelTorus : RotationCode 2 3 :=
  ⟨parallelTriple, parallelAlpha, parallelForward⟩

theorem parallelSphere_faces : parallelSphere.faceCount = 3 := by decide +kernel
theorem parallelTorus_faces : parallelTorus.faceCount = 1 := by decide +kernel
theorem parallelSphere_admissible : parallelSphere.admissible = true := by decide +kernel
theorem parallelTorus_valid : parallelTorus.Valid := by decide +kernel
theorem parallelTorus_not_admissible : parallelTorus.admissible = false := by decide +kernel

theorem singleton_cycles_counted :
    (1 : Equiv.Perm (Fin 3)).partition.parts.card = 3 := by decide +kernel

end Controls

end Mettapedia.GraphTheory.FourColor.BoundedCubicColourTrace
