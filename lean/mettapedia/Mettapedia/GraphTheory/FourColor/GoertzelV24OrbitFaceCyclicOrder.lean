import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitIncidence

/-!
# Cyclic indexing of a rotation-system face orbit

Face incidence is naturally stored as an unordered finite orbit.  Boundary
arcs require the cyclic order retained by the face permutation.  This module
recovers that order compactly: starting at any dart, the first `|face|`
iterates of `phi` are an equivalence from `Fin |face|` to the complete face
orbit.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrbitFaceCyclicOrder

open GoertzelV24FaceOrbitIncidence

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The face permutation acts as one cycle on the orbit of any chosen root
dart. -/
theorem phi_isCycleOn_faceOrbit (RS : RotationSystem V E) (root : RS.D) :
    RS.phi.IsCycleOn (RS.faceOrbit root : Set RS.D) := by
  refine ⟨?_, ?_⟩
  · exact RS.phi.bijOn fun dart => by
      change RS.phi dart ∈ RS.faceOrbit root ↔ dart ∈ RS.faceOrbit root
      exact RS.phi_mem_faceOrbit_iff
  · intro first hfirst second hsecond
    have hfirst' : first ∈ RS.faceOrbit root := hfirst
    have hsecond' : second ∈ RS.faceOrbit root := hsecond
    exact ((RS.mem_faceOrbit).1 hfirst').symm.trans
      ((RS.mem_faceOrbit).1 hsecond')

/-- The dart at one cyclic position after the chosen face root. -/
def faceOrbitDartAt (RS : RotationSystem V E) (root : RS.D)
    (position : Fin (RS.faceOrbit root).card) : RS.D :=
  (RS.phi ^ position.val) root

/-- Every cyclically indexed dart remains in the chosen face orbit. -/
theorem faceOrbitDartAt_mem (RS : RotationSystem V E) (root : RS.D)
    (position : Fin (RS.faceOrbit root).card) :
    faceOrbitDartAt RS root position ∈ RS.faceOrbit root := by
  have hcycle := phi_isCycleOn_faceOrbit RS root
  exact hcycle.1.mapsTo.perm_pow position.val (RS.mem_faceOrbit_self root)

/-- The indexed dart, packaged as an element of the chosen face orbit. -/
def faceOrbitDartAtFace (RS : RotationSystem V E) (root : RS.D)
    (position : Fin (RS.faceOrbit root).card) :
    {dart : RS.D // dart ∈ RS.faceOrbit root} :=
  ⟨faceOrbitDartAt RS root position, faceOrbitDartAt_mem RS root position⟩

/-- No two positions before the face length name the same dart. -/
theorem faceOrbitDartAt_injective (RS : RotationSystem V E) (root : RS.D) :
    Function.Injective (faceOrbitDartAt RS root) := by
  intro first second heq
  have hcycle := phi_isCycleOn_faceOrbit RS root
  have hmod := (hcycle.pow_apply_eq_pow_apply
    (RS.mem_faceOrbit_self root)).1 heq
  apply Fin.ext
  change first.val % (RS.faceOrbit root).card =
    second.val % (RS.faceOrbit root).card at hmod
  rw [Nat.mod_eq_of_lt first.isLt, Nat.mod_eq_of_lt second.isLt] at hmod
  exact hmod

/-- Every dart in the chosen face orbit has a cyclic position before the
face length. -/
theorem faceOrbitDartAt_surjective (RS : RotationSystem V E) (root : RS.D) :
    Function.Surjective (faceOrbitDartAtFace RS root) := by
  intro dart
  have hcycle := phi_isCycleOn_faceOrbit RS root
  rcases hcycle.exists_pow_eq (RS.mem_faceOrbit_self root) dart.2 with
    ⟨power, hpower, heq⟩
  refine ⟨⟨power, hpower⟩, ?_⟩
  apply Subtype.ext
  exact heq

/-- Cyclic face positions are equivalent to the complete orbit subtype. -/
def faceOrbitDartEquiv (RS : RotationSystem V E) (root : RS.D) :
    Fin (RS.faceOrbit root).card ≃ {dart // dart ∈ RS.faceOrbit root} :=
  Equiv.ofBijective
    (faceOrbitDartAtFace RS root)
    ⟨fun _ _ heq => faceOrbitDartAt_injective RS root
        (congrArg Subtype.val heq),
      faceOrbitDartAt_surjective RS root⟩

@[simp] theorem faceOrbitDartEquiv_apply_val
    (RS : RotationSystem V E) (root : RS.D)
    (position : Fin (RS.faceOrbit root).card) :
    (faceOrbitDartEquiv RS root position).1 =
      (RS.phi ^ position.val) root :=
  rfl

end

end GoertzelV24OrbitFaceCyclicOrder

end Mettapedia.GraphTheory.FourColor
