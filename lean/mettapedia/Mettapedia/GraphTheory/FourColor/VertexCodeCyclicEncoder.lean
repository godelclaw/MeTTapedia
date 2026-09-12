import Mettapedia.GraphTheory.FourColor.VertexCodePartition
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness

/-!
# A source-facing cyclic encoder

The interpreter reads a code's three slots as a cyclic order: the realized
star satisfies `rho (slot i) = slot (i+1)`. An encoder that merely enumerates
the three incident darts therefore need not describe the source rotation,
and the discrepancy is invisible to the colour test, which only asks that the
three darts carry distinct nonzero colours. It is *not* invisible to the Euler
mass: the two cyclic orders of one incidence pattern give masses four and zero
on the same cut data.

This file supplies the missing enumeration. At a cubic vertex whose stored
rotation is genuinely one cyclic order, the three darts are `d`, `rho d`,
`rho (rho d)`, and `rho` returns. Encoding through that enumeration produces
a code whose consecutive slots are consecutive darts of the source rotation,
which is the property the interpreter consumes.

Encoding is factored through an arbitrary supplied enumeration, so the
existing encoder is the special case `encodeWith (starEquiv ..)` and nothing
proved about it is lost.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexCodeCyclicEncoder

open TubeSlab.VertexTransfer GoertzelV24FaceDualConnectedness
open GoertzelV24RotationCutDartDecomposition TubeSlab.NestedSideWire

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem.{u, u, u} V E} {inner : V → Prop} {v : V}

noncomputable section

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-! ## The rotation restricted to one vertex -/

/-- The darts based at `v`. -/
abbrev At (RS : RotationSystem.{u, u, u} V E) (v : V) := {d : RS.D // RS.vertOf d = v}

/-- The stored rotation restricted to one dart fiber. -/
def rot (d : At RS v) : At RS v := ⟨RS.rho d.1, (RS.vert_rho d.1).trans d.2⟩

theorem rot_injective : Function.Injective (rot (RS := RS) (v := v)) := fun _ _ h =>
  Subtype.ext (RS.rho.injective (congrArg Subtype.val h))

theorem card_at (hc : RS.IsCubic) : Fintype.card (At RS v) = 3 := by
  simpa only [Fintype.card_subtype, RotationSystem.dartsAt] using hc v

/-- With one cyclic order per fiber, no dart is fixed: a fixed dart is its own
whole cycle, so the fiber could not also contain a second dart. -/
theorem rot_ne (hc : RS.IsCubic) (hcyc : VertexRotationCyclic RS) (d : At RS v) :
    rot d ≠ d := by
  intro hfix
  have hself : RS.rho d.1 = d.1 := congrArg Subtype.val hfix
  obtain ⟨e, hne⟩ : ∃ e : At RS v, e ≠ d :=
    Fintype.exists_ne_of_one_lt_card (by rw [card_at hc]; omega) d
  obtain ⟨k, hk⟩ := hcyc d.1 e.1 (d.2.trans e.2.symm)
  exact hne (Subtype.ext
    ((Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hself k).symm.trans hk).symm)

/-- A fixed-point-free injection of a three-element type has order three.
Checked by exhausting the twenty-seven endomorphisms of `Fin 3`. -/
theorem fin3_fixfree : ∀ f : Fin 3 → Fin 3, (∀ a b, f a = f b → a = b) →
    (∀ x, f x ≠ x) → ∀ x, f (f (f x)) = x := by decide +kernel

theorem rot_three (hc : RS.IsCubic) (hcyc : VertexRotationCyclic RS) (d : At RS v) :
    rot (rot (rot d)) = d := by
  classical
  let e : At RS v ≃ Fin 3 := Fintype.equivFinOfCardEq (card_at hc)
  have hg : ∀ a b : Fin 3, e (rot (e.symm a)) = e (rot (e.symm b)) → a = b := by
    intro a b h
    simpa using congrArg e (rot_injective (e.injective h))
  have hfix : ∀ a : Fin 3, e (rot (e.symm a)) ≠ a := by
    intro a h
    exact rot_ne hc hcyc (e.symm a) (e.injective (by simpa using h))
  have h3 := fin3_fixfree (fun a => e (rot (e.symm a))) hg hfix (e d)
  simp only [Equiv.symm_apply_apply] at h3
  exact e.injective h3

theorem rot_ne_two (hc : RS.IsCubic) (hcyc : VertexRotationCyclic RS) (d : At RS v) :
    rot (rot d) ≠ d := by
  intro h
  have h3 := rot_three hc hcyc d
  rw [h] at h3
  exact rot_ne hc hcyc d h3

/-! ## The cyclic enumeration -/

/-- `NewDart` is exactly a dart based at the new vertex. -/
def newDartEquiv (hv : ¬ inner v) : NewDart RS inner v ≃ At RS v where
  toFun d := ⟨d.1, newDart_base d⟩
  invFun d := ⟨d.1, ⟨Or.inr d.2, fun h => hv (d.2 ▸ h)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem newDartEquiv_symm_coe (hv : ¬ inner v) (d : At RS v) :
    ((newDartEquiv (RS := RS) (inner := inner) hv).symm d).1 = d.1 := rfl

def cyc (d₀ : At RS v) (i : Fin 3) : At RS v := rot^[i.val] d₀

theorem cyc_injective (hc : RS.IsCubic) (hcyc : VertexRotationCyclic RS) (d₀ : At RS v) :
    Function.Injective (cyc d₀) := by
  have h1 : rot d₀ ≠ d₀ := rot_ne hc hcyc d₀
  have h2 : rot (rot d₀) ≠ d₀ := rot_ne_two hc hcyc d₀
  have h3 : rot (rot d₀) ≠ rot d₀ := fun h => h1 (rot_injective h)
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp only [cyc] at hab <;>
    first
      | rfl
      | exact absurd hab (by simpa using h1)
      | exact absurd hab (by simpa using h2)
      | exact absurd hab (by simpa using h3)
      | exact absurd hab.symm (by simpa using h1)
      | exact absurd hab.symm (by simpa using h2)
      | exact absurd hab.symm (by simpa using h3)

/-- The code's three slots, in the source's own cyclic order. -/
def cyclicStarEquiv (hc : RS.IsCubic) (hv : ¬ inner v) (hcyc : VertexRotationCyclic RS)
    (d₀ : At RS v) : Fin 3 ≃ NewDart RS inner v :=
  Equiv.ofBijective (fun i => (newDartEquiv hv).symm (cyc d₀ i))
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨(newDartEquiv hv).symm.injective.comp (cyc_injective hc hcyc d₀), by
        simp [Fintype.card_congr (newDartEquiv (RS := RS) (inner := inner) hv), card_at hc]⟩)

theorem cyclicStarEquiv_coe (hc : RS.IsCubic) (hv : ¬ inner v)
    (hcyc : VertexRotationCyclic RS) (d₀ : At RS v) (i : Fin 3) :
    ((cyclicStarEquiv hc hv hcyc d₀) i).1 = (cyc d₀ i).1 := rfl

/-- **The required property.** Consecutive slots are consecutive darts of the
source rotation, so the realized star carries the source's cyclic order. -/
theorem cyclicStarEquiv_succ (hc : RS.IsCubic) (hv : ¬ inner v)
    (hcyc : VertexRotationCyclic RS) (d₀ : At RS v) (i : Fin 3) :
    RS.rho ((cyclicStarEquiv hc hv hcyc d₀) i).1 =
      ((cyclicStarEquiv hc hv hcyc d₀) (i + 1)).1 := by
  have h3 := rot_three hc hcyc d₀
  fin_cases i <;>
    simp only [cyclicStarEquiv_coe, cyc, Function.iterate_zero_apply,
      Function.iterate_one] <;>
    first
      | rfl
      | exact congrArg Subtype.val h3

/-! ## Encoding through a supplied enumeration -/

variable {l r : ℕ}

/-- The existing encoder with its star enumeration exposed as a parameter. -/
def encodeWith (se : Fin 3 ≃ NewDart RS inner v)
    (mi : Fin l ≃ BoundaryDart RS inner)
    (mo : Fin r ≃ BoundaryDart RS (enlarged inner v)) : Code l r :=
  (fun i => Sum.map mi.symm mo.symm (port (se i)),
   fun j => if hi : inner (RS.vertOf (mo j).1.1)
     then some (mi.symm (throughFromOuter inclusion (mo j) hi)) else none)

/-- Nothing already proved is lost: the old encoder is one instance. -/
theorem encodeWith_starEquiv (hc : RS.IsCubic) (hv : ¬ inner v)
    (mi : Fin l ≃ BoundaryDart RS inner)
    (mo : Fin r ≃ BoundaryDart RS (enlarged inner v)) :
    encodeWith (starEquiv hc hv) mi mo = encode hc hv mi mo := rfl

theorem encodeWith_star_injective (se : Fin 3 ≃ NewDart RS inner v)
    (mi : Fin l ≃ BoundaryDart RS inner)
    (mo : Fin r ≃ BoundaryDart RS (enlarged inner v)) :
    Function.Injective (encodeWith se mi mo).1 := fun _ _ h =>
  se.injective (port_injective ((Equiv.sumCongr mi.symm mo.symm).injective h))

theorem encodeWith_wire_injective (se : Fin 3 ≃ NewDart RS inner v)
    (mi : Fin l ≃ BoundaryDart RS inner)
    (mo : Fin r ≃ BoundaryDart RS (enlarged inner v)) (j k : Fin r) (i : Fin l)
    (hj : (encodeWith se mi mo).2 j = some i)
    (hk : (encodeWith se mi mo).2 k = some i) : j = k := by
  simp only [encodeWith] at hj hk
  split_ifs at hj with hjin
  split_ifs at hk with hkin
  have he := mi.symm.injective ((Option.some.inj hj).trans (Option.some.inj hk).symm)
  exact mo.injective (Subtype.ext (Subtype.ext
    (congrArg (fun b : BoundaryDart RS inner => b.1.1) he)))

theorem encodeWith_forced (se : Fin 3 ≃ NewDart RS inner v)
    (mi : Fin l ≃ BoundaryDart RS inner)
    (mo : Fin r ≃ BoundaryDart RS (enlarged inner v))
    (x : Fin l → Color) (y : Fin r → Color) (t : Fin 3) :
    Sum.elim x y ((encodeWith se mi mo).1 t) =
      forced (fun b => x (mi.symm b)) (fun b => y (mo.symm b)) (se t) := by
  rw [forced_eq]
  change Sum.elim x y (Sum.map mi.symm mo.symm _) = _
  cases port (se t) <;> rfl

/-- The finite colour test is unchanged by the choice of enumeration: this is
exactly why a wrong rotation is invisible to colour data. -/
theorem encodeWith_codeAccepts_iff (se : Fin 3 ≃ NewDart RS inner v)
    (mi : Fin l ≃ BoundaryDart RS inner)
    (mo : Fin r ≃ BoundaryDart RS (enlarged inner v))
    (x : Fin l → Color) (y : Fin r → Color) :
    CodeAccepts (encodeWith se mi mo) x y ↔
      Accepts (fun b => x (mi.symm b)) (fun b => y (mo.symm b)) := by
  constructor
  · rintro ⟨hx, hy, hs, hw⟩
    refine ⟨fun b => hx _, fun b => hy _, ?_, ?_⟩
    · intro d e heq
      have h := hs (a₁ := se.symm d) (a₂ := se.symm e)
      simp only [encodeWith_forced, Equiv.apply_symm_apply] at h
      exact se.symm.injective (h heq)
    · intro b hi
      have h := hw (mo.symm b) (mi.symm (throughFromOuter inclusion b hi))
      simp only [encodeWith, Equiv.apply_symm_apply, dif_pos hi, forall_const] at h
      exact h
  · rintro ⟨hx, hy, hs, hw⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      simpa only [Equiv.symm_apply_apply] using hx (mi i)
    · intro j
      simpa only [Equiv.symm_apply_apply] using hy (mo j)
    · intro s t heq
      change Sum.elim x y ((encodeWith se mi mo).1 s) =
        Sum.elim x y ((encodeWith se mi mo).1 t) at heq
      rw [encodeWith_forced, encodeWith_forced] at heq
      exact se.injective (hs heq)
    · intro j i heq
      change (if hi : inner (RS.vertOf (mo j).1.1) then
        some (mi.symm (throughFromOuter inclusion (mo j) hi)) else none) = some i at heq
      split_ifs at heq with hi
      · cases Option.some.inj heq
        simpa only [Equiv.symm_apply_apply] using hw (mo j) hi

theorem encodeWith_count (se : Fin 3 ≃ NewDart RS inner v)
    (mi : Fin l ≃ BoundaryDart RS inner)
    (mo : Fin r ≃ BoundaryDart RS (enlarged inner v))
    (x : Fin l → Color) (y : Fin r → Color) :
    slabCount inclusion (fun b => x (mi.symm b)) (fun b => y (mo.symm b)) =
      if CodeAccepts (encodeWith se mi mo) x y then 1 else 0 := by
  rw [slabCount_eq, encodeWith_codeAccepts_iff]

/-! ## The source-facing encoder -/

/-- The encoder whose slots follow the source rotation. -/
def cyclicEncode (hc : RS.IsCubic) (hv : ¬ inner v) (hcyc : VertexRotationCyclic RS)
    (d₀ : At RS v) (mi : Fin l ≃ BoundaryDart RS inner)
    (mo : Fin r ≃ BoundaryDart RS (enlarged inner v)) : Code l r :=
  encodeWith (cyclicStarEquiv hc hv hcyc d₀) mi mo

theorem cyclicEncode_slot (hc : RS.IsCubic) (hv : ¬ inner v)
    (hcyc : VertexRotationCyclic RS) (d₀ : At RS v)
    (mi : Fin l ≃ BoundaryDart RS inner)
    (mo : Fin r ≃ BoundaryDart RS (enlarged inner v)) (i : Fin 3) :
    (cyclicEncode hc hv hcyc d₀ mi mo).1 i =
      Sum.map mi.symm mo.symm (port ((cyclicStarEquiv hc hv hcyc d₀) i)) := rfl

/-- Slot `i+1` of the emitted code is the port of the source dart `rho (slot i)`.
The interpreter's cyclic reading of the slots is therefore the source rotation
and not an arbitrary relabelling of the three incident darts. -/
theorem cyclicEncode_rotation (hc : RS.IsCubic) (hv : ¬ inner v)
    (hcyc : VertexRotationCyclic RS) (d₀ : At RS v)
    (mi : Fin l ≃ BoundaryDart RS inner)
    (mo : Fin r ≃ BoundaryDart RS (enlarged inner v)) (i : Fin 3) :
    ∃ d : NewDart RS inner v,
      d.1 = RS.rho ((cyclicStarEquiv hc hv hcyc d₀) i).1 ∧
        (cyclicEncode hc hv hcyc d₀ mi mo).1 (i + 1) =
          Sum.map mi.symm mo.symm (port d) :=
  ⟨(cyclicStarEquiv hc hv hcyc d₀) (i + 1),
    (cyclicStarEquiv_succ hc hv hcyc d₀ i).symm, rfl⟩

theorem cyclicEncode_codeAccepts_iff (hc : RS.IsCubic) (hv : ¬ inner v)
    (hcyc : VertexRotationCyclic RS) (d₀ : At RS v)
    (mi : Fin l ≃ BoundaryDart RS inner)
    (mo : Fin r ≃ BoundaryDart RS (enlarged inner v))
    (x : Fin l → Color) (y : Fin r → Color) :
    CodeAccepts (cyclicEncode hc hv hcyc d₀ mi mo) x y ↔
      Accepts (fun b => x (mi.symm b)) (fun b => y (mo.symm b)) :=
  encodeWith_codeAccepts_iff _ mi mo x y

/-! ## The emitted code lies in the interpreter's domain

Each clause of incidence validity is an actual dichotomy about the ambient
darts: a new boundary port is fresh exactly when it is based at the new
vertex, and an old boundary port is consumed exactly when its mate is.
-/

variable (se : Fin 3 ≃ NewDart RS inner v)
  (mi : Fin l ≃ BoundaryDart RS inner)
  (mo : Fin r ≃ BoundaryDart RS (enlarged inner v))

theorem encodeWith_none_iff (j : Fin r) :
    (encodeWith se mi mo).2 j = none ↔ ¬ inner (RS.vertOf (mo j).1.1) := by
  simp only [encodeWith]
  split_ifs with hi
  · exact ⟨fun h => absurd h (by simp), fun h => absurd hi h⟩
  · exact ⟨fun _ => hi, fun _ => rfl⟩

/-- A slot emits a new port exactly when that port is based at the new vertex. -/
theorem encodeWith_inr_iff (j : Fin r) :
    (∃ t, (encodeWith se mi mo).1 t = Sum.inr j) ↔ ¬ inner (RS.vertOf (mo j).1.1) := by
  constructor
  · rintro ⟨t, ht⟩
    change Sum.map mi.symm mo.symm (port (se t)) = Sum.inr j at ht
    unfold port at ht
    split_ifs at ht with hio
    · exact absurd ht (by simp)
    · have hj : mo j = outgoing (se t) hio := by
        rw [← Sum.inr.inj ht]; exact mo.apply_symm_apply _
      rw [hj]
      exact (se t).2.2
  · intro hni
    have hout : ¬ inner (RS.vertOf (RS.alpha (mo j).1.1)) := fun h => (mo j).2 (Or.inl h)
    refine ⟨se.symm ⟨(mo j).1.1, ⟨(mo j).1.2, hni⟩⟩, ?_⟩
    change Sum.map mi.symm mo.symm (port (se (se.symm _))) = Sum.inr j
    rw [se.apply_symm_apply]
    unfold port
    rw [dif_neg hout]
    exact congrArg Sum.inr (by rw [show outgoing _ hout = mo j from rfl, mo.symm_apply_apply])

/-- A slot consumes an old port exactly when that port's mate is at the new
vertex; otherwise the port persists as a wire. The two cases are exclusive
and exhaustive, which is the content of the remaining validity clause. -/
theorem encodeWith_inl_iff (hv : ¬ inner v) (i : Fin l) :
    (∃ t, (encodeWith se mi mo).1 t = Sum.inl i) ↔
      RS.vertOf (RS.alpha (mi i).1.1) = v := by
  constructor
  · rintro ⟨t, ht⟩
    change Sum.map mi.symm mo.symm (port (se t)) = Sum.inl i at ht
    unfold port at ht
    split_ifs at ht with hio
    · have hj : mi i = incoming (se t) hio := by
        rw [← Sum.inl.inj ht]; exact mi.apply_symm_apply _
      have hd : (mi i).1.1 = RS.alpha (se t).1 := congrArg (fun b : BoundaryDart RS inner => b.1.1) hj
      rw [hd, RS.alpha_involutive]
      exact newDart_base (se t)
    · exact absurd ht (by simp)
  · intro hvv
    have hin : inner (RS.vertOf (RS.alpha (RS.alpha (mi i).1.1))) := by
      rw [RS.alpha_involutive]; exact (mi i).1.2
    refine ⟨se.symm ⟨RS.alpha (mi i).1.1, ⟨Or.inr hvv, fun h => hv (hvv ▸ h)⟩⟩, ?_⟩
    change Sum.map mi.symm mo.symm (port (se (se.symm _))) = Sum.inl i
    rw [se.apply_symm_apply]
    unfold port
    rw [dif_pos hin]
    refine congrArg Sum.inl ?_
    have : incoming (⟨RS.alpha (mi i).1.1, ⟨Or.inr hvv, fun h => hv (hvv ▸ h)⟩⟩ :
        NewDart RS inner v) hin = mi i :=
      Subtype.ext (Subtype.ext (RS.alpha_involutive _))
    rw [this, mi.symm_apply_apply]

theorem encodeWith_some_iff (i : Fin l) :
    (∃ j, (encodeWith se mi mo).2 j = some i) ↔
      RS.vertOf (RS.alpha (mi i).1.1) ≠ v := by
  constructor
  · rintro ⟨j, hj⟩
    simp only [encodeWith] at hj
    split_ifs at hj with hio
    · have hb : mi i = throughFromOuter inclusion (mo j) hio := by
        rw [← Option.some.inj hj]; exact mi.apply_symm_apply _
      have hd : (mi i).1.1 = (mo j).1.1 :=
        congrArg (fun b : BoundaryDart RS inner => b.1.1) hb
      rw [hd]
      exact fun h => (mo j).2 (Or.inr h)
  · intro hne
    have hbd : ¬ (enlarged inner v) (RS.vertOf (RS.alpha (mi i).1.1)) := by
      rintro (h | h)
      · exact (mi i).2 h
      · exact hne h
    have hbeq : throughFromOuter inclusion
        (⟨⟨(mi i).1.1, Or.inl (mi i).1.2⟩, hbd⟩ : BoundaryDart RS (enlarged inner v))
        (mi i).1.2 = mi i := rfl
    exact ⟨mo.symm ⟨⟨(mi i).1.1, Or.inl (mi i).1.2⟩, hbd⟩, by
      simp only [encodeWith, mo.apply_symm_apply, dif_pos (mi i).1.2, hbeq,
        Equiv.symm_apply_apply]⟩

/-- **Source steps encode into valid codes.** Validity holds for any supplied
enumeration; combined with `cyclicStarEquiv_succ` the cyclic encoder emits a
valid code whose slot order is the source rotation. -/
theorem encodeWith_valid (hv : ¬ inner v) :
    VertexCodePartition.Valid (encodeWith se mi mo) := by
  refine ⟨encodeWith_star_injective se mi mo, fun j => ?_, fun i => ?_, ?_⟩
  · rw [encodeWith_none_iff, ← encodeWith_inr_iff se mi mo]
  · rw [encodeWith_inl_iff se mi mo hv, ← not_exists,
      encodeWith_some_iff se mi mo, not_not]
  · exact fun j k i => encodeWith_wire_injective se mi mo j k i

theorem cyclicEncode_valid (hc : RS.IsCubic) (hv : ¬ inner v)
    (hcyc : VertexRotationCyclic RS) (d₀ : At RS v) :
    VertexCodePartition.Valid (cyclicEncode hc hv hcyc d₀ mi mo) :=
  encodeWith_valid _ mi mo hv

end
end Mettapedia.GraphTheory.FourColor.VertexCodeCyclicEncoder
