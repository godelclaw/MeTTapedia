import Mettapedia.GraphTheory.FourColor.TubeSlabEmbedding

/-!
# Chains of zigzag slabs: the tube instance of the corridor lemma

A `Tube` is a chain of zigzag slabs, each attached to the side enlarged by the
previous one.  With coherent seams (each slab's in-port labelling is the
previous slab's out-port labelling), the numerals of the words accepted after
`r` slabs are the `r`-fold ring image of the initial side's numerals
(`sideSet_side`), and the kernel-checked stabilisation gives: the sides after
`k-1+j` and `k+j` slabs accept the same words in tube coordinates
(`sideSet_stable`).  This is the corridor stabilisation on an arbitrary
rotation system; the splice against a least counterexample is the next step.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab

open GoertzelV24RotationCutDartDecomposition
open ZigzagRing
open TubeRingOrbit

universe u

variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem.{u, u, u} V E} {k : Nat} [NeZero k]

/-- numerals of the words a side accepts on its boundary, in the coordinates `e` -/
def sideSet (inner : V → Prop) (e : Fin k ≃ BoundaryDart RS inner) : Set Nat :=
  {Y | Y < 3 ^ k ∧ (fun b => wordOf k Y (e.symm b)) ∈ sideSupport RS inner}

theorem ne_zero_of_mem_sideSupport {inner : V → Prop} (e : Fin k ≃ BoundaryDart RS inner)
    {w : Fin k → Color} (h : (fun b => w (e.symm b)) ∈ sideSupport RS inner) (i : Fin k) :
    w i ≠ 0 := by
  obtain ⟨c, hc⟩ := h
  have := hc (e i)
  simp only [Equiv.symm_apply_apply] at this
  rw [← this]
  exact c.ne_zero _

/-- one slab pushes the side's numerals through the ring relation -/
theorem sideSet_slab {inner : V → Prop} (S : ZigzagSlab RS k inner) :
    sideSet S.inner' S.outEquiv = stepS k (sideSet inner S.inEquiv) := by
  ext Y
  simp only [sideSet, stepS, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hY, h⟩
    obtain ⟨w, hw, hring⟩ := (S.mem_sideSupport_inner'_iff (wordOf k Y)).mp h
    have hw0 := ne_zero_of_mem_sideSupport S.inEquiv hw
    refine ⟨hY, encW k w, encW_lt k w, ⟨encW_lt k w, ?_⟩, ?_⟩
    · rw [wordOf_encW k w hw0]; exact hw
    · rw [← accepts_iff_testBit k _ _ hY, wordOf_encW k w hw0]; exact hring
  · rintro ⟨hY, X, hX, ⟨-, hmem⟩, hb⟩
    exact ⟨hY, (S.mem_sideSupport_inner'_iff (wordOf k Y)).mpr
      ⟨wordOf k X, hmem, (accepts_iff_testBit k X Y hY).mpr hb⟩⟩

/-- a chain of slabs, each attached to the side enlarged by the previous one; the
empty chain carries a labelling of its side's boundary -/
inductive Tube (RS : RotationSystem.{u, u, u} V E) (k : Nat) [NeZero k] :
    (V → Prop) → Nat → Type u
  | nil (inner : V → Prop) (e : Fin k ≃ BoundaryDart RS inner) : Tube RS k inner 0
  | cons {inner : V → Prop} (S : ZigzagSlab RS k inner) {n : Nat} (rest : Tube RS k S.inner' n) :
      Tube RS k inner (n + 1)

namespace Tube

/-- the side after `r` slabs (the last side beyond the chain's length) -/
def side : {inner : V → Prop} → {n : Nat} → Tube RS k inner n → Nat → (V → Prop)
  | inner, _, nil _ _, _ => inner
  | inner, _, cons _ _, 0 => inner
  | _, _, cons _ rest, r + 1 => rest.side r

/-- the labelling of the side after `r` slabs -/
noncomputable def sideEquiv : {inner : V → Prop} → {n : Nat} → (t : Tube RS k inner n) → (r : Nat) →
    Fin k ≃ BoundaryDart RS (t.side r)
  | _, _, nil _ e, _ => e
  | _, _, cons S _, 0 => S.inEquiv
  | _, _, cons _ rest, r + 1 => rest.sideEquiv r

/-- the labelling of the initial side -/
noncomputable def firstEquiv : {inner : V → Prop} → {n : Nat} → Tube RS k inner n →
    Fin k ≃ BoundaryDart RS inner
  | _, _, nil _ e => e
  | _, _, cons S _ => S.inEquiv

/-- coherent seams: each slab's in-port labelling is the previous slab's out-port labelling -/
def Coherent : {inner : V → Prop} → {n : Nat} → Tube RS k inner n → Prop
  | _, _, nil _ _ => True
  | _, _, cons S rest => rest.firstEquiv = S.outEquiv ∧ rest.Coherent

/-- the numerals after `r` slabs are the `r`-fold ring image of the initial numerals -/
theorem sideSet_side : {inner : V → Prop} → {n : Nat} → (t : Tube RS k inner n) → t.Coherent →
    (r : Nat) → r ≤ n →
    sideSet (t.side r) (t.sideEquiv r) = (stepS k)^[r] (sideSet inner t.firstEquiv)
  | _, _, nil _ _, _, r, hr => by
    have : r = 0 := by omega
    subst this
    rfl
  | _, _, cons S rest, _, 0, _ => rfl
  | _, _, cons S rest, hc, r + 1, hr => by
    have hc' : rest.firstEquiv = S.outEquiv ∧ rest.Coherent := hc
    obtain ⟨hseam, hrest⟩ := hc'
    have ih := sideSet_side rest hrest r (by omega)
    show sideSet (rest.side r) (rest.sideEquiv r) = (stepS k)^[r + 1] (sideSet _ S.inEquiv)
    rw [ih, hseam, sideSet_slab, Function.iterate_succ_apply]

/-- the sides are nested -/
theorem side_mono : {inner : V → Prop} → {n : Nat} → (t : Tube RS k inner n) → (r : Nat) →
    ∀ v, t.side r v → t.side (r + 1) v
  | _, _, nil _ _, _, _, hv => hv
  | _, _, cons S rest, 0, _, hv => by
    cases rest <;> exact S.inner'_of_inner hv
  | _, _, cons _ rest, r + 1, v, hv => side_mono rest r v hv

theorem stepS_iterate_stable (h : stabilizes k = true) (S : Set Nat)
    (hS : ∀ X ∈ S, X < 3 ^ k) (j : Nat) :
    (stepS k)^[k + j] S = (stepS k)^[k - 1 + j] S := by
  rw [show k + j = j + k by omega, Function.iterate_add_apply,
    stepS_iterate_of_stabilizes k h S hS, show k - 1 + j = j + (k - 1) by omega,
    Function.iterate_add_apply]

/-- **Tube stabilisation.**  Along a coherent chain, the sides after `k-1+j` and `k+j`
slabs accept the same words in tube coordinates. -/
theorem sideSet_stable (h : stabilizes k = true) {inner : V → Prop} {n : Nat}
    (t : Tube RS k inner n) (hc : t.Coherent) (j : Nat) (hn : k + j ≤ n) :
    sideSet (t.side (k + j)) (t.sideEquiv (k + j)) =
      sideSet (t.side (k - 1 + j)) (t.sideEquiv (k - 1 + j)) := by
  rw [sideSet_side t hc _ hn, sideSet_side t hc _ (by omega),
    stepS_iterate_stable h _ (fun X hX => hX.1) j]

theorem sideSet_stable_five {inner : V → Prop} {n : Nat}
    (t : Tube RS 5 inner n) (hc : t.Coherent) (j : Nat) (hn : 5 + j ≤ n) :
    sideSet (t.side (5 + j)) (t.sideEquiv (5 + j)) =
      sideSet (t.side (4 + j)) (t.sideEquiv (4 + j)) :=
  sideSet_stable zigzag5_stabilizes t hc j hn

theorem sideSet_stable_six {inner : V → Prop} {n : Nat}
    (t : Tube RS 6 inner n) (hc : t.Coherent) (j : Nat) (hn : 6 + j ≤ n) :
    sideSet (t.side (6 + j)) (t.sideEquiv (6 + j)) =
      sideSet (t.side (5 + j)) (t.sideEquiv (5 + j)) :=
  sideSet_stable zigzag6_stabilizes t hc j hn

end Tube

end TubeSlab
end Mettapedia.GraphTheory.FourColor
