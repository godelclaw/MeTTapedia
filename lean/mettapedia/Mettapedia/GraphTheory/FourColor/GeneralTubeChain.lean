import Mettapedia.GraphTheory.FourColor.GeneralSlabEmbedding

/-!
# Periodic chains of slabs of arbitrary shape

`TubeOf RS T` is a chain of copies of one abstract slab shape `T`.  The words a
side accepts (`sideWords`) are pushed through `T`'s relation by each slab
(`sideWords_slab`), so along a coherent chain the side after `r` slabs accepts
the `r`-fold image of the initial words (`sideWords_side`).  When `T`'s relation
stabilises — the `(m+1)`-fold image equals the `m`-fold image on every set of
words — the sides after `m+j` and `m+1+j` slabs accept the same words
(`sideWords_stable`).  For the zigzag ring this is the kernel-checked `k-1`
law; for a rung of a thin annulus it is the lab's index.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab

open GoertzelV24RotationCutDartDecomposition
open GoertzelV24OpenTangleComposition

universe u

variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem.{u, u, u} V E} {k : Nat} [NeZero k]
variable {Vt It : Type u} {T : TwoSidedOpenTangleData Vt It (Fin k) (Fin k)}

/-- the words a side accepts on its boundary, in the coordinates `e` -/
def sideWords (side : V → Prop) (e : Fin k ≃ BoundaryDart RS side) : Set (Fin k → Color) :=
  {w | (fun b => w (e.symm b)) ∈ sideSupport RS side}

/-- the image of a set of words under the shape's relation -/
def relImage (T : TwoSidedOpenTangleData Vt It (Fin k) (Fin k)) (W : Set (Fin k → Color)) :
    Set (Fin k → Color) :=
  {w' | ∃ w ∈ W, T.AcceptsBoundaryWords w w'}

theorem sideWords_slab {inner : V → Prop} (S : SlabOf RS T inner) :
    sideWords S.inner' S.outEquiv = relImage T (sideWords inner S.inEquiv) := by
  ext w'
  simp only [sideWords, relImage, Set.mem_setOf_eq]
  exact S.mem_sideSupport_inner'_iff w'

/-- a chain of copies of the shape `T` -/
inductive TubeOf (RS : RotationSystem.{u, u, u} V E) {k : Nat} [NeZero k] {Vt It : Type u}
    (T : TwoSidedOpenTangleData Vt It (Fin k) (Fin k)) : (V → Prop) → Nat → Type u
  | nil (inner : V → Prop) (e : Fin k ≃ BoundaryDart RS inner) : TubeOf RS T inner 0
  | cons {inner : V → Prop} (S : SlabOf RS T inner) {n : Nat} (rest : TubeOf RS T S.inner' n) :
      TubeOf RS T inner (n + 1)

namespace TubeOf

def side : {inner : V → Prop} → {n : Nat} → TubeOf RS T inner n → Nat → (V → Prop)
  | inner, _, nil _ _, _ => inner
  | inner, _, cons _ _, 0 => inner
  | _, _, cons _ rest, r + 1 => rest.side r

noncomputable def sideEquiv : {inner : V → Prop} → {n : Nat} → (t : TubeOf RS T inner n) →
    (r : Nat) → Fin k ≃ BoundaryDart RS (t.side r)
  | _, _, nil _ e, _ => e
  | _, _, cons S _, 0 => S.inEquiv
  | _, _, cons _ rest, r + 1 => rest.sideEquiv r

noncomputable def firstEquiv : {inner : V → Prop} → {n : Nat} → TubeOf RS T inner n →
    Fin k ≃ BoundaryDart RS inner
  | _, _, nil _ e => e
  | _, _, cons S _ => S.inEquiv

def Coherent : {inner : V → Prop} → {n : Nat} → TubeOf RS T inner n → Prop
  | _, _, nil _ _ => True
  | _, _, cons S rest => rest.firstEquiv = S.outEquiv ∧ rest.Coherent

theorem sideWords_side : {inner : V → Prop} → {n : Nat} → (t : TubeOf RS T inner n) →
    t.Coherent → (r : Nat) → r ≤ n →
    sideWords (t.side r) (t.sideEquiv r) = (relImage T)^[r] (sideWords inner t.firstEquiv)
  | _, _, nil _ _, _, r, hr => by
    have : r = 0 := by omega
    subst this
    rfl
  | _, _, cons _ _, _, 0, _ => rfl
  | _, _, cons S rest, hc, r + 1, hr => by
    have hc' : rest.firstEquiv = S.outEquiv ∧ rest.Coherent := hc
    obtain ⟨hseam, hrest⟩ := hc'
    have ih := sideWords_side rest hrest r (by omega)
    show sideWords (rest.side r) (rest.sideEquiv r) = (relImage T)^[r + 1] (sideWords _ S.inEquiv)
    rw [ih, hseam, sideWords_slab, Function.iterate_succ_apply]

theorem side_mono : {inner : V → Prop} → {n : Nat} → (t : TubeOf RS T inner n) → (r : Nat) →
    ∀ v, t.side r v → t.side (r + 1) v
  | _, _, nil _ _, _, _, hv => hv
  | _, _, cons S rest, 0, _, hv => by
    cases rest <;> exact S.inner'_of_inner hv
  | _, _, cons _ rest, r + 1, v, hv => side_mono rest r v hv

/-- **stationarity along a periodic chain** once the shape's relation stabilises -/
theorem sideWords_stable {m : Nat}
    (hstab : ∀ W : Set (Fin k → Color), (relImage T)^[m + 1] W = (relImage T)^[m] W)
    {inner : V → Prop} {n : Nat} (t : TubeOf RS T inner n) (hc : t.Coherent) (j : Nat)
    (hn : m + 1 + j ≤ n) :
    sideWords (t.side (m + 1 + j)) (t.sideEquiv (m + 1 + j)) =
      sideWords (t.side (m + j)) (t.sideEquiv (m + j)) := by
  rw [sideWords_side t hc _ hn, sideWords_side t hc _ (by omega)]
  have h1 : (relImage T)^[m + 1 + j] (sideWords inner t.firstEquiv) =
      (relImage T)^[j] ((relImage T)^[m + 1] (sideWords inner t.firstEquiv)) := by
    rw [Nat.add_comm (m + 1) j, Function.iterate_add_apply]
  have h2 : (relImage T)^[m + j] (sideWords inner t.firstEquiv) =
      (relImage T)^[j] ((relImage T)^[m] (sideWords inner t.firstEquiv)) := by
    rw [Nat.add_comm m j, Function.iterate_add_apply]
  rw [h1, h2, hstab]

end TubeOf

end TubeSlab
end Mettapedia.GraphTheory.FourColor
