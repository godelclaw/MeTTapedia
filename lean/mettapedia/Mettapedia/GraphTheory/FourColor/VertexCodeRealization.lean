import Mettapedia.GraphTheory.FourColor.VertexCodePartition
import Mettapedia.GraphTheory.FourColor.TwoSidedBoundaryReindex
import Mettapedia.GraphTheory.FourColor.VertexAttachmentTransfer

/-!
# Constructing the physical meaning of every valid vertex code

Split the old boundary into retained and consumed ports, attach the
oriented cubic star, and reindex the surviving boundary. The constructor
exists for every valid code; its colour relation is exactly CodeAccepts.
Validity does not assert that a sewing preserves genus or connectivity.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexCodeRealization

open TubeSlab.VertexTransfer VertexCodePartition
open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open TwoSidedBoundaryReindex VertexAttachmentTransfer

noncomputable section
attribute [local instance] Classical.propDecidable
variable {l r : ℕ} (a : Code l r) (h : Valid a)

theorem star_word (x : Fin l → Color) (y : Fin r → Color) (t : Fin 3) :
    Sum.elim (fun p : Consumed a => x p) (fun p : Fresh a => y p)
      (starOrder a h t) = Sum.elim x y (a.1 t) := by
  rw [← starOrder_spec a h t]
  cases starOrder a h t <;> rfl

theorem star_relation (x : Fin l → Color) (y : Fin r → Color) :
    (star (starOrder a h)).AcceptsBoundaryWords
        (fun p : Consumed a => x p) (fun p : Fresh a => y p) ↔
      (∀ t, Sum.elim x y (a.1 t) ≠ 0) ∧
        Function.Injective (fun t => Sum.elim x y (a.1 t)) := by
  rw [star_accepts]
  constructor
  · rintro ⟨hn, hi⟩
    refine ⟨?_, ?_⟩
    · intro t
      rw [← star_word a h]
      exact hn _
    · intro s t he
      apply (starOrder a h).injective
      apply hi
      simpa only [star_word] using he
  · rintro ⟨hn, hi⟩
    refine ⟨?_, ?_⟩
    · intro p
      have hh := hn ((starOrder a h).symm p)
      simpa only [← star_word a h, Equiv.apply_symm_apply] using hh
    · intro p q he
      apply (starOrder a h).symm.injective
      apply hi
      simpa only [← star_word a h, Equiv.apply_symm_apply] using he

theorem codeAccepts_iff_star (x : Fin l → Color) (y : Fin r → Color) :
    CodeAccepts a x y ↔
      (∀ i, x i ≠ 0) ∧
      (∀ p : Retained a, x p.1.2 = y p.1.1) ∧
      (star (starOrder a h)).AcceptsBoundaryWords
        (fun p : Consumed a => x p) (fun p : Fresh a => y p) := by
  rw [star_relation]
  constructor
  · rintro ⟨hx, hy, hi, hw⟩
    refine ⟨hx, fun p => hw _ _ p.2, ?_, hi⟩
    intro t
    cases a.1 t with
    | inl i => exact hx i
    | inr j => exact hy j
  · rintro ⟨hx, hw, hn, hi⟩
    refine ⟨hx, ?_, hi, fun j i hj => hw ⟨(j, i), hj⟩⟩
    intro j
    cases hj : a.2 j with
    | none =>
      obtain ⟨t, ht⟩ := (h.2.1 j).mp hj
      simpa only [ht, Sum.elim_inr] using hn t
    | some i =>
      exact (hw ⟨(j, i), hj⟩) ▸ hx i

variable {V I : Type*}

def inCoordinates : Retained a ⊕ Consumed a ≃ Fin 0 ⊕ Fin l :=
  (inputEquiv a h).trans (Equiv.emptySum (Fin 0) (Fin l)).symm

def outCoordinates : Fin 0 ⊕ Fin r ≃ Retained a ⊕ Fresh a :=
  (Equiv.emptySum (Fin 0) (Fin r)).trans (outputEquiv a).symm

def prepared (T : TwoSidedOpenTangleData V I (Fin 0) (Fin l)) :=
  reindex T (inCoordinates a h)

/-- Literal attachment, with persistent ports remaining on the old piece. -/
def attach (T : TwoSidedOpenTangleData V I (Fin 0) (Fin l)) :
    TwoSidedOpenTangleData (V ⊕ Unit)
      ((I ⊕ Empty) ⊕ (Consumed a ⊕ Consumed a)) (Fin 0) (Fin r) :=
  reindex (append (prepared a h T) (starOrder a h)) (outCoordinates a)

def Supports (T : TwoSidedOpenTangleData V I (Fin 0) (Fin l))
    (x : Fin l → Color) : Prop := T.AcceptsBoundaryWords Fin.elim0 x

theorem supports_nonzero {T : TwoSidedOpenTangleData V I (Fin 0) (Fin l)}
    {x : Fin l → Color} (hx : Supports T x) (i : Fin l) : x i ≠ 0 := by
  obtain ⟨c, hc, _, hy⟩ := hx
  rw [← congrFun hy i]
  exact hc.2.2 _

theorem prepared_support (T : TwoSidedOpenTangleData V I (Fin 0) (Fin l))
    (x : Fin l → Color) :
    (prepared a h T).AcceptsBoundaryWords
      (fun p : Retained a => x p.1.2) (fun p : Consumed a => x p) ↔ Supports T x := by
  have he : (Sum.elim Fin.elim0 x) ∘ inCoordinates a h =
      Sum.elim (fun p : Retained a => x p.1.2) (fun p : Consumed a => x p) := by
    funext p
    cases p <;> rfl
  have hh := accepts_reindex T (inCoordinates a h) (Sum.elim Fin.elim0 x)
  rw [he, accepts_iff, accepts_iff] at hh
  exact hh

theorem attach_support (T : TwoSidedOpenTangleData V I (Fin 0) (Fin l))
    (y : Fin r → Color) :
    Supports (attach a h T) y ↔
      ∃ z : Consumed a → Color,
        (prepared a h T).AcceptsBoundaryWords (fun p : Retained a => y p.1.1) z ∧
        (star (starOrder a h)).AcceptsBoundaryWords z (fun p : Fresh a => y p) := by
  let w := Sum.elim (fun p : Retained a => y p.1.1) (fun p : Fresh a => y p)
  have hw (p : Retained a ⊕ Fresh a) : w p = y (outputEquiv a p) := by
    cases p <;> rfl
  have he : w ∘ outCoordinates a = Sum.elim Fin.elim0 y := by
    funext p
    rcases p with p | p
    · exact p.elim0
    · change w ((outputEquiv a).symm p) = y p
      rw [hw, Equiv.apply_symm_apply]
  have hh := accepts_reindex (append (prepared a h T) (starOrder a h))
    (outCoordinates a) w
  rw [he, accepts_iff] at hh
  change Supports (attach a h T) y ↔ Accepts _ w at hh
  rw [hh, accepts_iff, append, serialCompose_acceptsBoundaryWords_iff]
  rfl

/-- Every valid finite letter computes exactly the support of its real
attachment, in both directions and in the specified persistent coordinates. -/
theorem supports_attach_iff (T : TwoSidedOpenTangleData V I (Fin 0) (Fin l))
    (y : Fin r → Color) :
    Supports (attach a h T) y ↔ ∃ x, Supports T x ∧ CodeAccepts a x y := by
  rw [attach_support]
  constructor
  · rintro ⟨z, hz, hs⟩
    let x : Fin l → Color :=
      Sum.elim (fun p : Retained a => y p.1.1) z ∘ (inputEquiv a h).symm
    have hr (p : Retained a) : x p.1.2 = y p.1.1 := by
      change Sum.elim _ z ((inputEquiv a h).symm (inputEquiv a h (.inl p))) = _
      rw [Equiv.symm_apply_apply]
      rfl
    have hc (p : Consumed a) : x p = z p := by
      change Sum.elim _ z ((inputEquiv a h).symm (inputEquiv a h (.inr p))) = _
      rw [Equiv.symm_apply_apply]
      rfl
    have hx : Supports T x := by
      apply (prepared_support a h T x).mp
      simpa only [hr, hc] using hz
    refine ⟨x, hx, (codeAccepts_iff_star a h x y).mpr ⟨supports_nonzero hx, hr, ?_⟩⟩
    simpa only [hc] using hs
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨_, hr, hs⟩ := (codeAccepts_iff_star a h x y).mp hxy
    refine ⟨fun p => x p, ?_, hs⟩
    simpa only [hr] using (prepared_support a h T x).mpr hx

section Initial

variable (a : Code 0 r) (h : Valid a)

theorem initial_wire (j : Fin r) : a.2 j = none := by
  cases hj : a.2 j with
  | none => rfl
  | some i => exact i.elim0

def initialCoordinates : Fin 0 ⊕ Fin r ≃ Consumed a ⊕ Fresh a where
  toFun := Sum.elim Fin.elim0 (fun j => .inr ⟨j, initial_wire a j⟩)
  invFun := starVal a
  left_inv := by rintro (p | p); exact p.elim0; rfl
  right_inv := by
    rintro (p | p)
    · exact p.1.elim0
    · rfl

/-- The first vertex is a real star, not an empty tangle with an invented dart. -/
def initial : TwoSidedOpenTangleData Unit Empty (Fin 0) (Fin r) :=
  reindex (star (starOrder a h)) (initialCoordinates a)

theorem initial_support (y : Fin r → Color) :
    Supports (initial a h) y ↔ CodeAccepts a Fin.elim0 y := by
  let w := Sum.elim (fun p : Consumed a => p.1.elim0) (fun p : Fresh a => y p)
  have he : w ∘ initialCoordinates a = Sum.elim Fin.elim0 y := by
    funext p
    rcases p with p | p
    · exact p.elim0
    · rfl
  have hh := accepts_reindex (star (starOrder a h)) (initialCoordinates a) w
  rw [he, accepts_iff] at hh
  change Supports (initial a h) y ↔ Accepts _ w at hh
  rw [hh, accepts_iff, codeAccepts_iff_star a h]
  constructor
  · intro hs
    exact ⟨fun p => p.elim0, fun p => p.1.2.elim0, hs⟩
  · exact fun hs => hs.2.2

end Initial

end
end Mettapedia.GraphTheory.FourColor.VertexCodeRealization
