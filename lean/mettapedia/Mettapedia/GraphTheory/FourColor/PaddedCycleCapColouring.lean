import Mettapedia.GraphTheory.FourColor.PaddedCycleCapTangle
import Mettapedia.GraphTheory.FourColor.CycleSeamTransfer

/-!
# Uniform reconstruction across a padded cycle cap

The inner and middle radial edge colours are chosen equal. Each sector then
needs only a different nonzero colour, avoiding its first boundary letter.
The cyclic avoidance theorem closes these shared choices. All eight vertex
constraints are reconstructed in the literal tangle.
-/

namespace Mettapedia.GraphTheory.FourColor.PaddedCycleCap

open GoertzelV24OpenTangleComposition

set_option backward.isDefEq.respectTransparency false

variable (m : ℕ) [NeZero m]

/-- The actual two vertices of the smaller cycle in each sector. -/
structure CycleWitness (w : Boundary m → Color) (s : Fin m → Color) : Prop where
  boundary_nonzero : ∀ b, w b ≠ 0
  seam_nonzero : ∀ i, s i ≠ 0
  middle_nonzero : ∀ i, s i + w (i,false) ≠ 0
  next_seam : ∀ i, s (i+1) = s i + w (i,false) + w (i,true)

set_option synthInstance.maxSize 1024 in
private theorem pair_constancy (s t c d : Color)
    (hs : s ≠ 0) (ht : t ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hs' : s+c ≠ 0) (ht' : t+c ≠ 0) (h : t = s+c+d) : d = c := by
  revert s t c d
  decide

theorem CycleWitness.first_nonconstant {w : Boundary m → Color} {s : Fin m → Color}
    (h : CycleWitness m w s) (hn : ¬ ∃ c, ∀ b, w b = c) :
    ∃ i j, w (i,false) ≠ w (j,false) := by
  by_contra hc
  push Not at hc
  let c := w (0,false)
  have hf (i) : w (i,false) = c := hc i 0
  have ht (i) : w (i,true) = c := by
    apply pair_constancy (s i) (s (i+1)) c (w (i,true))
      (h.seam_nonzero _) (h.seam_nonzero _) (h.boundary_nonzero _) (h.boundary_nonzero _)
    · simpa [hf] using h.middle_nonzero i
    · simpa [hf] using h.middle_nonzero (i+1)
    · simpa [hf] using h.next_seam i
  exact hn ⟨c, by rintro ⟨i,b⟩; cases b; exact hf i; exact ht i⟩

def edgeColours (w : Boundary m → Color) (s q : Fin m → Color)
    (i : Fin m) : Fin 11 → Color :=
  ![q i, q i, s (i+1), q (i-1)+q i, q i, q i+w (i,false),
    w (i,false), w (i,false), s i+w (i,false), s i, s i+w (i,false)]

def colouringOf (w : Boundary m → Color) (s q : Fin m → Color) : Dart m → Color
  | .inl (i,(e,_)) => edgeColours m w s q i e
  | .inr (.inl e) => nomatch e
  | .inr (.inr b) => w b

private def GoodStar (f : Fin 3 → Color) : Prop :=
  (∀ j, f j ≠ 0) ∧ Function.Injective f

private theorem good_three (a b c : Color) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hs : a+b+c = 0) : GoodStar ![a,b,c] := by
  unfold GoodStar
  revert a b c
  decide

theorem colouringOf_isTait (hm : 2 ≤ m) {w : Boundary m → Color}
    {s q : Fin m → Color} (h : CycleWitness m w s)
    (hq : CycleCap.Valid m q) (havoid : ∀ i, q i ≠ w (i,false)) :
    (tangle m hm).IsTaitColoring (colouringOf m w s q) := by
  have hprev (i) : q (i-1) ≠ q i := by simpa using hq.2 (i-1)
  have hstars (i : Fin m) (v : Fin 8) :
      GoodStar (fun j => colouringOf m w s q (star m (i,v,j))) := by
    have hqp := hq.1 (i-1)
    have hqi := hq.1 i
    have hw := h.boundary_nonzero (i,false)
    have hw' := h.boundary_nonzero (i,true)
    have hs := h.seam_nonzero i
    have hs' := h.seam_nonzero (i+1)
    have hm' := h.middle_nonzero i
    have hqq := add_ne_zero_of_ne (hprev i)
    have hqw := add_ne_zero_of_ne (havoid i)
    have hc := h.next_seam i
    have hexpand (f : Fin 3 → Color) : f = ![f 0, f 1, f 2] := by
      funext j
      fin_cases j <;> rfl
    rw [hexpand (fun j => colouringOf m w s q (star m (i,v,j)))]
    apply good_three
    all_goals fin_cases v <;> simp [star, colouringOf, edgeColours]
    all_goals first
      | assumption
      | (try rw [hc]
         abel_nf
         simp [two_mul])
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i,e,b⟩
    rfl
  · intro d e hv hne he
    obtain ⟨⟨i,v,a⟩, rfl⟩ : ∃ p, star m p = d := ⟨position m d, star_position m d⟩
    obtain ⟨⟨j,u,b⟩, rfl⟩ : ∃ p, star m p = e := ⟨position m e, star_position m e⟩
    simp only [vertOf_star, Prod.mk.injEq] at hv
    obtain ⟨rfl,rfl⟩ := hv
    have hab := (hstars i v).2 he
    subst b
    exact hne rfl
  · intro d
    rw [← star_position m d]
    exact (hstars _ _).1 _

/-- One shared cyclic choice constructs all internal edge colours. -/
theorem accepts_of_nonconstant (hm : 2 ≤ m) {w : Boundary m → Color}
    {s : Fin m → Color} (h : CycleWitness m w s)
    (hn : ¬ ∃ c, ∀ b, w b = c) :
    (tangle m hm).AcceptsBoundaryWords Empty.elim w := by
  obtain ⟨q,hq,havoid⟩ := CyclicColourAvoidance.exists_cycle (fun i => w (i,false))
    (fun i => h.boundary_nonzero _) (h.first_nonconstant m hn)
  exact ⟨colouringOf m w s q, colouringOf_isTait m hm h hq havoid,
    funext (fun e => e.elim), rfl⟩

end Mettapedia.GraphTheory.FourColor.PaddedCycleCap
