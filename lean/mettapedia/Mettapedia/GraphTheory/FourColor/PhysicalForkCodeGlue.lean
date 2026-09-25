import Mettapedia.GraphTheory.FourColor.PhysicalForkCodePiece

/-!
# Gluing open pieces along a fork descriptor

Two open pieces with named open vertices are glued along a legal descriptor:
paired open vertices become one vertex, and the right piece's ends at such a
vertex are rotated into the left piece's open slots.  At a vertex where both
pieces have one end, the right end goes directly after the left end when the
descriptor keeps the right mark, and directly before it when it keeps the left
mark.  The parent's open vertices are named by the kept marks.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodePiece

open Equiv Equiv.Perm
open GoertzelV24ForkInterfaceSupport GoertzelV24OrderedCutFaceReturnProfile
open EdgeShoreFaceForkFold PhysicalForkCodeFaces PhysicalForkCodeCut PhysicalForkCodeEuler
open PhysicalForkCodeFold PhysicalForkCode

noncomputable section
attribute [local instance] Classical.propDecidable

/-! ## Slots of an open vertex -/

namespace Piece

variable (P : Piece)

/-- The interface slot of a vertex: an occupied slot followed by an open one. -/
def ifaceSlot (v : P.V) : ZMod 3 :=
  if h : ∃ k, P.Filled (v, k) ∧ ¬ P.Filled (v, k + 1) then h.choose else 0

variable {P}

theorem ifaceSlot_spec {v : P.V} (hv : P.IsOpen v) :
    P.Filled (v, P.ifaceSlot v) ∧ ¬ P.Filled (v, P.ifaceSlot v + 1) := by
  have hex : ∃ k, P.Filled (v, k) ∧ ¬ P.Filled (v, k + 1) := by
    obtain ⟨x, hx⟩ := P.covered v
    set k := (P.place x).2
    have hk : P.Filled (v, k) := ⟨x, by rw [← hx]⟩
    obtain ⟨l, hl⟩ := hv
    by_cases h1 : P.Filled (v, k + 1)
    · by_cases h2 : P.Filled (v, k + 1 + 1)
      · exfalso
        apply hl
        rcases zmod3_cases (l - k) with h | h | h
        · rw [show l = k by rw [sub_eq_zero] at h; exact h]; exact hk
        · rw [show l = k + 1 by rw [← h]; ring]; exact h1
        · have hl' : l = k + 1 + 1 := by rw [add_assoc, one_add_one_eq_two, ← h]; ring
          rw [hl']
          exact h2
      · exact ⟨k + 1, h1, h2⟩
    · exact ⟨k, hk, h1⟩
  unfold ifaceSlot
  rw [dite_eq_left hex]
  exact hex.choose_spec

/-- **The occupied slots of an open vertex.**  The interface slot, and the slot
two after it exactly when the vertex carries two ends. -/
theorem filled_iff {v : P.V} (hv : P.IsOpen v) (k : ZMod 3) :
    P.Filled (v, k) ↔ k = P.ifaceSlot v ∨ (P.two v = true ∧ k = P.ifaceSlot v + 2) := by
  obtain ⟨ha, ha1⟩ := ifaceSlot_spec hv
  set a := P.ifaceSlot v
  have htwo : P.two v = true ↔ P.Filled (v, a + 2) := by
    unfold Piece.two
    rw [decide_eq_true_iff]
    constructor
    · rintro ⟨l, hl, hl'⟩
      rcases zmod3_cases (l - a) with h | h | h
      · rw [show l = a by rw [sub_eq_zero] at h; exact h] at hl'
        exact absurd hl' ha1
      · rw [show l = a + 1 by rw [← h]; ring] at hl
        exact absurd hl ha1
      · rwa [show l = a + 2 by rw [← h]; ring] at hl
    · intro h
      exact ⟨a + 2, h, by rw [add_assoc, show (2 : ZMod 3) + 1 = 0 by decide, add_zero]; exact ha⟩
  constructor
  · intro hk
    rcases zmod3_cases (k - a) with h | h | h
    · left; rw [sub_eq_zero] at h; exact h
    · rw [show k = a + 1 by rw [← h]; ring] at hk
      exact absurd hk ha1
    · right
      have hk' : k = a + 2 := by rw [← h]; ring
      exact ⟨htwo.mpr (hk' ▸ hk), hk'⟩
  · rintro (rfl | ⟨h2, rfl⟩)
    · exact ha
    · exact htwo.mp h2

theorem not_filled_add_one {v : P.V} (hv : P.IsOpen v) :
    ¬ P.Filled (v, P.ifaceSlot v + 1) := (ifaceSlot_spec hv).2

end Piece

/-! ## The glued piece -/

section Defs

variable {PL PR : Piece} {nL nR nP : ℕ} (ℓL : Fin nL ≃ PL.OpenV) (ℓR : Fin nR ≃ PR.OpenV)
  (g : Glue nL nR nP)

/-- The left position a right vertex is glued to. -/
def partnerPos (w : PR.V) : Option (Fin nL) :=
  if hw : PR.IsOpen w then
    (g.pair (.inr (ℓR.symm ⟨w, hw⟩))).elim some (fun _ => none)
  else none

/-- The vertices of the glued piece: all left vertices, and the right vertices
glued to none. -/
abbrev GV (PL : Piece) {PR : Piece} {nL nR nP : ℕ} (ℓR : Fin nR ≃ PR.OpenV)
    (g : Glue nL nR nP) :=
  PL.V ⊕ {w : PR.V // partnerPos ℓR g w = none}

/-- Where a right vertex goes. -/
def vR (w : PR.V) : GV PL ℓR g :=
  if h : partnerPos ℓR g w = none then .inr ⟨w, h⟩
  else .inl (ℓL ((partnerPos ℓR g w).get (Option.ne_none_iff_isSome.mp h))).1

/-- The rotation of the right slots at a glued vertex. -/
def shift (w : PR.V) : ZMod 3 :=
  (partnerPos ℓR g w).elim 0 fun i =>
    PL.ifaceSlot (ℓL i).1 - PR.ifaceSlot w +
      (if PR.two w = true ∨ Sum.inl i ∈ Set.range g.keep then 2 else 1)

/-- The ends of the glued piece. -/
def gluePlace : (PL.E ⊕ PR.E) × Bool → GV PL ℓR g × ZMod 3
  | (.inl e, b) => (.inl (PL.place (e, b)).1, (PL.place (e, b)).2)
  | (.inr e, b) => (vR ℓL ℓR g (PR.place (e, b)).1,
      (PR.place (e, b)).2 + shift ℓL ℓR g (PR.place (e, b)).1)

/-- The hypotheses of a glue: a legal descriptor whose `two` fields are the
pieces' own. -/
structure GlueOK (L : Code nL) (R : Code nR) : Prop where
  legal : Legal L R g
  twoL : ∀ i, L.two i = PL.two (ℓL i).1
  twoR : ∀ j, R.two j = PR.two (ℓR j).1

end Defs

section Lemmas

variable {PL PR : Piece} {nL nR nP : ℕ} (ℓL : Fin nL ≃ PL.OpenV) (ℓR : Fin nR ≃ PR.OpenV)
  (g : Glue nL nR nP) {L : Code nL} {R : Code nR} (h : GlueOK ℓL ℓR g L R)

theorem partnerPos_eq_some_iff {w : PR.V} {i : Fin nL} :
    partnerPos ℓR g w = some i ↔
      ∃ hw : PR.IsOpen w, g.pair (.inr (ℓR.symm ⟨w, hw⟩)) = .inl i := by
  unfold partnerPos
  constructor
  · intro hp
    by_cases hw : PR.IsOpen w
    · rw [dite_eq_left hw] at hp
      refine ⟨hw, ?_⟩
      revert hp
      cases g.pair (.inr (ℓR.symm ⟨w, hw⟩)) with
      | inl i' => intro hp; simp only [Sum.elim_inl, Option.some.injEq] at hp; rw [hp]
      | inr _ => intro hp; simp at hp
    · rw [dite_eq_right hw] at hp; exact absurd hp (by simp)
  · rintro ⟨hw, hp⟩
    rw [dite_eq_left hw, hp]
    rfl

theorem vR_of_some {w : PR.V} {i : Fin nL} (hp : partnerPos ℓR g w = some i) :
    vR ℓL ℓR g w = .inl (ℓL i).1 := by
  unfold vR
  rw [dite_eq_right (by rw [hp]; simp)]
  simp only [hp, Option.get_some]

theorem vR_of_none {w : PR.V} (hp : partnerPos ℓR g w = none) :
    vR ℓL ℓR g w = .inr ⟨w, hp⟩ := by
  unfold vR
  rw [dite_eq_left hp]

theorem shift_of_some {w : PR.V} {i : Fin nL} (hp : partnerPos ℓR g w = some i) :
    shift ℓL ℓR g w = PL.ifaceSlot (ℓL i).1 - PR.ifaceSlot w +
      (if PR.two w = true ∨ Sum.inl i ∈ Set.range g.keep then 2 else 1) := by
  unfold shift
  rw [hp]
  rfl

theorem shift_of_none {w : PR.V} (hp : partnerPos ℓR g w = none) : shift ℓL ℓR g w = 0 := by
  unfold shift
  rw [hp]
  rfl

/-- A right position's partner, read on the right vertex. -/
theorem partnerPos_ℓR_eq_some_iff (j : Fin nR) (i : Fin nL) :
    partnerPos ℓR g (ℓR j).1 = some i ↔ g.pair (.inr j) = .inl i := by
  rw [partnerPos_eq_some_iff]
  constructor
  · rintro ⟨hw, hp⟩
    have : ℓR.symm ⟨(ℓR j).1, hw⟩ = j := by rw [Equiv.symm_apply_eq]
    rwa [this] at hp
  · intro hp
    refine ⟨(ℓR j).2, ?_⟩
    have : ℓR.symm ⟨(ℓR j).1, (ℓR j).2⟩ = j := by simp
    rw [this, hp]

theorem partnerPos_injective {w w' : PR.V} {i : Fin nL} (hp : partnerPos ℓR g w = some i)
    (hp' : partnerPos ℓR g w' = some i) : w = w' := by
  obtain ⟨hw, hq⟩ := (partnerPos_eq_some_iff ℓR g).mp hp
  obtain ⟨hw', hq'⟩ := (partnerPos_eq_some_iff ℓR g).mp hp'
  have := g.pair.injective (hq.trans hq'.symm)
  simp only [Sum.inr.injEq] at this
  exact congrArg Subtype.val (ℓR.symm.injective this)

theorem vR_injective : Function.Injective (vR ℓL ℓR g) := by
  intro w w' hv
  by_cases hw : partnerPos ℓR g w = none <;> by_cases hw' : partnerPos ℓR g w' = none
  · rw [vR_of_none ℓL ℓR g hw, vR_of_none ℓL ℓR g hw'] at hv
    simpa using hv
  · obtain ⟨i', hi'⟩ := Option.ne_none_iff_exists'.mp hw'
    rw [vR_of_none ℓL ℓR g hw, vR_of_some ℓL ℓR g hi'] at hv
    exact absurd hv Sum.inr_ne_inl
  · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hw
    rw [vR_of_some ℓL ℓR g hi, vR_of_none ℓL ℓR g hw'] at hv
    exact absurd hv Sum.inl_ne_inr
  · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hw
    obtain ⟨i', hi'⟩ := Option.ne_none_iff_exists'.mp hw'
    rw [vR_of_some ℓL ℓR g hi, vR_of_some ℓL ℓR g hi'] at hv
    simp only [Sum.inl.injEq] at hv
    have hii : i = i' := ℓL.injective (Subtype.ext hv)
    subst hii
    exact partnerPos_injective ℓR g hi hi'

include h

/-- The pair of a left position, read through `partnerPos`. -/
theorem pair_inl_of_partner {w : PR.V} {i : Fin nL} (hp : partnerPos ℓR g w = some i) :
    ∃ hw : PR.IsOpen w, g.pair (.inl i) = .inr (ℓR.symm ⟨w, hw⟩) := by
  obtain ⟨hw, hq⟩ := (partnerPos_eq_some_iff ℓR g).mp hp
  exact ⟨hw, by rw [← hq, h.legal.pair_invol]⟩

theorem partnerPos_ℓR_eq_none_iff (j : Fin nR) :
    partnerPos ℓR g (ℓR j).1 = none ↔ g.pair (.inr j) = .inr j := by
  constructor
  · intro hp
    rcases h.legal.pair_right j with h' | ⟨i, h'⟩
    · exact h'
    · rw [(partnerPos_ℓR_eq_some_iff ℓR g j i).mpr h'] at hp; exact absurd hp (by simp)
  · intro hq
    by_contra hne
    obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hne
    rw [(partnerPos_ℓR_eq_some_iff ℓR g j i).mp hi] at hq
    exact Sum.inl_ne_inr hq

theorem no_partner_of_fixed {i : Fin nL} (hi : g.pair (.inl i) = .inl i) (w : PR.V) :
    partnerPos ℓR g w ≠ some i := by
  intro hp
  obtain ⟨hw, hq⟩ := pair_inl_of_partner ℓL ℓR g h hp
  rw [hi] at hq
  exact Sum.inl_ne_inr hq

/-- **The right ends land in open left slots.** -/
theorem shifted_not_filled {w : PR.V} {i : Fin nL} (hp : partnerPos ℓR g w = some i)
    {k : ZMod 3} (hk : PR.Filled (w, k)) : ¬ PL.Filled ((ℓL i).1, k + shift ℓL ℓR g w) := by
  obtain ⟨hw, hq⟩ := pair_inl_of_partner ℓL ℓR g h hp
  set j := ℓR.symm ⟨w, hw⟩ with hj
  have hwj : (ℓR j).1 = w := by simp [hj]
  have hopenL := (ℓL i).2
  rw [shift_of_some ℓL ℓR g hp]
  rw [Piece.filled_iff hw] at hk
  rw [Piece.filled_iff hopenL]
  set a := PL.ifaceSlot (ℓL i).1
  set c := PR.ifaceSlot w
  have hdeg := h.legal.degree (.inl i) (by rw [hq]; exact Sum.inr_ne_inl)
  rw [hq] at hdeg
  simp only [twoOf, h.twoL, h.twoR, hwj] at hdeg
  have hne := zmod3_add_ne a
  by_cases hR2 : PR.two w = true
  · have hL2 : PL.two (ℓL i).1 = false := by
      rcases hdeg with h1 | h1
      · exact h1
      · rw [h1] at hR2; exact absurd hR2 (by decide)
    rw [ite_eq_left (Or.inl hR2)]
    rcases hk with rfl | ⟨_, rfl⟩
    · have : PR.ifaceSlot w + (a - PR.ifaceSlot w + 2) = a + 2 := by ring
      rw [this, hL2]
      simp only [Bool.false_eq_true, false_and, or_false]
      exact hne.2.1
    · have : PR.ifaceSlot w + 2 + (a - PR.ifaceSlot w + 2) = a + 1 := by
        rw [show PR.ifaceSlot w + 2 + (a - PR.ifaceSlot w + 2) = a + 4 by ring,
          show (4 : ZMod 3) = 1 by decide]
      rw [this, hL2]
      simp only [Bool.false_eq_true, false_and, or_false]
      exact hne.1
  · have hR2' : PR.two w = false := by simpa using hR2
    rcases hk with rfl | ⟨h2, _⟩
    · by_cases hkeep : Sum.inl i ∈ Set.range g.keep
      · rw [ite_eq_left (Or.inr hkeep)]
        have hopen : OpenAt L R g (.inl i) := by
          by_contra hno
          exact h.legal.keep_closed (.inl i) (by rw [hq]; exact Sum.inr_ne_inl) hno hkeep
        have hL2 : PL.two (ℓL i).1 = false := by
          have := hopen.1
          simp only [twoOf, h.twoL] at this
          exact this
        have : PR.ifaceSlot w + (a - PR.ifaceSlot w + 2) = a + 2 := by ring
        rw [this, hL2]
        simp only [Bool.false_eq_true, false_and, or_false]
        exact hne.2.1
      · rw [ite_eq_right (by simp [hR2', hkeep])]
        have : PR.ifaceSlot w + (a - PR.ifaceSlot w + 1) = a + 1 := by ring
        rw [this]
        rintro (h1 | ⟨_, h1⟩)
        · exact hne.1 h1
        · exact hne.2.2 h1.symm
    · rw [hR2'] at h2; exact absurd h2 (by decide)

theorem gluePlace_injective : Function.Injective (gluePlace ℓL ℓR g) := by
  rintro ⟨e | e, b⟩ ⟨e' | e', b'⟩ hx
  · simp only [gluePlace, Prod.mk.injEq, Sum.inl.injEq] at hx
    have := PL.place_injective (Prod.ext hx.1 hx.2)
    simp only [Prod.mk.injEq] at this
    rw [this.1, this.2]
  · exfalso
    simp only [gluePlace, Prod.mk.injEq] at hx
    obtain ⟨hv, hk⟩ := hx
    by_cases hw : partnerPos ℓR g (PR.place (e', b')).1 = none
    · rw [vR_of_none ℓL ℓR g hw] at hv; exact Sum.inl_ne_inr hv
    · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hw
      rw [vR_of_some ℓL ℓR g hi] at hv
      simp only [Sum.inl.injEq] at hv
      apply shifted_not_filled ℓL ℓR g h hi (PR.filled_place (e', b'))
      rw [← hv, ← hk]
      exact PL.filled_place (e, b)
  · exfalso
    simp only [gluePlace, Prod.mk.injEq] at hx
    obtain ⟨hv, hk⟩ := hx
    by_cases hw : partnerPos ℓR g (PR.place (e, b)).1 = none
    · rw [vR_of_none ℓL ℓR g hw] at hv; exact Sum.inr_ne_inl hv
    · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hw
      rw [vR_of_some ℓL ℓR g hi] at hv
      simp only [Sum.inl.injEq] at hv
      apply shifted_not_filled ℓL ℓR g h hi (PR.filled_place (e, b))
      rw [hv, hk]
      exact PL.filled_place (e', b')
  · simp only [gluePlace, Prod.mk.injEq] at hx
    obtain ⟨hv, hk⟩ := hx
    have hw := vR_injective ℓL ℓR g hv
    rw [hw] at hk
    have hk' := add_right_cancel hk
    have := PR.place_injective (Prod.ext hw hk')
    simp only [Prod.mk.injEq] at this
    rw [this.1, this.2]

end Lemmas

/-- **The glued piece.** -/
abbrev gluePiece {PL PR : Piece} {nL nR nP : ℕ} (ℓL : Fin nL ≃ PL.OpenV) (ℓR : Fin nR ≃ PR.OpenV)
    (g : Glue nL nR nP) {L : Code nL} {R : Code nR} (h : GlueOK ℓL ℓR g L R) : Piece where
  V := GV PL ℓR g
  E := PL.E ⊕ PR.E
  place := gluePlace ℓL ℓR g
  place_injective := gluePlace_injective ℓL ℓR g h
  loopless := by
    rintro (e | e)
    · simp only [gluePlace, ne_eq, Sum.inl.injEq]
      exact PL.loopless e
    · simp only [gluePlace, ne_eq]
      intro hv
      exact PR.loopless e (vR_injective ℓL ℓR g hv)
  covered := by
    rintro (v | ⟨w, hw⟩)
    · obtain ⟨x, hx⟩ := PL.covered v
      exact ⟨(.inl x.1, x.2), by simp [gluePlace, hx]⟩
    · obtain ⟨x, hx⟩ := PR.covered w
      refine ⟨(.inr x.1, x.2), ?_⟩
      simp only [gluePlace]
      rw [hx, vR_of_none ℓL ℓR g hw]

/-! ## Slots of the glued piece -/

section Slots

variable {PL PR : Piece} {nL nR nP : ℕ} (ℓL : Fin nL ≃ PL.OpenV) (ℓR : Fin nR ≃ PR.OpenV)
  (g : Glue nL nR nP) {L : Code nL} {R : Code nR} (h : GlueOK ℓL ℓR g L R)

theorem glue_filled_inl (v : PL.V) (k : ZMod 3) :
    (gluePiece ℓL ℓR g h).Filled (.inl v, k) ↔
      PL.Filled (v, k) ∨ ∃ w i, partnerPos ℓR g w = some i ∧ (ℓL i).1 = v ∧
        PR.Filled (w, k - shift ℓL ℓR g w) := by
  constructor
  · rintro ⟨⟨e | e, b⟩, hx⟩
    · left
      simp only [gluePiece, gluePlace, Prod.mk.injEq, Sum.inl.injEq] at hx
      exact ⟨(e, b), Prod.ext hx.1 hx.2⟩
    · right
      simp only [gluePiece, gluePlace, Prod.mk.injEq] at hx
      obtain ⟨hv, hk⟩ := hx
      by_cases hw : partnerPos ℓR g (PR.place (e, b)).1 = none
      · rw [vR_of_none ℓL ℓR g hw] at hv; exact absurd hv Sum.inr_ne_inl
      · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hw
        rw [vR_of_some ℓL ℓR g hi, Sum.inl.injEq] at hv
        exact ⟨_, i, hi, hv, (e, b), Prod.ext rfl (by rw [← hk]; ring)⟩
  · rintro (⟨⟨e, b⟩, hx⟩ | ⟨w, i, hi, hv, ⟨⟨e, b⟩, hx⟩⟩)
    · exact ⟨(.inl e, b), by simp only [gluePiece, gluePlace, hx]⟩
    · refine ⟨(.inr e, b), ?_⟩
      simp only [gluePiece, gluePlace]
      rw [hx, vR_of_some ℓL ℓR g hi, hv]
      simp

theorem glue_filled_inr {w : PR.V} (hw : partnerPos ℓR g w = none) (k : ZMod 3) :
    (gluePiece ℓL ℓR g h).Filled (.inr ⟨w, hw⟩, k) ↔ PR.Filled (w, k) := by
  constructor
  · rintro ⟨⟨e | e, b⟩, hx⟩
    · simp [gluePiece, gluePlace] at hx
    · simp only [gluePiece, gluePlace, Prod.mk.injEq] at hx
      obtain ⟨hv, hk⟩ := hx
      by_cases hw' : partnerPos ℓR g (PR.place (e, b)).1 = none
      · rw [vR_of_none ℓL ℓR g hw'] at hv
        simp only [Sum.inr.injEq, Subtype.mk.injEq] at hv
        rw [shift_of_none ℓL ℓR g hw', add_zero] at hk
        exact ⟨(e, b), Prod.ext hv hk⟩
      · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hw'
        rw [vR_of_some ℓL ℓR g hi] at hv; exact absurd hv Sum.inl_ne_inr
  · rintro ⟨⟨e, b⟩, hx⟩
    refine ⟨(.inr e, b), ?_⟩
    simp only [gluePiece, gluePlace]
    rw [hx, vR_of_none ℓL ℓR g hw, shift_of_none ℓL ℓR g hw, add_zero]

theorem glue_filled_unshared {i : Fin nL} (hi : g.pair (.inl i) = .inl i) (k : ZMod 3) :
    (gluePiece ℓL ℓR g h).Filled (.inl (ℓL i).1, k) ↔ PL.Filled ((ℓL i).1, k) := by
  rw [glue_filled_inl]
  constructor
  · rintro (hk | ⟨w, i', hi', hv, _⟩)
    · exact hk
    · have : i' = i := ℓL.injective (Subtype.ext hv)
      subst this
      exact absurd hi' (no_partner_of_fixed ℓL ℓR g h hi w)
  · exact Or.inl

theorem glue_filled_shared {w : PR.V} {i : Fin nL} (hwi : partnerPos ℓR g w = some i)
    (k : ZMod 3) :
    (gluePiece ℓL ℓR g h).Filled (.inl (ℓL i).1, k) ↔
      PL.Filled ((ℓL i).1, k) ∨ PR.Filled (w, k - shift ℓL ℓR g w) := by
  rw [glue_filled_inl]
  constructor
  · rintro (hk | ⟨w', i', hi', hv, hk⟩)
    · exact Or.inl hk
    · have : i' = i := ℓL.injective (Subtype.ext hv)
      subst this
      rw [partnerPos_injective ℓR g hi' hwi] at hk
      exact Or.inr hk
  · rintro (hk | hk)
    · exact Or.inl hk
    · exact Or.inr ⟨w, i, hwi, rfl, hk⟩

/-- **The slots of a shared vertex.**  With `a` the left interface slot, the
right ends occupy `a + ε` (and `a + ε + 2` when the right vertex carries two
ends), where `ε` is `2` when the right vertex carries two ends or the left mark
is kept, and `1` otherwise. -/
theorem glue_filled_shared_iff {w : PR.V} {i : Fin nL} (hwi : partnerPos ℓR g w = some i)
    (k : ZMod 3) :
    (gluePiece ℓL ℓR g h).Filled (.inl (ℓL i).1, k) ↔
      (k = PL.ifaceSlot (ℓL i).1 ∨
        (PL.two (ℓL i).1 = true ∧ k = PL.ifaceSlot (ℓL i).1 + 2)) ∨
      (k = PL.ifaceSlot (ℓL i).1 +
          (if PR.two w = true ∨ Sum.inl i ∈ Set.range g.keep then 2 else 1) ∨
        (PR.two w = true ∧ k = PL.ifaceSlot (ℓL i).1 +
          (if PR.two w = true ∨ Sum.inl i ∈ Set.range g.keep then 2 else 1) + 2)) := by
  obtain ⟨hw, _⟩ := pair_inl_of_partner ℓL ℓR g h hwi
  rw [glue_filled_shared ℓL ℓR g h hwi, Piece.filled_iff (ℓL i).2, Piece.filled_iff hw,
    shift_of_some ℓL ℓR g hwi]
  set ε : ZMod 3 := if PR.two w = true ∨ Sum.inl i ∈ Set.range g.keep then 2 else 1
  set a := PL.ifaceSlot (ℓL i).1
  set c := PR.ifaceSlot w
  have e1 : k - (a - c + ε) = c ↔ k = a + ε := by
    constructor <;> intro hk
    · rw [sub_eq_iff_eq_add] at hk; rw [hk]; ring
    · rw [hk]; ring
  have e2 : k - (a - c + ε) = c + 2 ↔ k = a + ε + 2 := by
    constructor <;> intro hk
    · rw [sub_eq_iff_eq_add] at hk; rw [hk]; ring
    · rw [hk]; ring
  rw [e1, e2]

end Slots

namespace Piece

theorem ifaceSlot_eq {P : Piece} {v : P.V} {s : ZMod 3} (h1 : P.Filled (v, s))
    (h2 : ¬ P.Filled (v, s + 1)) : P.ifaceSlot v = s := by
  have hv : P.IsOpen v := ⟨s + 1, h2⟩
  rcases (filled_iff hv s).mp h1 with hs | ⟨_, hs⟩
  · exact hs.symm
  · exfalso
    apply h2
    rw [hs, add_assoc, show (2 : ZMod 3) + 1 = 0 by decide, add_zero]
    exact (ifaceSlot_spec hv).1

theorem two_congr {P Q : Piece} {v : P.V} {w : Q.V}
    (hPQ : ∀ k, P.Filled (v, k) ↔ Q.Filled (w, k)) : P.two v = Q.two w := by
  simp only [two, hPQ]

theorem two_of_consecutive {P : Piece} {v : P.V} {k : ZMod 3} (h1 : P.Filled (v, k))
    (h2 : P.Filled (v, k + 1)) : P.two v = true := by
  unfold two
  exact decide_eq_true ⟨k, h1, h2⟩

end Piece

/-! ## The parent's open vertices -/

section Parent

variable {PL PR : Piece} {nL nR nP : ℕ} (ℓL : Fin nL ≃ PL.OpenV) (ℓR : Fin nR ≃ PR.OpenV)
  (g : Glue nL nR nP) {L : Code nL} {R : Code nR} (h : GlueOK ℓL ℓR g L R)

/-- The vertex of a child mark in the glued piece. -/
def markVertex : Fin nL ⊕ Fin nR → GV PL ℓR g
  | .inl i => .inl (ℓL i).1
  | .inr j => vR ℓL ℓR g (ℓR j).1

/-- The slot of a child mark's interface end in the glued piece. -/
def markSlot : Fin nL ⊕ Fin nR → ZMod 3
  | .inl i => PL.ifaceSlot (ℓL i).1
  | .inr j => PR.ifaceSlot (ℓR j).1 + shift ℓL ℓR g (ℓR j).1

include h

theorem shared_left {i : Fin nL} {j : Fin nR} (hij : g.pair (.inl i) = .inr j) :
    partnerPos ℓR g (ℓR j).1 = some i :=
  (partnerPos_ℓR_eq_some_iff ℓR g j i).mpr (by rw [← hij, h.legal.pair_invol])

/-- **The kept marks.**  At a kept mark the glued vertex has its interface end in
the mark's slot, and it carries two ends exactly when the mark is shared or its
child vertex carries two. -/
theorem kept_facts {a : Fin nL ⊕ Fin nR} (ha : a ∈ Set.range g.keep) :
    (gluePiece ℓL ℓR g h).Filled (markVertex ℓL ℓR g a, markSlot ℓL ℓR g a) ∧
    ¬ (gluePiece ℓL ℓR g h).Filled (markVertex ℓL ℓR g a, markSlot ℓL ℓR g a + 1) ∧
    (gluePiece ℓL ℓR g h).two (markVertex ℓL ℓR g a) =
      (if g.pair a = a then twoOf L R a else true) := by
  have hne := zmod3_add_ne
  rcases a with i | j
  · rcases h.legal.pair_left i with hfix | ⟨j, hij⟩
    · have hsl := glue_filled_unshared ℓL ℓR g h hfix
      obtain ⟨h1, h2⟩ := Piece.ifaceSlot_spec (ℓL i).2
      simp only [markVertex, markSlot]
      refine ⟨(hsl _).mpr h1, fun hf => h2 ((hsl _).mp hf), ?_⟩
      rw [ite_eq_left hfix, Piece.two_congr hsl]
      exact (h.twoL i).symm
    · have hp := shared_left ℓL ℓR g h hij
      have hopen : OpenAt L R g (.inl i) := by
        by_contra hno
        exact h.legal.keep_closed (.inl i) (by rw [hij]; exact Sum.inr_ne_inl) hno ha
      have hL2 : PL.two (ℓL i).1 = false := by
        have := hopen.1; simp only [twoOf, h.twoL] at this; exact this
      have hR2 : PR.two (ℓR j).1 = false := by
        have := hopen.2; rw [hij] at this; simp only [twoOf, h.twoR] at this; exact this
      have hsl := glue_filled_shared_iff ℓL ℓR g h hp
      simp only [hL2, hR2, Bool.false_eq_true, false_and, or_false, false_or, ha,
        ↓reduceIte] at hsl
      set a := PL.ifaceSlot (ℓL i).1
      simp only [markVertex, markSlot]
      refine ⟨(hsl _).mpr (Or.inl rfl), ?_, ?_⟩
      · intro hf
        rcases (hsl _).mp hf with h1 | h1
        · exact (hne a).1 h1
        · exact (hne a).2.2 h1.symm
      · rw [ite_eq_right (by rw [hij]; exact Sum.inr_ne_inl)]
        exact Piece.two_of_consecutive ((hsl _).mpr (Or.inr rfl))
          ((hsl _).mpr (Or.inl (by rw [add_assoc, show (2 : ZMod 3) + 1 = 0 by decide,
            add_zero])))
  · rcases h.legal.pair_right j with hfix | ⟨i, hji⟩
    · have hnone := (partnerPos_ℓR_eq_none_iff ℓL ℓR g h j).mpr hfix
      have hsl := glue_filled_inr ℓL ℓR g h hnone
      obtain ⟨h1, h2⟩ := Piece.ifaceSlot_spec (ℓR j).2
      have hv : markVertex ℓL ℓR g (.inr j) = .inr ⟨(ℓR j).1, hnone⟩ := vR_of_none ℓL ℓR g hnone
      have hs : markSlot ℓL ℓR g (.inr j) = PR.ifaceSlot (ℓR j).1 := by
        simp only [markSlot, shift_of_none ℓL ℓR g hnone, add_zero]
      rw [hv, hs]
      refine ⟨(hsl _).mpr h1, fun hf => h2 ((hsl _).mp hf), ?_⟩
      rw [ite_eq_left hfix, Piece.two_congr hsl]
      exact (h.twoR j).symm
    · have hij : g.pair (.inl i) = .inr j := by rw [← hji, h.legal.pair_invol]
      have hp := shared_left ℓL ℓR g h hij
      have hopen : OpenAt L R g (.inr j) := by
        by_contra hno
        exact h.legal.keep_closed (.inr j) (by rw [hji]; exact Sum.inl_ne_inr) hno ha
      have hR2 : PR.two (ℓR j).1 = false := by
        have := hopen.1; simp only [twoOf, h.twoR] at this; exact this
      have hL2 : PL.two (ℓL i).1 = false := by
        have := hopen.2; rw [hji] at this; simp only [twoOf, h.twoL] at this; exact this
      have hnotL : Sum.inl i ∉ Set.range g.keep := by
        have := (h.legal.keep_open (.inr j) (by rw [hji]; exact Sum.inl_ne_inr) hopen).mp ha
        rwa [hji] at this
      have hsl := glue_filled_shared_iff ℓL ℓR g h hp
      simp only [hL2, hR2, Bool.false_eq_true, false_and, or_false, hnotL,
        ↓reduceIte] at hsl
      set a := PL.ifaceSlot (ℓL i).1
      have hv : markVertex ℓL ℓR g (.inr j) = .inl (ℓL i).1 := vR_of_some ℓL ℓR g hp
      have hs : markSlot ℓL ℓR g (.inr j) = a + 1 := by
        simp only [markSlot]
        rw [shift_of_some ℓL ℓR g hp, ite_eq_right (by simp [hR2, hnotL])]
        ring
      rw [hv, hs]
      refine ⟨(hsl _).mpr (Or.inr rfl), ?_, ?_⟩
      · intro hf
        rcases (hsl _).mp hf with h1 | h1
        · exact (hne a).2.1 (by rw [show a + 2 = a + 1 + 1 by ring]; exact h1)
        · exact (hne (a + 1)).1 h1
      · rw [ite_eq_right (by rw [hji]; exact Sum.inl_ne_inr)]
        exact Piece.two_of_consecutive ((hsl _).mpr (Or.inl rfl)) ((hsl _).mpr (Or.inr rfl))

theorem markVertex_isOpen {a : Fin nL ⊕ Fin nR} (ha : a ∈ Set.range g.keep) :
    (gluePiece ℓL ℓR g h).IsOpen (markVertex ℓL ℓR g a) :=
  ⟨_, (kept_facts ℓL ℓR g h ha).2.1⟩

theorem ifaceSlot_markVertex {a : Fin nL ⊕ Fin nR} (ha : a ∈ Set.range g.keep) :
    (gluePiece ℓL ℓR g h).ifaceSlot (markVertex ℓL ℓR g a) = markSlot ℓL ℓR g a :=
  Piece.ifaceSlot_eq (kept_facts ℓL ℓR g h ha).1 (kept_facts ℓL ℓR g h ha).2.1

/-- Two kept marks at one glued vertex are the same mark. -/
theorem markVertex_inj {a a' : Fin nL ⊕ Fin nR} (ha : a ∈ Set.range g.keep)
    (ha' : a' ∈ Set.range g.keep) (hv : markVertex ℓL ℓR g a = markVertex ℓL ℓR g a') :
    a = a' := by
  have both : ∀ i j, g.pair (.inl i) = .inr j → Sum.inl i ∈ Set.range g.keep →
      Sum.inr j ∈ Set.range g.keep → False := by
    intro i j hij hi hj
    by_cases hop : OpenAt L R g (.inl i)
    · have := (h.legal.keep_open (.inl i) (by rw [hij]; exact Sum.inr_ne_inl) hop).mp hi
      rw [hij] at this
      exact this hj
    · exact h.legal.keep_closed (.inl i) (by rw [hij]; exact Sum.inr_ne_inl) hop hi
  have mixed : ∀ i j, Sum.inl i ∈ Set.range g.keep → Sum.inr j ∈ Set.range g.keep →
      markVertex ℓL ℓR g (.inl i) = markVertex ℓL ℓR g (.inr j) → False := by
    intro i j hi hj hv
    simp only [markVertex] at hv
    by_cases hn : partnerPos ℓR g (ℓR j).1 = none
    · rw [vR_of_none ℓL ℓR g hn] at hv; exact Sum.inl_ne_inr hv
    · obtain ⟨i', hi'⟩ := Option.ne_none_iff_exists'.mp hn
      rw [vR_of_some ℓL ℓR g hi', Sum.inl.injEq] at hv
      have : i = i' := ℓL.injective (Subtype.ext hv)
      subst this
      have hji := (partnerPos_ℓR_eq_some_iff ℓR g j i).mp hi'
      exact both i j (by rw [← hji, h.legal.pair_invol]) hi hj
  rcases a with i | j <;> rcases a' with i' | j'
  · simp only [markVertex, Sum.inl.injEq] at hv
    rw [ℓL.injective (Subtype.ext hv)]
  · exact (mixed i j' ha ha' hv).elim
  · exact (mixed i' j ha' ha hv.symm).elim
  · simp only [markVertex] at hv
    rw [ℓR.injective (Subtype.ext (vR_injective ℓL ℓR g hv))]

/-- A shared vertex which closes has all three slots occupied. -/
theorem closed_shared_filled {i : Fin nL} {j : Fin nR} (hij : g.pair (.inl i) = .inr j)
    (hcl : ¬ OpenAt L R g (.inl i)) (k : ZMod 3) :
    (gluePiece ℓL ℓR g h).Filled (.inl (ℓL i).1, k) := by
  have hp := shared_left ℓL ℓR g h hij
  have hsl := glue_filled_shared_iff ℓL ℓR g h hp k
  have hnk : Sum.inl i ∉ Set.range g.keep :=
    h.legal.keep_closed (.inl i) (by rw [hij]; exact Sum.inr_ne_inl) hcl
  have htw : PL.two (ℓL i).1 = true ∨ PR.two (ℓR j).1 = true := by
    by_contra hn
    simp only [not_or, Bool.not_eq_true] at hn
    apply hcl
    refine ⟨?_, ?_⟩
    · simp only [twoOf, h.twoL]; simpa using hn.1
    · rw [hij]; simp only [twoOf, h.twoR]; simpa using hn.2
  rw [hsl]
  set a := PL.ifaceSlot (ℓL i).1
  rcases zmod3_cases (k - a) with hk | hk | hk
  · left; left; rw [sub_eq_zero] at hk; exact hk
  · rcases htw with hL | hR
    · have hR' : PR.two (ℓR j).1 = false := by
        have hdeg := h.legal.degree (.inl i) (by rw [hij]; exact Sum.inr_ne_inl)
        rw [hij] at hdeg
        simp only [twoOf, h.twoL, h.twoR, hL] at hdeg
        rcases hdeg with hd | hd
        · exact absurd hd (by decide)
        · exact hd
      right; left
      rw [ite_eq_right (by simp [hR', hnk])]
      rw [sub_eq_iff_eq_add] at hk; rw [hk]; ring
    · right; right
      refine ⟨hR, ?_⟩
      rw [ite_eq_left (Or.inl hR)]
      rw [sub_eq_iff_eq_add] at hk
      rw [hk, show a + 2 + 2 = a + 4 by ring, show (4 : ZMod 3) = 1 by decide]
      ring
  · rcases htw with hL | hR
    · left; right
      refine ⟨hL, ?_⟩
      rw [sub_eq_iff_eq_add] at hk; rw [hk]; ring
    · right; left
      rw [ite_eq_left (Or.inl hR)]
      rw [sub_eq_iff_eq_add] at hk; rw [hk]; ring

/-- Every open vertex of the glued piece is the vertex of a kept mark. -/
theorem exists_kept_of_isOpen (x : GV PL ℓR g) (hx : (gluePiece ℓL ℓR g h).IsOpen x) :
    ∃ k, markVertex ℓL ℓR g (g.keep k) = x := by
  obtain ⟨s, hs⟩ := hx
  rcases x with v | ⟨w, hw⟩
  · have hvo : PL.IsOpen v := ⟨s, fun hf => hs ((glue_filled_inl ℓL ℓR g h v s).mpr (Or.inl hf))⟩
    set i := ℓL.symm ⟨v, hvo⟩
    have hvi : (ℓL i).1 = v := by simp [i]
    rcases h.legal.pair_left i with hfix | ⟨j, hij⟩
    · obtain ⟨k, hk⟩ := h.legal.keep_fixed (.inl i) hfix
      exact ⟨k, by rw [hk]; simp [markVertex, hvi]⟩
    · by_cases hop : OpenAt L R g (.inl i)
      · by_cases hi : Sum.inl i ∈ Set.range g.keep
        · obtain ⟨k, hk⟩ := hi
          exact ⟨k, by rw [hk]; simp [markVertex, hvi]⟩
        · have hj := (h.legal.keep_open (.inl i) (by rw [hij]; exact Sum.inr_ne_inl) hop).not.mp
            (by simpa using hi)
          rw [hij] at hj
          obtain ⟨k, hk⟩ : Sum.inr j ∈ Set.range g.keep := by simpa using hj
          refine ⟨k, ?_⟩
          rw [hk]
          simp only [markVertex]
          rw [vR_of_some ℓL ℓR g (shared_left ℓL ℓR g h hij), hvi]
      · exact absurd (hvi ▸ closed_shared_filled ℓL ℓR g h hij hop s) hs
  · have hwo : PR.IsOpen w := ⟨s, fun hf => hs ((glue_filled_inr ℓL ℓR g h hw s).mpr hf)⟩
    set j := ℓR.symm ⟨w, hwo⟩
    have hwj : (ℓR j).1 = w := by simp [j]
    have hn : partnerPos ℓR g (ℓR j).1 = none := by rw [hwj]; exact hw
    have hfix := (partnerPos_ℓR_eq_none_iff ℓL ℓR g h j).mp hn
    obtain ⟨k, hk⟩ := h.legal.keep_fixed (.inr j) hfix
    refine ⟨k, ?_⟩
    rw [hk]
    simp only [markVertex]
    rw [vR_of_none ℓL ℓR g hn]
    simp [hwj]

/-- **The parent's open vertices, named by the kept marks.** -/
def parentLabel : Fin nP ≃ (gluePiece ℓL ℓR g h).OpenV :=
  Equiv.ofBijective
    (fun k => ⟨markVertex ℓL ℓR g (g.keep k), markVertex_isOpen ℓL ℓR g h ⟨k, rfl⟩⟩)
    ⟨fun k k' hk => g.keep.injective (markVertex_inj ℓL ℓR g h ⟨k, rfl⟩ ⟨k', rfl⟩
        (congrArg Subtype.val hk)),
      fun x => by
        obtain ⟨k, hk⟩ := exists_kept_of_isOpen ℓL ℓR g h x.1 x.2
        exact ⟨k, Subtype.ext hk⟩⟩

theorem parentLabel_apply (k : Fin nP) :
    (parentLabel ℓL ℓR g h k).1 = markVertex ℓL ℓR g (g.keep k) := rfl

/-- **The `two` field of the glued piece is the fork's.** -/
theorem parent_two (k : Fin nP) :
    (fork L R g).two k = (gluePiece ℓL ℓR g h).two (parentLabel ℓL ℓR g h k).1 := by
  rw [parentLabel_apply, (kept_facts ℓL ℓR g h ⟨k, rfl⟩).2.2]
  rfl

end Parent

/-! ## The children inside an embedded glued piece -/

theorem Emb.alpha_faceLabel {V' E' : Type*} [Fintype V'] [DecidableEq V'] [Fintype E']
    [DecidableEq E'] {P : Piece} {RS : RotationSystem V' E'} (emb : Emb P RS) (hC : Cubic3 RS)
    {n : ℕ} (ℓ : Fin n ≃ P.OpenV) (i : Fin n) :
    RS.alpha (faceLabel hC emb.shore (emb.label hC ℓ) i).1 =
      emb.smap ((ℓ i).1, P.ifaceSlot (ℓ i).1) := by
  obtain ⟨k, hk, h1, h2⟩ := emb.iface_slot hC ℓ i
  rw [hk, Piece.ifaceSlot_eq h1 h2]

section Embed

variable {PL PR : Piece} {nL nR nP : ℕ} (ℓL : Fin nL ≃ PL.OpenV) (ℓR : Fin nR ≃ PR.OpenV)
  (g : Glue nL nR nP) {L : Code nL} {R : Code nR} (h : GlueOK ℓL ℓR g L R)
  {V' E' : Type*} [Fintype V'] [DecidableEq V'] [Fintype E'] [DecidableEq E']
  {RS : RotationSystem V' E'} (emb : Emb (gluePiece ℓL ℓR g h) RS)

/-- The left piece inside an embedded glued piece. -/
def leftEmb : Emb PL RS where
  vmap v := emb.vmap (.inl v)
  vmap_injective := fun _ _ hab => Sum.inl_injective (emb.vmap_injective hab)
  emap e := emb.emap (.inl e)
  emap_injective := fun _ _ hab => Sum.inl_injective (emb.emap_injective hab)
  smap s := emb.smap (.inl s.1, s.2)
  vertOf_smap s := emb.vertOf_smap _
  rho_smap v k := emb.rho_smap _ _
  edgeOf_place x := emb.edgeOf_place (.inl x.1, x.2)
  alpha_place e b := emb.alpha_place (.inl e) b
  open_not_shore := by
    rintro ⟨v, k⟩ hs ⟨e, he⟩
    by_cases hf : (gluePiece ℓL ℓR g h).Filled (.inl v, k)
    · obtain ⟨⟨e' | e', b'⟩, hy⟩ := hf
      · apply hs
        simp only [gluePiece, gluePlace, Prod.mk.injEq, Sum.inl.injEq] at hy
        exact ⟨(e', b'), Prod.ext hy.1 hy.2⟩
      · have := emb.edgeOf_place (.inr e', b')
        rw [hy] at this
        rw [this] at he
        exact Sum.inl_ne_inr (emb.emap_injective he)
    · exact emb.open_not_shore _ hf ⟨.inl e, he⟩

/-- The right piece inside an embedded glued piece. -/
def rightEmb : Emb PR RS where
  vmap w := emb.vmap (vR ℓL ℓR g w)
  vmap_injective := fun _ _ hab => vR_injective ℓL ℓR g (emb.vmap_injective hab)
  emap e := emb.emap (.inr e)
  emap_injective := fun _ _ hab => Sum.inr_injective (emb.emap_injective hab)
  smap s := emb.smap (vR ℓL ℓR g s.1, s.2 + shift ℓL ℓR g s.1)
  vertOf_smap s := emb.vertOf_smap _
  rho_smap w k := by
    rw [emb.rho_smap]
    congr 2
    ring
  edgeOf_place x := emb.edgeOf_place (.inr x.1, x.2)
  alpha_place e b := emb.alpha_place (.inr e) b
  open_not_shore := by
    rintro ⟨w, k⟩ hs ⟨e, he⟩
    by_cases hf : (gluePiece ℓL ℓR g h).Filled (vR ℓL ℓR g w, k + shift ℓL ℓR g w)
    · obtain ⟨⟨e' | e', b'⟩, hy⟩ := hf
      · have := emb.edgeOf_place (.inl e', b')
        rw [hy] at this
        rw [this] at he
        exact Sum.inr_ne_inl (emb.emap_injective he)
      · apply hs
        simp only [gluePiece, gluePlace, Prod.mk.injEq] at hy
        obtain ⟨hv, hk⟩ := hy
        have hw := vR_injective ℓL ℓR g hv
        rw [hw] at hk
        exact ⟨(e', b'), Prod.ext hw (add_right_cancel hk)⟩
    · exact emb.open_not_shore _ hf ⟨.inr e, he⟩

theorem shore_union :
    (leftEmb ℓL ℓR g h emb).shore ∪ (rightEmb ℓL ℓR g h emb).shore = emb.shore := by
  ext e
  simp only [Finset.mem_union, Emb.mem_shore, Set.mem_range]
  constructor
  · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨.inl a, rfl⟩
    · exact ⟨.inr a, rfl⟩
  · rintro ⟨a | a, rfl⟩
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨a, rfl⟩

theorem shores_disjoint :
    Disjoint (leftEmb ℓL ℓR g h emb).shore (rightEmb ℓL ℓR g h emb).shore := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨a, rfl⟩ := (Emb.mem_shore _).mp he
  obtain ⟨b, hb⟩ := (Emb.mem_shore _).mp he'
  exact Sum.inr_ne_inl (emb.emap_injective hb)

end Embed

/-! ## The slot after a mark -/

section Next

variable {PL PR : Piece} {nL nR nP : ℕ} (ℓL : Fin nL ≃ PL.OpenV) (ℓR : Fin nR ≃ PR.OpenV)
  (g : Glue nL nR nP) {L : Code nL} {R : Code nR} (h : GlueOK ℓL ℓR g L R)

include h

theorem openAt_pair_iff (x : Fin nL ⊕ Fin nR) :
    OpenAt L R g (g.pair x) ↔ OpenAt L R g x := by
  simp only [OpenAt, h.legal.pair_invol]
  tauto

/-- **A mark is kept exactly when the slot after its end stays open.** -/
theorem not_filled_next_iff (a : Fin nL ⊕ Fin nR) :
    ¬ (gluePiece ℓL ℓR g h).Filled (markVertex ℓL ℓR g a, markSlot ℓL ℓR g a + 1) ↔
      a ∈ Set.range g.keep := by
  refine ⟨fun hn => ?_, fun ha => (kept_facts ℓL ℓR g h ha).2.1⟩
  by_contra ha
  apply hn
  rcases a with i | j
  · rcases h.legal.pair_left i with hfix | ⟨j, hij⟩
    · exact absurd (h.legal.keep_fixed (.inl i) hfix) ha
    · by_cases hop : OpenAt L R g (.inl i)
      · have hp := shared_left ℓL ℓR g h hij
        have hL2 : PL.two (ℓL i).1 = false := by
          have := hop.1; simp only [twoOf, h.twoL] at this; exact this
        have hR2 : PR.two (ℓR j).1 = false := by
          have := hop.2; rw [hij] at this; simp only [twoOf, h.twoR] at this; exact this
        have hsl := glue_filled_shared_iff ℓL ℓR g h hp
        simp only [hL2, hR2, Bool.false_eq_true, false_and, or_false, ha, ↓reduceIte] at hsl
        simp only [markVertex, markSlot]
        exact (hsl _).mpr (Or.inr rfl)
      · exact closed_shared_filled ℓL ℓR g h hij hop _
  · rcases h.legal.pair_right j with hfix | ⟨i, hji⟩
    · exact absurd (h.legal.keep_fixed (.inr j) hfix) ha
    · have hij : g.pair (.inl i) = .inr j := by rw [← hji, h.legal.pair_invol]
      have hp := shared_left ℓL ℓR g h hij
      have hv : markVertex ℓL ℓR g (.inr j) = .inl (ℓL i).1 := vR_of_some ℓL ℓR g hp
      rw [hv]
      by_cases hop : OpenAt L R g (.inl i)
      · have hL2 : PL.two (ℓL i).1 = false := by
          have := hop.1; simp only [twoOf, h.twoL] at this; exact this
        have hR2 : PR.two (ℓR j).1 = false := by
          have := hop.2; rw [hij] at this; simp only [twoOf, h.twoR] at this; exact this
        have hkeepL : Sum.inl i ∈ Set.range g.keep := by
          by_contra hl
          have := (h.legal.keep_open (.inl i) (by rw [hij]; exact Sum.inr_ne_inl) hop).not.mp hl
          rw [hij, not_not] at this
          exact ha this
        have hsl := glue_filled_shared_iff ℓL ℓR g h hp
        simp only [hL2, hR2, Bool.false_eq_true, false_and, or_false, hkeepL, ↓reduceIte,
          false_or] at hsl
        have hs : markSlot ℓL ℓR g (.inr j) = PL.ifaceSlot (ℓL i).1 + 2 := by
          simp only [markSlot]
          rw [shift_of_some ℓL ℓR g hp, ite_eq_left (Or.inr hkeepL)]
          ring
        rw [hs, add_assoc, show (2 : ZMod 3) + 1 = 0 by decide, add_zero]
        exact (hsl _).mpr (Or.inl rfl)
      · exact closed_shared_filled ℓL ℓR g h hij hop _

end Next

/-! ## The physical descriptor of an embedded glued piece -/

section Descriptor

variable {PL PR : Piece} {nL nR nP : ℕ} (ℓL : Fin nL ≃ PL.OpenV) (ℓR : Fin nR ≃ PR.OpenV)
  (g : Glue nL nR nP) {L : Code nL} {R : Code nR} (h : GlueOK ℓL ℓR g L R)
  {V' E' : Type*} [Fintype V'] [DecidableEq V'] [Fintype E'] [DecidableEq E']
  {RS : RotationSystem V' E'} (emb : Emb (gluePiece ℓL ℓR g h) RS) (hC : Cubic3 RS)

theorem leftEmb_label_apply (i : Fin nL) :
    ((leftEmb ℓL ℓR g h emb).label hC ℓL i).1 = emb.vmap (markVertex ℓL ℓR g (.inl i)) := rfl

theorem rightEmb_label_apply (j : Fin nR) :
    ((rightEmb ℓL ℓR g h emb).label hC ℓR j).1 = emb.vmap (markVertex ℓL ℓR g (.inr j)) := rfl

/-- **The pairing read off the map is the descriptor's.** -/
theorem physPair_glue :
    physPair ((leftEmb ℓL ℓR g h emb).label hC ℓL) ((rightEmb ℓL ℓR g h emb).label hC ℓR) =
      g.pair := by
  have hmidR : ∀ x : V', x ∈ mid RS.endpoints (rightEmb ℓL ℓR g h emb).shore ↔
      ∃ w, PR.IsOpen w ∧ emb.vmap (vR ℓL ℓR g w) = x :=
    fun x => (rightEmb ℓL ℓR g h emb).mem_mid_iff hC x
  have hmidL : ∀ x : V', x ∈ mid RS.endpoints (leftEmb ℓL ℓR g h emb).shore ↔
      ∃ v, PL.IsOpen v ∧ emb.vmap (.inl v) = x :=
    fun x => (leftEmb ℓL ℓR g h emb).mem_mid_iff hC x
  apply Equiv.ext
  rintro (i | j)
  · rcases h.legal.pair_left i with hfix | ⟨j, hij⟩
    · rw [hfix, physPair_inl_of_not_mem]
      intro hmem
      obtain ⟨w, _, hwv⟩ := (hmidR _).mp hmem
      rw [leftEmb_label_apply] at hwv
      have hv := emb.vmap_injective hwv
      by_cases hn : partnerPos ℓR g w = none
      · rw [vR_of_none ℓL ℓR g hn] at hv; exact Sum.inr_ne_inl hv
      · obtain ⟨i', hi'⟩ := Option.ne_none_iff_exists'.mp hn
        rw [vR_of_some ℓL ℓR g hi'] at hv
        simp only [markVertex, Sum.inl.injEq] at hv
        have : i' = i := ℓL.injective (Subtype.ext hv)
        subst this
        exact no_partner_of_fixed ℓL ℓR g h hfix w hi'
    · have hp := shared_left ℓL ℓR g h hij
      have hvj : emb.vmap (vR ℓL ℓR g (ℓR j).1) = emb.vmap (.inl (ℓL i).1) := by
        rw [vR_of_some ℓL ℓR g hp]
      have hmem : ((leftEmb ℓL ℓR g h emb).label hC ℓL i).1 ∈
          mid RS.endpoints (rightEmb ℓL ℓR g h emb).shore :=
        (hmidR _).mpr ⟨(ℓR j).1, (ℓR j).2, hvj⟩
      rw [physPair_inl_of_mem _ _ hmem, hij, Sum.inr.injEq, Equiv.symm_apply_eq]
      apply Subtype.ext
      rw [rightEmb_label_apply]
      exact hvj.symm
  · rcases h.legal.pair_right j with hfix | ⟨i, hji⟩
    · rw [hfix, physPair_inr_of_not_mem]
      intro hmem
      obtain ⟨v, _, hvv⟩ := (hmidL _).mp hmem
      rw [rightEmb_label_apply] at hvv
      have hv := emb.vmap_injective hvv
      have hn := (partnerPos_ℓR_eq_none_iff ℓL ℓR g h j).mpr hfix
      simp only [markVertex] at hv
      rw [vR_of_none ℓL ℓR g hn] at hv
      exact Sum.inl_ne_inr hv
    · have hij : g.pair (.inl i) = .inr j := by rw [← hji, h.legal.pair_invol]
      have hp := shared_left ℓL ℓR g h hij
      have hvj : emb.vmap (.inl (ℓL i).1) = emb.vmap (vR ℓL ℓR g (ℓR j).1) := by
        rw [vR_of_some ℓL ℓR g hp]
      have hmem : ((rightEmb ℓL ℓR g h emb).label hC ℓR j).1 ∈
          mid RS.endpoints (leftEmb ℓL ℓR g h emb).shore :=
        (hmidL _).mpr ⟨(ℓL i).1, (ℓL i).2, hvj⟩
      rw [physPair_inr_of_mem _ _ hmem, hji, Sum.inl.injEq, Equiv.symm_apply_eq]
      apply Subtype.ext
      rw [leftEmb_label_apply]
      exact hvj.symm

/-- The child end of a mark, read as a slot of the glued piece. -/
theorem alpha_toMarked (a : Fin nL ⊕ Fin nR) :
    RS.alpha (toMarked hC (shores_disjoint ℓL ℓR g h emb) ((leftEmb ℓL ℓR g h emb).label hC ℓL)
        ((rightEmb ℓL ℓR g h emb).label hC ℓR) a).1.1 =
      emb.smap (markVertex ℓL ℓR g a, markSlot ℓL ℓR g a) := by
  rcases a with i | j
  · rw [toMarked_inl, Emb.alpha_faceLabel]
    rfl
  · rw [toMarked_inr, Emb.alpha_faceLabel]
    rfl

/-- **The kept marks read off the map are the descriptor's.** -/
theorem physKeep_glue
    (ℓP : Fin nP ≃ MidVertex RS ((leftEmb ℓL ℓR g h emb).shore ∪ (rightEmb ℓL ℓR g h emb).shore))
    (hℓ : ∀ k, (ℓP k).1 = emb.vmap (markVertex ℓL ℓR g (g.keep k))) :
    physKeep hC (shores_disjoint ℓL ℓR g h emb) ((leftEmb ℓL ℓR g h emb).label hC ℓL)
      ((rightEmb ℓL ℓR g h emb).label hC ℓR) ℓP = g.keep := by
  set hdisj := shores_disjoint ℓL ℓR g h emb
  set ℓS := (leftEmb ℓL ℓR g h emb).label hC ℓL
  set ℓT := (rightEmb ℓL ℓR g h emb).label hC ℓR
  have hU := shore_union ℓL ℓR g h emb
  have hrange : ∀ a, a ∈ Set.range (physKeep hC hdisj ℓS ℓT ℓP) ↔ a ∈ Set.range g.keep := by
    intro a
    rw [mem_range_physKeep, forkKeep_toMarked_iff, alpha_toMarked, emb.rho_smap, hU,
      emb.inShore_smap_iff hC]
    exact not_filled_next_iff ℓL ℓR g h a
  apply DFunLike.ext
  intro k
  set a := physKeep hC hdisj ℓS ℓT ℓP k
  have ha : a ∈ Set.range g.keep := (hrange a).mp ⟨k, rfl⟩
  apply markVertex_inj ℓL ℓR g h ha ⟨k, rfl⟩
  apply emb.vmap_injective
  have hdart : (toMarked hC hdisj ℓS ℓT a).1.1 = (faceLabel hC _ ℓP k).1 := by
    have := toMarked_keepFun hC hdisj ℓS ℓT ℓP k
    exact congrArg (fun y => y.1.1) this
  have h1 := congrArg RS.vertOf (alpha_toMarked ℓL ℓR g h emb hC a)
  rw [emb.vertOf_smap, hdart, vertOf_alpha_faceLabel] at h1
  rw [← h1, hℓ]

/-- **The descriptor read off the map is the descriptor glued along.** -/
theorem physGlue_glue
    (ℓP : Fin nP ≃ MidVertex RS ((leftEmb ℓL ℓR g h emb).shore ∪ (rightEmb ℓL ℓR g h emb).shore))
    (hℓ : ∀ k, (ℓP k).1 = emb.vmap (markVertex ℓL ℓR g (g.keep k))) :
    physGlue hC (shores_disjoint ℓL ℓR g h emb) ((leftEmb ℓL ℓR g h emb).label hC ℓL)
      ((rightEmb ℓL ℓR g h emb).label hC ℓR) ℓP = g := by
  have hp := physPair_glue ℓL ℓR g h emb hC
  have hk := physKeep_glue ℓL ℓR g h emb hC ℓP hℓ
  unfold physGlue
  rw [hp, hk]

end Descriptor

/-! ## Realization of the closure -/

section Realize

variable {V' E' : Type*} [Fintype V'] [DecidableEq V'] [Fintype E'] [DecidableEq E']

theorem encode_congr {RS : RotationSystem V' E'} (hC : Cubic3 RS) {X Y : Finset E'}
    (hXY : X = Y) {n : ℕ} (ℓX : Fin n ≃ MidVertex RS X) (ℓY : Fin n ≃ MidVertex RS Y)
    (hℓ : ∀ k, (ℓX k).1 = (ℓY k).1) : encode hC X ℓX = encode hC Y ℓY := by
  subst hXY
  have : ℓX = ℓY := Equiv.ext fun k => Subtype.ext (hℓ k)
  rw [this]

theorem shoreConnected_union {RS : RotationSystem V' E'} {S T : Finset E'}
    (hS : ShoreConnected RS S) (hT : ShoreConnected RS T) {x : V'} (hxS : x ∈ touched RS S)
    (hxT : x ∈ touched RS T) : ShoreConnected RS (S ∪ T) := by
  have hleS : shoreGraph RS S ≤ shoreGraph RS (S ∪ T) := by
    rintro u v ⟨d, hd, hu, hv⟩
    exact ⟨d, Finset.mem_union_left _ hd, hu, hv⟩
  have hleT : shoreGraph RS T ≤ shoreGraph RS (S ∪ T) := by
    rintro u v ⟨d, hd, hu, hv⟩
    exact ⟨d, Finset.mem_union_right _ hd, hu, hv⟩
  have hto : ∀ u, u ∈ touched RS (S ∪ T) → (shoreGraph RS (S ∪ T)).Reachable u x := by
    intro u hu
    rw [touched_union, Finset.mem_union] at hu
    rcases hu with hu | hu
    · exact (hS u x hu hxS).mono hleS
    · exact (hT u x hu hxT).mono hleT
  intro u v hu hv
  exact (hto u hu).trans (hto v hv).symm

/-- **Euler's formula passes to a planar fork.**  The children's formulas and the
guard of the code give the parent's. -/
theorem euler_parent {RS : RotationSystem V' E'} (hC : Cubic3 RS) {S T : Finset E'}
    (hdisj : Disjoint S T) {nL nR nP : ℕ} (ℓS : Fin nL ≃ MidVertex RS S)
    (ℓT : Fin nR ≃ MidVertex RS T) (ℓP : Fin nP ≃ MidVertex RS (S ∪ T))
    (L : Code nL) (R : Code nR) (hL : L.ret = codeRet hC S ℓS) (hR : R.ret = codeRet hC T ℓT)
    (hES : (touched RS S).card +
        (shoreFace RS.rho RS.alpha RS.edgeOf RS.edge_alpha S).partition.parts.card = 2 + S.card)
    (hET : (touched RS T).card +
        (shoreFace RS.rho RS.alpha RS.edgeOf RS.edge_alpha T).partition.parts.card = 2 + T.card)
    (he : Euler L R (physGlue hC hdisj ℓS ℓT ℓP)) :
    (touched RS (S ∪ T)).card +
        (shoreFace RS.rho RS.alpha RS.edgeOf RS.edge_alpha (S ∪ T)).partition.parts.card =
      2 + (S ∪ T).card := by
  unfold PhysicalForkCode.Euler PhysicalForkCode.cyc at he
  rw [sharedCount_physGlue] at he
  have hLc : L.ret.partition.parts.card =
      (nodeRet RS.rho RS.alpha RS.edgeOf RS.edge_alpha S).partition.parts.card := by
    rw [hL, codeRet, GoertzelV24RetainedSpliceFaceCount.card_permCongr_partition_parts]
  have hRc : R.ret.partition.parts.card =
      (nodeRet RS.rho RS.alpha RS.edgeOf RS.edge_alpha T).partition.parts.card := by
    rw [hR, codeRet, GoertzelV24RetainedSpliceFaceCount.card_permCongr_partition_parts]
  have hstep : (PhysicalForkCode.merged L R * (physGlue hC hdisj ℓS ℓT ℓP).pair).partition.parts.card =
      (mergeRet RS.rho RS.alpha RS.edgeOf S T hdisj
          (nodeRet RS.rho RS.alpha RS.edgeOf RS.edge_alpha S)
          (nodeRet RS.rho RS.alpha RS.edgeOf RS.edge_alpha T) *
        forkRewire RS.rho RS.alpha RS.edgeOf RS.edge_alpha S T hdisj).partition.parts.card := by
    rw [← toMarked_step hC hdisj ℓS ℓT L R hL hR,
      GoertzelV24RetainedSpliceFaceCount.card_permCongr_partition_parts]
    rfl
  have hfaces := forkStep_faces RS.rho RS.alpha RS.edgeOf RS.edge_alpha S T hdisj
  rw [forkStep_eq, nodeState_faces, nodeState_faces, nodeState_faces, mergeRet_card] at hfaces
  have hunion := Finset.card_union_add_card_inter (touched RS S) (touched RS T)
  rw [← touched_union] at hunion
  have hST := Finset.card_union_of_disjoint hdisj
  rw [hLc, hRc, hstep] at he
  omega

/-- **A planar fork of realized codes is realized by the glued piece.** -/
theorem realizes_fork {PL PR : Piece} {nL nR nP : ℕ} {ℓL : Fin nL ≃ PL.OpenV}
    {ℓR : Fin nR ≃ PR.OpenV} {L : Code nL} {R : Code nR} (hL : Realizes PL ℓL L)
    (hR : Realizes PR ℓR R) (g : Glue nL nR nP) (hg : Legal L R g) (he : Euler L R g) :
    Realizes (gluePiece ℓL ℓR g ⟨hg, hL.two, hR.two⟩)
      (parentLabel ℓL ℓR g ⟨hg, hL.two, hR.two⟩) (fork L R g) where
  two k := parent_two ℓL ℓR g ⟨hg, hL.two, hR.two⟩ k
  shore := by
    intro V' E' _ _ _ _ RS hC hcubic emb
    have h : GlueOK ℓL ℓR g L R := ⟨hg, hL.two, hR.two⟩
    obtain ⟨hcL, hconnL, heulL⟩ := hL.shore RS hC hcubic (leftEmb ℓL ℓR g h emb)
    obtain ⟨hcR, hconnR, heulR⟩ := hR.shore RS hC hcubic (rightEmb ℓL ℓR g h emb)
    have hU := shore_union ℓL ℓR g h emb
    have hdisj := shores_disjoint ℓL ℓR g h emb
    let ℓP' : Fin nP ≃ MidVertex RS
        ((leftEmb ℓL ℓR g h emb).shore ∪ (rightEmb ℓL ℓR g h emb).shore) :=
      (emb.label hC (parentLabel ℓL ℓR g h)).trans
        (Equiv.subtypeEquivRight (fun x => by rw [hU]))
    have hℓ : ∀ k, (ℓP' k).1 = emb.vmap (markVertex ℓL ℓR g (g.keep k)) := by
      intro k
      simp only [ℓP', Equiv.trans_apply, Equiv.subtypeEquivRight_apply_coe, Emb.label_apply,
        parentLabel_apply]
    have hphys := physGlue_glue ℓL ℓR g h emb hC ℓP' hℓ
    have hfork := encode_fork hC hcubic hdisj ((leftEmb ℓL ℓR g h emb).label hC ℓL)
      ((rightEmb ℓL ℓR g h emb).label hC ℓR) ℓP'
    rw [hphys, hcL, hcR] at hfork
    refine ⟨?_, ?_, ?_⟩
    · rw [← hfork]
      exact encode_congr hC hU.symm _ _ (fun k => by rw [Emb.label_apply, parentLabel_apply, hℓ])
    · rw [← hU]
      obtain ⟨x, hx⟩ := hg.shared
      obtain ⟨i, j, hij⟩ : ∃ i j, g.pair (.inl i) = .inr j := by
        rcases x with i | j
        · rcases hg.pair_left i with h1 | ⟨j, h1⟩
          · exact absurd h1 hx
          · exact ⟨i, j, h1⟩
        · rcases hg.pair_right j with h1 | ⟨i, h1⟩
          · exact absurd h1 hx
          · exact ⟨i, j, by rw [← h1, hg.pair_invol]⟩
      have hp := shared_left ℓL ℓR g h hij
      refine shoreConnected_union hconnL hconnR
        ((leftEmb ℓL ℓR g h emb).mem_touched_iff hC _ |>.mpr ⟨(ℓL i).1, rfl⟩)
        ((rightEmb ℓL ℓR g h emb).mem_touched_iff hC _ |>.mpr ⟨(ℓR j).1, ?_⟩)
      change emb.vmap (vR ℓL ℓR g (ℓR j).1) = emb.vmap (.inl (ℓL i).1)
      rw [vR_of_some ℓL ℓR g hp]
    · rw [← hU]
      refine euler_parent hC hdisj _ _ ℓP' L R ?_ ?_ heulL heulR (by rw [hphys]; exact he)
      · exact (congrArg PhysicalForkCode.Code.ret hcL).symm
      · exact (congrArg PhysicalForkCode.Code.ret hcR).symm

/-- **Soundness of the closure.**  Every code of the closure is realized by an
open piece: in every cubic map in which the piece is embedded, its shore has
the code, is connected, and satisfies Euler's formula for the sphere. -/
theorem reach_realized {bound n : ℕ} {c : Code n} (hc : Reach bound n c) :
    ∃ (P : Piece) (ℓ : Fin n ≃ P.OpenV), Realizes P ℓ c ∧ Nonempty P.E := by
  induction hc with
  | leaf => exact ⟨leafPiece, leafLabel, leafPiece_realizes, ⟨()⟩⟩
  | @fork nL nR nP L R g _ _ hlegal heuler _ ihL ihR =>
      obtain ⟨PL, ℓL, hL, ⟨e⟩⟩ := ihL
      obtain ⟨PR, ℓR, hR, _⟩ := ihR
      exact ⟨_, _, realizes_fork hL hR g hlegal heuler, ⟨.inl e⟩⟩

end Realize

end

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodePiece
