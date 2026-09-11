import Mettapedia.GraphTheory.FourColor.PhysicalContextBits
import Mettapedia.GraphTheory.FourColor.GoertzelV24CompositeSeamCubic

/-!
# Exponentially many literal physical right languages

Disjoint union of the four-port bit pieces has `4*n` ports. The context
which tests just block `i` accepts precisely bit `i`. Consequently any
exact deterministic code for these literal sewn-map colourability tests
has at least `2^n` states. Rejecting contexts contain bridges; restriction
to bridgeless closures is a separate, target-facing problem.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalContextBits

open GoertzelV24OpenTangleComposition GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PhysicalClosedCountBridge GoertzelV24ClosedCountReplacement
open GoertzelV24PhysicalRightLanguageBoundary
open GoertzelV24CompositeSeamCubic

section Reindex
universe u
variable {V I P Q : Type u}

def reindex (T : PortTangle V I P) (e : Q ≃ P) : PortTangle V I Q where
  vert := T.vert ∘ Sum.map id e
  alpha := T.alpha
  alpha_involutive := T.alpha_involutive
  alpha_fixfree := T.alpha_fixfree
  no_self_loops := T.no_self_loops

theorem reindex_col_iff (T : PortTangle V I P) (e : Q ≃ P) (w : P → Color) :
    Nonempty (Col (reindex T e) (w ∘ e)) ↔ Nonempty (Col T w) := by
  let E := Equiv.sumCongr (Equiv.refl I) e
  constructor
  · rintro ⟨⟨c, hp, hw⟩⟩
    let c' : Coloring T :=
      ⟨fun d => c.color (E.symm d), fun d => c.invariant d⟩
    refine ⟨⟨c', ⟨fun d => hp.1 _, ?_⟩, ?_⟩⟩
    · intro d f hv hne
      apply hp.2 (E.symm d) (E.symm f)
      · simpa [reindex, E] using hv
      · exact E.symm.injective.ne hne
    · funext p
      have h := congrFun hw (e.symm p)
      simpa [word, c', E, Function.comp_def] using h
  · rintro ⟨⟨c, hp, hw⟩⟩
    let c' : Coloring (reindex T e) :=
      ⟨fun d => c.color (E d), fun d => c.invariant d⟩
    refine ⟨⟨c', ⟨fun d => hp.1 _, ?_⟩, ?_⟩⟩
    · intro d f hv hne
      exact hp.2 (E d) (E f) hv (E.injective.ne hne)
    · funext p
      exact congrFun hw (e p)

def dropLeft (P : Type u) : (EmptyPort.{u} ⊕ P) ≃ P where
  toFun := Sum.elim PEmpty.elim id
  invFun := Sum.inr
  left_inv := by rintro (e | p); exact e.elim; rfl
  right_inv := fun _ => rfl

def dropRight (P : Type u) : (P ⊕ EmptyPort.{u}) ≃ P where
  toFun := Sum.elim id PEmpty.elim
  invFun := Sum.inl
  left_inv := by rintro (p | e); rfl; exact e.elim
  right_inv := fun _ => rfl

def Realizes (T : OpenTangleData V I P) (w : P → Color) : Prop :=
  Nonempty (Col (ofOpenTangleData T) w)

/-- Reflect the exterior disc. Colouring semantics is unchanged. -/
def reverseData (T : OpenTangleData V I P) : OpenTangleData V I P :=
  { T with
    rho := T.rho.symm
    vert_rho := by
      intro d
      simpa only [Equiv.apply_symm_apply] using (T.vert_rho (T.rho.symm d)).symm }

@[simp] theorem realizes_reverse (T : OpenTangleData V I P) (w : P → Color) :
    Realizes (reverseData T) w ↔ Realizes T w := Iff.rfl

theorem left_realizes (T : OpenTangleData V I P) (w : P → Color) :
    w ∈ outerSupport (leftClosedPortTangle T) ↔ Realizes T w := by
  have ht : reindex (ofOpenTangleData T) (dropLeft P) = leftClosedPortTangle T := by
    unfold reindex ofOpenTangleData leftClosedPortTangle
    congr 1
    funext d
    rcases d with d | (e | p)
    · rfl
    · exact e.elim
    · rfl
  have hw : w ∘ dropLeft P = Sum.elim PEmpty.elim w := by
    funext p; rcases p with e | p; exact e.elim; rfl
  have h := reindex_col_iff (ofOpenTangleData T) (dropLeft P) w
  rw [ht, hw] at h
  exact h

theorem right_realizes (T : OpenTangleData V I P) (w : P → Color) :
    w ∈ innerSupport (rightClosedPortTangle T (Equiv.refl P)) ↔ Realizes T w := by
  have ht : reindex (ofOpenTangleData T) (dropRight P) =
      rightClosedPortTangle T (Equiv.refl P) := by
    unfold reindex ofOpenTangleData rightClosedPortTangle
    congr 1
    funext d
    rcases d with d | (p | e)
    · rfl
    · rfl
    · exact e.elim
  have hw : w ∘ dropRight P = Sum.elim w PEmpty.elim := by
    funext p; rcases p with p | e; rfl; exact e.elim
  have h := reindex_col_iff (ofOpenTangleData T) (dropRight P) w
  rw [ht, hw] at h
  exact h

end Reindex

variable {n : Nat}

abbrev BI (n : Nat) := Fin n × I
abbrev BP (n : Nat) := Fin n × Fin 4
abbrev BD (n : Nat) := BI n ⊕ BP n

def bundle : BD n ≃ Fin n × D where
  toFun
    | .inl (i, d) => (i, .inl d)
    | .inr (i, p) => (i, .inr p)
  invFun
    | (i, .inl d) => .inl (i, d)
    | (i, .inr p) => .inr (i, p)
  left_inv := by rintro (⟨i,d⟩ | ⟨i,p⟩) <;> rfl
  right_inv := by rintro ⟨i,d | p⟩ <;> rfl

def blockPerm (ts : Fin n → Kind) : Equiv.Perm (Fin n × D) where
  toFun := fun ⟨i,d⟩ => (i, (localData (ts i)).rho d)
  invFun := fun ⟨i,d⟩ => (i, (localData (ts i)).rho.symm d)
  left_inv := by rintro ⟨i,d⟩; simp
  right_inv := by rintro ⟨i,d⟩; simp

def blockVertex (ts : Fin n → Kind) (d : BD n) : BP n :=
  ((bundle d).1, vertex (ts (bundle d).1) (bundle d).2)

def blockColors (w : BP n → Color) (c : Fin n → Fin 4 → Color) (d : BD n) : Color :=
  colors (fun p => w ((bundle d).1, p)) (c (bundle d).1) (bundle d).2

def blockData [NeZero n] (ts : Fin n → Kind) : OpenTangleData (BP n) (BI n) (BP n) where
  interiorVert := fun d => blockVertex ts (.inl d)
  boundaryVert := fun p => blockVertex ts (.inr p)
  interiorAlpha := (Equiv.refl (Fin n)).prodCongr
    ((Equiv.refl (Fin 4)).prodCongr (Function.Involutive.toPerm not Bool.not_not))
  interiorAlpha_involutive := by rintro ⟨i,e,b⟩; cases b <;> rfl
  interiorAlpha_fixfree := by rintro ⟨i,e,b⟩; cases b <;> simp
  interior_no_self_loops := by
    rintro ⟨i,e,b⟩ h
    exact (localData (ts i)).interior_no_self_loops (e,b) (congrArg Prod.snd h)
  rho := bundle.trans ((blockPerm ts).trans bundle.symm)
  vert_rho := by
    intro d
    have hv : ∀ d, openTangleVertOf
        (fun d => blockVertex ts (.inl d)) (fun p => blockVertex ts (.inr p)) d =
          blockVertex ts d := by intro d; cases d <;> rfl
    rw [hv, hv]
    simp only [Equiv.trans_apply, blockVertex, Equiv.apply_symm_apply]
    change ((bundle d).1, vertex (ts (bundle d).1)
      ((localData (ts (bundle d).1)).rho (bundle d).2)) = _
    have h := (localData (ts (bundle d).1)).vert_rho (bundle d).2
    have he : ∀ t d, openTangleVertOf (localData t).interiorVert
      (localData t).boundaryVert d = vertex t d := by intro t d; cases d <;> rfl
    simpa only [he] using congrArg (fun v => ((bundle d).1, v)) h
  outer := .inr (0,0)

@[simp] theorem block_vert [NeZero n] (ts : Fin n → Kind) (d : BD n) :
    (ofOpenTangleData (blockData ts)).vert d = blockVertex ts d := by
  cases d <;> rfl

theorem local_cubic (t : Kind) : OpenIsCubic (localData t) := by
  unfold OpenIsCubic openDartsAt
  cases t <;> decide

theorem block_data_vert [NeZero n] (ts : Fin n → Kind) (d : BD n) :
    (blockData ts).vertOf d = blockVertex ts d := by
  cases d <;> rfl

theorem block_cubic [NeZero n] (ts : Fin n → Kind) : OpenIsCubic (blockData ts) := by
  rintro ⟨i,v⟩
  have heq : openDartsAt (blockData ts) (i,v) =
      (openDartsAt (localData (ts i)) v).image (fun d => bundle.symm (i,d)) := by
    ext d
    simp only [openDartsAt, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, block_data_vert]
    constructor
    · intro h
      have hi : (bundle d).1 = i := congrArg (fun p : BP n => p.1) h
      refine ⟨(bundle d).2, ?_, ?_⟩
      · have hv := congrArg (fun p : BP n => p.2) h
        change vertex (ts (bundle d).1) (bundle d).2 = v at hv
        rw [hi] at hv
        have hl : ∀ t d, (localData t).vertOf d = vertex t d := by
          intro t d; cases d <;> rfl
        simpa only [hl] using hv
      · apply bundle.injective
        simp only [Equiv.apply_symm_apply]
        exact Prod.ext hi.symm rfl
    · rintro ⟨e,he,rfl⟩
      simp only [blockVertex, Equiv.apply_symm_apply]
      have hl : ∀ t d, (localData t).vertOf d = vertex t d := by
        intro t d; cases d <;> rfl
      exact Prod.ext rfl (by simpa only [hl] using he)
  rw [heq, Finset.card_image_of_injective]
  · exact local_cubic (ts i) v
  · intro a b h
    exact (Prod.mk.inj (bundle.symm.injective h)).2

theorem block_valid_iff (ts : Fin n → Kind) (w : BP n → Color)
    (c : Fin n → Fin 4 → Color) :
    ((∀ d, blockColors w c d ≠ 0) ∧
      ∀ d e, blockVertex ts d = blockVertex ts e → d ≠ e →
        blockColors w c d ≠ blockColors w c e) ↔
      ∀ i, Valid (ts i) (fun p => w (i,p)) (c i) := by
  constructor
  · rintro ⟨hnz,hp⟩ i
    refine ⟨fun d => ?_, fun d e hv hne => ?_⟩
    · simpa [blockColors] using hnz (bundle.symm (i,d))
    · have hv' : blockVertex ts (bundle.symm (i,d)) =
          blockVertex ts (bundle.symm (i,e)) := by simp [blockVertex, hv]
      have hne' : bundle.symm (i,d) ≠ bundle.symm (i,e) :=
        fun h => hne (congrArg Prod.snd (bundle.symm.injective h))
      simpa [blockColors] using hp _ _ hv' hne'
  · intro h
    refine ⟨fun d => (h (bundle d).1).1 _, ?_⟩
    intro d e hv hne
    have hi : (bundle d).1 = (bundle e).1 := congrArg (fun p : BP n => p.1) hv
    have hv' := congrArg Prod.snd hv
    change vertex (ts (bundle d).1) (bundle d).2 =
      vertex (ts (bundle e).1) (bundle e).2 at hv'
    rw [← hi] at hv'
    have hd : (bundle d).2 ≠ (bundle e).2 := by
      intro he
      exact hne (bundle.injective (Prod.ext hi he))
    have hp := (h (bundle d).1).2 _ _ hv' hd
    simpa only [blockColors, ← hi] using hp

theorem block_realizes_iff [NeZero n] (ts : Fin n → Kind) (w : BP n → Color) :
    Realizes (blockData ts) w ↔ ∃ c : Fin n → Fin 4 → Color,
      ∀ i, Valid (ts i) (fun p => w (i,p)) (c i) := by
  constructor
  · rintro ⟨⟨col,hp,hw⟩⟩
    let c : Fin n → Fin 4 → Color := fun i e => col.color (.inl (i,e,false))
    have he : col.color = blockColors w c := by
      funext d
      rcases d with ⟨i,e,b⟩ | ⟨i,p⟩
      · cases b
        · rfl
        · exact col.invariant (i,e,false)
      · exact congrFun hw (i,p)
    refine ⟨c, (block_valid_iff ts w c).mp ?_⟩
    simpa only [IsProper, he, block_vert] using hp
  · rintro ⟨c,hc⟩
    let col : Coloring (ofOpenTangleData (blockData ts)) :=
      ⟨blockColors w c, by rintro ⟨i,e,b⟩; cases b <;> rfl⟩
    refine ⟨⟨col, ?_, ?_⟩⟩
    · simpa only [IsProper, col, block_vert] using (block_valid_iff ts w c).mpr hc
    · rfl

def bits (s : Fin n → Bool) : Fin n → Kind := fun i => bitKind (s i)
def tester (i : Fin n) : Fin n → Kind := fun j => if j = i then .test else .a

theorem block_experiment (s : Fin n → Bool) (i : Fin n) :
    (∃ (w : BP n → Color) (c d : Fin n → Fin 4 → Color),
      (∀ j, Valid (bits s j) (fun p => w (j,p)) (c j)) ∧
      (∀ j, Valid (tester i j) (fun p => w (j,p)) (d j))) ↔ s i = true := by
  constructor
  · rintro ⟨w,c,d,hs,ht⟩
    apply (bit_test (s i)).mp
    exact ⟨_,c i,d i,hs i,by simpa [tester] using ht i⟩
  · intro hi
    have h : ∀ j, ∃ w c d, Valid (bits s j) w c ∧ Valid (tester i j) w d := by
      intro j
      by_cases hj : j = i
      · subst j
        simpa [bits, hi, bitKind, tester] using b_accepted
      · simpa [bits, tester, hj] using neutral_exists (s j)
    choose w c d hc hd using h
    exact ⟨fun p => w p.1 p.2,c,d,hc,hd⟩

/-- The observer is the actual physical sewn rotation system, not an
arbitrary singleton boundary support. -/
theorem physical_test [NeZero n] (s : Fin n → Bool) (i : Fin n) :
    i ∈ physicalRightLanguage (fun i => reverseData (blockData (tester i)))
      (fun s => blockData (bits s)) (Equiv.refl (BP n)) s ↔ s i = true := by
  rw [mem_physicalRightLanguage_iff_supports_meet]
  simp only [left_realizes, right_realizes, realizes_reverse, block_realizes_iff]
  rw [← block_experiment s i]
  constructor
  · rintro ⟨w,⟨d,hd⟩,⟨c,hc⟩⟩
    exact ⟨w,c,d,hc,hd⟩
  · rintro ⟨w,c,d,hc,hd⟩
    exact ⟨w,⟨d,hd⟩,⟨c,hc⟩⟩

theorem exact_code_injective [NeZero n] {Code : Type*}
    (encode : (Fin n → Bool) → Code) (observe : Code → Fin n → Prop)
    (hexact : ∀ s i, observe (encode s) i ↔
      i ∈ physicalRightLanguage (fun i => reverseData (blockData (tester i)))
        (fun s => blockData (bits s)) (Equiv.refl (BP n)) s) :
    Function.Injective encode := by
  intro s t he
  funext i
  have hs := (hexact s i).trans (physical_test s i)
  have ht := (hexact t i).trans (physical_test t i)
  rw [he] at hs
  have h := hs.symm.trans ht
  cases hsi : s i <;> cases hti : t i <;> simp_all

/-- Already this physical family requires exponentially many exact codes
at a boundary of `4*n` ports. No claim is made for bridgeless-only tests. -/
theorem two_pow_le_card_code [NeZero n] {Code : Type*} [Fintype Code]
    (encode : (Fin n → Bool) → Code) (observe : Code → Fin n → Prop)
    (hexact : ∀ s i, observe (encode s) i ↔
      i ∈ physicalRightLanguage (fun i => reverseData (blockData (tester i)))
        (fun s => blockData (bits s)) (Equiv.refl (BP n)) s) :
    2 ^ n ≤ Fintype.card Code := by
  simpa using Fintype.card_le_of_injective encode (exact_code_injective encode observe hexact)

theorem port_card : Fintype.card (BP n) = 4 * n := by simp [BP, Nat.mul_comm]

theorem sewn_cubic [NeZero n] (s : Fin n → Bool) (i : Fin n) :
    ((reverseData (blockData (tester i))).composeRotationSystem
      (blockData (bits s)) (Equiv.refl (BP n))).IsCubic :=
  isCubic_composeRotationSystem _ _ _ (block_cubic _) (block_cubic _)

theorem exponential_exceeds_quadratic : ∀ n : Nat, 16 ≤ n →
    4 * ((4 * n) * (4 * n)) + 2 * (4 * n) + 2 < 2 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    nlinarith

end Mettapedia.GraphTheory.FourColor.PhysicalContextBits
