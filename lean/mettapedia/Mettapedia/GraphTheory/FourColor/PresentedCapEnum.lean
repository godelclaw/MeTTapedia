import Mettapedia.GraphTheory.FourColor.PresentedCap
import Mettapedia.GraphTheory.FourColor.PresentedEnumCorrect

/-!
# The support of a presented cap, enumerated

A presented cap's seam support (the boundary words extendable to a proper colouring of the
cap) is characterised by a closed form (`mem_innerSupport_iff`) and computed by the
vertex-ordered enumerator of the two-sided presentations, reused with the ports as in-ports
and no out-ports (`accepts_iff`).  `capWords` lists the support in the coordinates of the
certificate checker, exactly (`mem_wordsOf_taitInnerSupport_iff`).
-/

namespace Mettapedia.GraphTheory.FourColor
namespace KempeDerivation
namespace PresentedCap
namespace Pres

open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24ClosedCountReplacement GoertzelV24PhysicalClosedCountBridge
open GoertzelV24RawNooseCountPumping
open ZigzagRing TubeRingOrbit

variable {V N k : Nat} [NeZero k] (P : Pres V N k)

/-! ## The closed form of the seam support -/

/-- the colour at a position, given edge colours and the boundary word -/
def colAt (c : Fin N → Color) (x : Fin k → Color) (p : Pos V) : Color :=
  match P.slotAt p with
  | Slot.edge e => c e
  | Slot.port i => x i

/-- nonzero colours, pairwise distinct at every vertex -/
structure CapValid (c : Fin N → Color) (x : Fin k → Color) : Prop where
  c_ne_zero : ∀ e, c e ≠ 0
  x_ne_zero : ∀ i, x i ≠ 0
  distinct : ∀ v : Fin V, ∀ s s' : Fin 3, s ≠ s' → P.colAt c x (v, s) ≠ P.colAt c x (v, s')

theorem colAt_endPos (hP : P.Valid) (c : Fin N → Color) (x : Fin k → Color) (e : Fin N)
    (b : Bool) : P.colAt c x (P.endPos e b) = c e := by
  simp [colAt, hP.1 e b]

theorem colAt_portPos (hP : P.Valid) (c : Fin N → Color) (x : Fin k → Color) (i : Fin k) :
    P.colAt c x (P.portPos i) = x i := by
  simp [colAt, hP.2.2.1 i]

theorem pos_injective (hP : P.Valid) : Function.Injective (P.pos (N := N) (k := k)) :=
  (P.posEquiv hP).injective

section Support

variable {L : Type} [Fintype L] [DecidableEq L]

/-- the dart of the closed port tangle as a dart of the cap -/
def capDart (matching : L ≃ Fin k) : IDart (N := N) ⊕ (L ⊕ EmptyPort.{0}) → D (N := N) (k := k)
  | Sum.inl d => Sum.inl d
  | Sum.inr (Sum.inl p) => Sum.inr (matching p)
  | Sum.inr (Sum.inr e) => PEmpty.elim e

theorem capDart_injective (matching : L ≃ Fin k) :
    Function.Injective (capDart (N := N) matching) := by
  rintro (d | p | e) (d' | p' | e') h <;> (try simp only [capDart] at h) <;>
    first
    | exact e.elim | exact e'.elim | (cases h; rfl) | (cases h)
    | (rw [matching.injective h]) | (rw [matching.injective (Sum.inr_injective h)])

theorem vert_eq_pos (hP : P.Valid) (matching : L ≃ Fin k)
    (d : IDart (N := N) ⊕ (L ⊕ EmptyPort.{0})) :
    (rightClosedPortTangle (P.toCap hP) matching).vert d = (P.pos (capDart matching d)).1 := by
  rcases d with d | p | e
  · rfl
  · rfl
  · exact e.elim

/-- **the closed form of the seam support** -/
theorem mem_innerSupport_iff (hP : P.Valid) (matching : L ≃ Fin k) (y : L → Color) :
    y ∈ innerSupport (rightClosedPortTangle (P.toCap hP) matching) ↔
      ∃ c, P.CapValid c fun i => y (matching.symm i) := by
  constructor
  · rintro ⟨⟨col, ⟨hnz, hdistinct⟩, hword⟩⟩
    let c : Fin N → Color := fun e => col.color (Sum.inl (e, false))
    let x : Fin k → Color := fun i => y (matching.symm i)
    have hy : ∀ p : L, col.color (Sum.inr (Sum.inl p)) = y p := fun p =>
      congrFun hword (Sum.inl p)
    -- every dart's colour is the colour at its position
    have hcol : ∀ d, col.color d = P.colAt c x (P.pos (capDart matching d)) := by
      rintro (⟨e, b⟩ | p | e)
      · simp only [capDart, pos, colAt_endPos P hP]
        cases b
        · rfl
        · exact col.invariant (e, false)
      · simp only [capDart, pos, colAt_portPos P hP, x, Equiv.symm_apply_apply]
        exact hy p
      · exact e.elim
    refine ⟨c, ⟨fun e => hnz _, fun i => ?_, ?_⟩⟩
    · have := hnz (Sum.inr (Sum.inl (matching.symm i)))
      rwa [hy] at this
    · intro v s s' hss'
      have h1 := P.pos_dartAt hP (v, s)
      have h2 := P.pos_dartAt hP (v, s')
      -- the two darts of the closed tangle at these positions
      obtain ⟨d, hd⟩ : ∃ d, capDart matching d = P.dartAt (v, s) := by
        rcases hd : P.dartAt (v, s) with d | i
        · exact ⟨Sum.inl d, rfl⟩
        · exact ⟨Sum.inr (Sum.inl (matching.symm i)), by simp [capDart]⟩
      obtain ⟨d', hd'⟩ : ∃ d', capDart matching d' = P.dartAt (v, s') := by
        rcases hd' : P.dartAt (v, s') with d' | i
        · exact ⟨Sum.inl d', rfl⟩
        · exact ⟨Sum.inr (Sum.inl (matching.symm i)), by simp [capDart]⟩
      have hne : d ≠ d' := by
        intro h
        rw [h, hd'] at hd
        have := congrArg P.pos hd
        rw [h1, h2] at this
        exact hss' (Prod.mk.inj this).2.symm
      have hv : (rightClosedPortTangle (P.toCap hP) matching).vert d =
          (rightClosedPortTangle (P.toCap hP) matching).vert d' := by
        rw [vert_eq_pos P hP, vert_eq_pos P hP, hd, hd', h1, h2]
      have := hdistinct d d' hv hne
      rwa [hcol, hcol, hd, hd', h1, h2] at this
  · rintro ⟨c, hV⟩
    let x : Fin k → Color := fun i => y (matching.symm i)
    refine ⟨⟨⟨fun d => P.colAt c x (P.pos (capDart matching d)), ?_⟩, ⟨?_, ?_⟩, ?_⟩⟩
    · rintro ⟨e, b⟩
      show P.colAt c x (P.endPos e (!b)) = P.colAt c x (P.endPos e b)
      rw [colAt_endPos P hP, colAt_endPos P hP]
    · rintro (⟨e, b⟩ | p | e)
      · show P.colAt c x (P.endPos e b) ≠ 0
        rw [colAt_endPos P hP]; exact hV.c_ne_zero e
      · show P.colAt c x (P.portPos (matching p)) ≠ 0
        rw [colAt_portPos P hP]; exact hV.x_ne_zero _
      · exact e.elim
    · intro d d' hv hne
      rw [vert_eq_pos P hP, vert_eq_pos P hP] at hv
      have hs : (P.pos (capDart matching d)).2 ≠ (P.pos (capDart matching d')).2 := by
        intro h
        apply hne
        apply capDart_injective matching
        apply P.pos_injective hP
        exact Prod.ext hv h
      have := hV.distinct (P.pos (capDart matching d)).1 _ _ hs
      have e2 : P.pos (capDart matching d') =
          ((P.pos (capDart matching d)).1, (P.pos (capDart matching d')).2) := by
        rw [hv]
      show P.colAt c x (P.pos (capDart matching d)) ≠ P.colAt c x (P.pos (capDart matching d'))
      rw [e2]
      exact this
    · funext p
      rcases p with p | e
      · show P.colAt c x (P.portPos (matching p)) = y p
        rw [colAt_portPos P hP]
        simp [x]
      · exact e.elim

end Support

/-! ## The enumerator, reused with ports as in-ports -/

/-- the cap's slot as a two-sided slot -/
def toSlot : Slot N k → TubeSlab.Presented.Slot N k
  | Slot.edge e => TubeSlab.Presented.Slot.edge e
  | Slot.port i => TubeSlab.Presented.Slot.inp i

/-- the cap as a two-sided presentation for the enumerator; out-ports are never used -/
def toEnum : TubeSlab.Presented.Pres V N k where
  tri v s := toSlot (P.tri v s)
  endPos := P.endPos
  inPos := P.portPos
  outPos := P.portPos

/-- the complete proper assignments for the boundary word `x` -/
def final (x : Fin k → Fin 3) : List (TubeSlab.Presented.PA N k) :=
  P.toEnum.runVertices x (List.finRange V) [TubeSlab.Presented.PA.empty]

/-- the boundary word `x` is in the support -/
def accepts (x : Fin k → Fin 3) : Bool := !(P.final x).isEmpty

theorem toSlot_ne_out (s : Slot N k) (i : Fin k) : toSlot s ≠ TubeSlab.Presented.Slot.out i := by
  cases s <;> simp [toSlot]

theorem toSlot_eq_edge_iff (s : Slot N k) (e : Fin N) :
    toSlot s = TubeSlab.Presented.Slot.edge e ↔ s = Slot.edge e := by
  cases s <;> simp [toSlot]

/-- every edge slot occurs at some vertex of the enumerator presentation -/
theorem slotsOf_edge (hP : P.Valid) (e : Fin N) :
    P.toEnum.SlotsOf (List.finRange V) (TubeSlab.Presented.Slot.edge e) := by
  refine ⟨(P.endPos e false).1, List.mem_finRange _, ?_⟩
  have := hP.1 e false
  simp only [slotAt] at this
  simp only [TubeSlab.Presented.Pres.SlotOf, toEnum]
  rcases hs3 : (P.endPos e false).2 with ⟨n, hn⟩
  rw [hs3] at this
  match n, hn, this with
  | 0, hn, h => exact Or.inl (by rw [show (0 : Fin 3) = ⟨0, hn⟩ from rfl, h]; rfl)
  | 1, hn, h => exact Or.inr (Or.inl (by rw [show (1 : Fin 3) = ⟨1, hn⟩ from rfl, h]; rfl))
  | 2, hn, h => exact Or.inr (Or.inr (by rw [show (2 : Fin 3) = ⟨2, hn⟩ from rfl, h]; rfl))

theorem not_slotsOf_out (i : Fin k) :
    ¬ P.toEnum.SlotsOf (List.finRange V) (TubeSlab.Presented.Slot.out i) := by
  rintro ⟨v, -, h | h | h⟩ <;> exact toSlot_ne_out _ i h.symm

/-- membership in the final list: every edge assigned, no out-port assigned, every vertex
proper -/
theorem mem_final_iff (hP : P.Valid) (x : Fin k → Fin 3) (σ : TubeSlab.Presented.PA N k) :
    σ ∈ P.final x ↔
      (∀ e, (σ.e e).isSome) ∧ (∀ i, σ.o i = none) ∧
        ∀ v, TubeSlab.Presented.PA.properAt x σ (toSlot (P.tri v 0)) (toSlot (P.tri v 1))
          (toSlot (P.tri v 2)) = true := by
  unfold final
  rw [TubeSlab.Presented.Pres.mem_runVertices_iff]
  constructor
  · rintro ⟨σ₀, hσ₀, -, hdom, hp⟩
    simp only [List.mem_singleton] at hσ₀
    subst hσ₀
    refine ⟨fun e => ?_, fun i => ?_, fun v => hp v (List.mem_finRange v)⟩
    · have := (hdom (TubeSlab.Presented.Slot.edge e)).2 (Or.inr (P.slotsOf_edge hP e))
      simpa [TubeSlab.Presented.PA.look] using this
    · have := hdom (TubeSlab.Presented.Slot.out i)
      simp only [TubeSlab.Presented.PA.look, TubeSlab.Presented.PA.empty, Option.isSome_none,
        Bool.false_eq_true, false_or] at this
      have h2 := this.not.2 (P.not_slotsOf_out i)
      simpa using h2
  · rintro ⟨hall, hout, hp⟩
    refine ⟨TubeSlab.Presented.PA.empty, List.mem_singleton_self _, ?_, fun s => ?_,
      fun v _ => hp v⟩
    · intro s hs
      rcases s with e | i | i
      · simp [TubeSlab.Presented.PA.look, TubeSlab.Presented.PA.empty] at hs
      · rfl
      · simp [TubeSlab.Presented.PA.look, TubeSlab.Presented.PA.empty] at hs
    · rcases s with e | i | i
      · simp only [TubeSlab.Presented.PA.look, TubeSlab.Presented.PA.empty, Option.isSome_none,
          Bool.false_eq_true, false_or]
        exact ⟨fun _ => P.slotsOf_edge hP e, fun _ => hall e⟩
      · simp [TubeSlab.Presented.PA.look]
      · simp only [TubeSlab.Presented.PA.look, TubeSlab.Presented.PA.empty, Option.isSome_none,
          Bool.false_eq_true, false_or, hout i]
        exact ⟨fun h => absurd h (by simp), fun h => absurd h (P.not_slotsOf_out i)⟩

/-- the digit of a cap slot under an assignment with all edges assigned -/
theorem look_toSlot (x : Fin k → Fin 3) (σ : TubeSlab.Presented.PA N k) (s : Slot N k) :
    σ.look x (toSlot s) = match s with
      | Slot.edge e => σ.e e
      | Slot.port i => some (x i) := by
  cases s <;> rfl

/-- **the enumerator decides the closed form** -/
theorem accepts_iff (hP : P.Valid) (X : Nat) :
    P.accepts (TubeSlab.Presented.Pres.inWord X) = true ↔ ∃ c, P.CapValid c (wordOf k X) := by
  unfold accepts
  rw [Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem]
  constructor
  · rintro ⟨σ, hσ⟩
    rw [mem_final_iff P hP] at hσ
    obtain ⟨hall, -, hp⟩ := hσ
    -- the colouring of the assignment
    let c : Fin N → Color := fun e => col ((σ.e e).getD 0)
    have hdig : ∀ p : Pos V, P.colAt c (wordOf k X) p =
        col (((σ.look (TubeSlab.Presented.Pres.inWord X) (toSlot (P.slotAt p))).getD 0 : Fin 3) : Nat) := by
      intro p
      unfold colAt
      cases P.slotAt p with
      | edge e => rfl
      | port i => simp [look_toSlot, wordOf, TubeSlab.Presented.Pres.inWord_val]
    refine ⟨c, ⟨fun e => col_ne_zero _, fun i => wordOf_ne_zero k X i, ?_⟩⟩
    intro v s s' hss'
    rw [hdig, hdig]
    have hpv := (TubeSlab.Presented.PA.properAt_iff (TubeSlab.Presented.Pres.inWord X) σ _ _ _).mp (hp v)
    obtain ⟨a, b, d, h0, h1, h2, hab, had, hbd⟩ := hpv
    intro heq
    have := TubeSlab.Presented.Pres.col_fin_inj heq
    simp only [slotAt] at this
    fin_cases s <;> fin_cases s' <;> simp at hss' <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, h0, h1, h2, Option.getD_some]
        at this <;>
      first
      | exact hab this | exact hab this.symm
      | exact had this | exact had this.symm
      | exact hbd this | exact hbd this.symm
  · rintro ⟨c, hV⟩
    let σ : TubeSlab.Presented.PA N k :=
      ⟨fun e => some ⟨idx (c e), idx_lt _⟩, fun _ => none⟩
    have hdig : ∀ p : Pos V,
        col (((σ.look (TubeSlab.Presented.Pres.inWord X) (toSlot (P.slotAt p))).getD 0 : Fin 3) : Nat) =
          P.colAt c (wordOf k X) p := by
      intro p
      unfold colAt
      cases P.slotAt p with
      | edge e => simp [σ, look_toSlot, col_idx (hV.c_ne_zero e)]
      | port i => simp [look_toSlot, wordOf, TubeSlab.Presented.Pres.inWord_val]
    refine ⟨σ, ?_⟩
    rw [mem_final_iff P hP]
    refine ⟨fun e => rfl, fun i => rfl, fun v => ?_⟩
    rw [TubeSlab.Presented.PA.properAt_iff]
    have hd : ∀ s s' : Fin 3, s ≠ s' →
        ((σ.look (TubeSlab.Presented.Pres.inWord X) (toSlot (P.tri v s))).getD 0 : Fin 3) ≠
          (σ.look (TubeSlab.Presented.Pres.inWord X) (toSlot (P.tri v s'))).getD 0 := by
      intro s s' hss' heq
      apply hV.distinct v s s' hss'
      rw [← hdig (v, s), ← hdig (v, s')]
      simp only [slotAt]
      rw [heq]
    have hsome : ∀ s : Slot N k, (σ.look (TubeSlab.Presented.Pres.inWord X) (toSlot s)).isSome := by
      intro s; cases s <;> simp [σ, look_toSlot]
    refine ⟨_, _, _, ?_, ?_, ?_, hd 0 1 (by decide), hd 0 2 (by decide), hd 1 2 (by decide)⟩ <;>
      exact TubeSlab.Presented.Pres.look_eq_some_digitOf _ _ _ (hsome _)

/-! ## The support as a word list -/

/-- the support, as a list of Tait words in port coordinates -/
def capWords (_hP : P.Valid) : List (Word k) :=
  ((List.range (3 ^ k)).filter fun X => P.accepts (TubeSlab.Presented.Pres.inWord X)).map fun X i =>
    ⟨wordOf k X i, wordOf_ne_zero k X i⟩

/-- the numeral of a Tait word -/
def numeralOf (w : Word k) : Nat := encB 3 (fun i => if h : i < k then idx (w ⟨i, h⟩).1 else 0) k

theorem numeralOf_lt (w : Word k) : numeralOf w < 3 ^ k :=
  encB_lt (by norm_num) k (fun j hj => by rw [dif_pos hj]; exact idx_lt _)

theorem wordOf_numeralOf (w : Word k) (i : Fin k) : wordOf k (numeralOf w) i = (w i).1 := by
  unfold wordOf numeralOf
  rw [digit_eq_digB, digB_encB (by norm_num) k (fun j hj => by
    rw [dif_pos hj]; exact idx_lt _) i i.isLt]
  simp [i.isLt, col_idx (w i).2]

theorem mem_capWords_iff (hP : P.Valid) (w : Word k) :
    w ∈ P.capWords hP ↔ ∃ c, P.CapValid c fun i => (w i).1 := by
  unfold capWords
  simp only [List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨X, ⟨-, hacc⟩, rfl⟩
    obtain ⟨c, hc⟩ := (P.accepts_iff hP X).1 hacc
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    refine ⟨numeralOf w, ⟨numeralOf_lt w, ?_⟩, ?_⟩
    · rw [P.accepts_iff hP]
      refine ⟨c, ?_⟩
      have : (wordOf k (numeralOf w)) = fun i => (w i).1 := funext (wordOf_numeralOf w)
      rw [this]; exact hc
    · funext i
      exact Subtype.ext (wordOf_numeralOf w i)

/-- the digits of a Tait word -/
def digitsOf (w : Word k) : Fin k → Fin 3 := fun i => ⟨idx (w i).1, idx_lt _⟩

theorem inWord_numeralOf (w : Word k) :
    TubeSlab.Presented.Pres.inWord (numeralOf w) = digitsOf w := by
  funext i
  apply Fin.ext
  show digit (numeralOf w) i = idx (w i).1
  unfold numeralOf
  rw [digit_eq_digB, digB_encB (by norm_num) k (fun j hj => by
    rw [dif_pos hj]; exact idx_lt _) i i.isLt]
  simp [i.isLt]

/-- the enumerator on a Tait word -/
def acceptsWord (w : Word k) : Bool := P.accepts (digitsOf w)

theorem acceptsWord_iff (hP : P.Valid) (w : Word k) :
    P.acceptsWord w = true ↔ ∃ c, P.CapValid c fun i => (w i).1 := by
  unfold acceptsWord
  rw [← inWord_numeralOf, P.accepts_iff hP]
  have : wordOf k (numeralOf w) = fun i => (w i).1 := funext (wordOf_numeralOf w)
  rw [this]

/-- **the support in certificate coordinates is the enumerated list** -/
theorem mem_wordsOf_taitInnerSupport_iff (hP : P.Valid) {L : Type} [Fintype L] [DecidableEq L]
    (order : Fin k ≃ L) (w : Word k) :
    w ∈ wordsOf order (taitInnerSupport (rightClosedPortTangle (P.toCap hP) order.symm)) ↔
      w ∈ P.capWords hP := by
  rw [mem_capWords_iff]
  show cutWordColor (fun l => w (order.symm l)) ∈
    innerSupport (rightClosedPortTangle (P.toCap hP) order.symm) ↔ _
  rw [mem_innerSupport_iff P hP]
  simp [cutWordColor]

end Pres
end PresentedCap
end KempeDerivation
end Mettapedia.GraphTheory.FourColor
