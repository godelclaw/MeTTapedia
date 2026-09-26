import Mettapedia.GraphTheory.FourColor.ZigzagRingTwoColour
import Mettapedia.GraphTheory.FourColor.ZigzagRingComposite
import Mettapedia.GraphTheory.FourColor.OpenTangleWitnessComposition
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Exact boundary semantics and shortening of zigzag tubes

Full three-colour words mix within their multiplicity classes. Words missing
a colour only rotate. Together these give a stationary boundary relation at
an explicit circumference-dependent threshold, for every boundary word.
The resulting shortening preserves compatibility with arbitrary exterior
constraints. No claim that an arbitrary contour band consists of these rings
is made.
-/

namespace Mettapedia.GraphTheory.FourColor.ZigzagRing

open GoertzelV24CorridorPumping

variable (k : Nat) [NeZero k]

private theorem move_symm {x y : Fin k → Color} (h : Move k x y) : Move k y x := by
  rcases h with rfl | ⟨j, rfl⟩
  · exact Or.inl rfl
  · right
    refine ⟨j, ?_⟩
    funext i
    simp only [swapAt_eq_comp_swap, Function.comp_apply, Equiv.swap_apply_self]

private def moveGraph : SimpleGraph (Fin k → Color) where
  Adj x y := x ≠ y ∧ Move k x y
  symm := ⟨fun _ _ h => ⟨h.1.symm, move_symm k h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem move_walk {n : Nat} {x y : Fin k → Color}
    (h : ExactRelationalTransfer (Move k) n x y) : Nonempty ((moveGraph k).Walk x y) := by
  induction h with
  | zero => exact ⟨.nil⟩
  | @succ n x z y hs ht ih =>
    obtain ⟨w⟩ := ih
    by_cases he : x = z
    · subst z
      exact ⟨w⟩
    · exact ⟨.cons ⟨he, hs⟩ w⟩

private theorem walk_moves {x y : Fin k → Color} (w : (moveGraph k).Walk x y) :
    ExactRelationalTransfer (Move k) w.length x y := by
  induction w with
  | nil => exact .zero _
  | cons h w ih => exact .succ h.2 ih

private theorem idle_moves (n : Nat) (x : Fin k → Color) :
    ExactRelationalTransfer (Move k) n x x := by
  induction n with
  | zero => exact .zero _
  | succ n ih => exact .succ (Or.inl rfl) ih

omit [NeZero k] in
private theorem word_card : Fintype.card (Fin k → Color) = 4 ^ k := by
  rw [Fintype.card_fun, Fintype.card_fin]
  congr 1

/-- A coarse explicit bound obtained by erasing loops from an adjacent-swap
walk in the finite word graph. Idle moves supply every longer length. -/
theorem moves_after_word_bound (x y : Fin k → Color)
    (hc : ∀ c, colourCount k x c = colourCount k y c) (n : Nat) (hn : 4 ^ k ≤ n) :
    ExactRelationalTransfer (Move k) n x y := by
  classical
  obtain ⟨p, hp⟩ := exists_perm_of_counts k x y hc
  obtain ⟨N, hN⟩ := exists_move_threshold k
  obtain ⟨w⟩ := move_walk k (hN p N le_rfl x)
  rw [← hp] at w
  let q := w.toPath
  have hshort : q.val.length < 4 ^ k := by
    simpa only [word_card] using q.property.length_lt
  have hpath := (walk_moves k q.val).comp (idle_moves k (n - q.val.length) y)
  simpa only [Nat.add_sub_of_le (hshort.le.trans hn)] using hpath

/-- The ergodic three-colour case has the explicit threshold `2 * 4^k`.
This deliberately coarse bound is independent of the count class. -/
theorem full_transfer_after_word_bound (hk : 3 ≤ k) (x y : Fin k → Color)
    (hx : Full k x) (hc : ∀ c, colourCount k x c = colourCount k y c)
    (r : Nat) (hr : 2 * 4 ^ k ≤ r) : ExactRelationalTransfer (Step k) r x y := by
  have heven : ∀ x y : Fin k → Color, Full k x →
      (∀ c, colourCount k x c = colourCount k y c) →
      ∀ n, 4 ^ k ≤ n → ExactRelationalTransfer (Step k) (2 * n) x y := by
    intro x y hx hc n hn
    let z := (shiftEquiv k ^ n).symm y
    have hcz : ∀ c, colourCount k x c = colourCount k z c := by
      intro c
      have hs := colourCount_shiftEquiv_pow k n z c
      have hcancel : (shiftEquiv k ^ n) z = y := Equiv.apply_symm_apply _ _
      rw [hcancel] at hs
      exact (hc c).trans hs
    have hm := moves_after_word_bound k x z hcz n hn
    simpa only [z, Equiv.apply_symm_apply] using transfer_of_movePath k hk hm hx
  by_cases hpar : r % 2 = 0
  · have hlen : 2 * (r / 2) = r := by omega
    simpa only [hlen] using heven x y hx hc (r / 2) (by omega)
  · have hlen : 1 + 2 * (r / 2) = r := by omega
    obtain ⟨z, hz⟩ := hx.exists_step k hk
    have hzcount : ∀ c, colourCount k z c = colourCount k y c :=
      fun c => (hz.colourCount k c).trans (hc c)
    have ht := heven z y (hz.full_target k hx) hzcount (r / 2) (by omega)
    have hs : ExactRelationalTransfer (Step k) 1 x z := .succ hz (.zero _)
    simpa only [hlen] using hs.comp ht

theorem shift_iterate_apply (n : Nat) (x : Fin k → Color) (i : Fin k) :
    ((shift k)^[n] x) i = x (i + Fin.ofNat k n) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', shift, ih]
    congr 1
    have hc : Fin.ofNat k (n + 1) = Fin.ofNat k n + 1 := by
      apply Fin.ext
      exact Nat.add_mod n 1 k
    rw [hc]
    ac_rfl

theorem shift_period (x : Fin k → Color) : (shift k)^[k] x = x := by
  funext i
  rw [shift_iterate_apply]
  simp

private theorem shift_nz (n : Nat) {x : Fin k → Color} (hx : ∀ i, x i ≠ 0) :
    ∀ i, ((shift k)^[n] x) i ≠ 0 := by
  intro i
  rw [shift_iterate_apply]
  exact hx _

private theorem shift_missing (n : Nat) {x : Fin k → Color} {c : Color}
    (hx : ∀ i, x i ≠ c) : ∀ i, ((shift k)^[n] x) i ≠ c := by
  intro i
  rw [shift_iterate_apply]
  exact hx _

private theorem missing_idle (n : Nat) {x : Fin k → Color} (hx : ∀ i, x i ≠ 0)
    {c : Color} (hc : c ≠ 0) (hm : ∀ i, x i ≠ c) :
    ExactRelationalTransfer (Step k) n x x := by
  induction n with
  | zero => exact .zero _
  | succ n ih => exact .succ ((step_iff_of_missing k x x hx hc hm).mpr (Or.inl rfl)) ih

private theorem missing_shifts (n : Nat) {x : Fin k → Color} (hx : ∀ i, x i ≠ 0)
    {c : Color} (hc : c ≠ 0) (hm : ∀ i, x i ≠ c) :
    ExactRelationalTransfer (Step k) n x ((shift k)^[n] x) := by
  induction n with
  | zero => exact .zero _
  | succ n ih =>
    have hs : Step k ((shift k)^[n] x) (shift k ((shift k)^[n] x)) :=
      (step_iff_of_missing k _ _ (shift_nz k n hx) hc (shift_missing k n hm)).mpr (Or.inr rfl)
    simpa only [Function.iterate_succ_apply'] using ih.comp (.succ hs (.zero _))

/-- Missing-colour sectors stabilize to cyclic rotation, including constant
words. They are not replaced by the larger multiplicity equivalence. -/
theorem missing_transfer_iff_rotation (x y : Fin k → Color) (hx : ∀ i, x i ≠ 0)
    {c : Color} (hc : c ≠ 0) (hm : ∀ i, x i ≠ c) (n : Nat) (hn : k ≤ n) :
    ExactRelationalTransfer (Step k) n x y ↔ ∃ j : Fin k, y = (shift k)^[j.val] x := by
  constructor
  · intro h
    obtain ⟨m, _, heq⟩ := transfer_rotation_of_missing k h hc hm
    refine ⟨⟨m % k, Nat.mod_lt _ (NeZero.pos k)⟩, ?_⟩
    exact heq.trans (Function.IsPeriodicPt.iterate_mod_apply (shift_period k x) m).symm
  · rintro ⟨j, rfl⟩
    have hj : j.val ≤ n := j.isLt.le.trans hn
    have hs := missing_shifts k j.val hx hc hm
    have hi := missing_idle k (n - j.val) (shift_nz k j.val hx) hc (shift_missing k j.val hm)
    simpa only [Nat.add_sub_of_le hj] using hs.comp hi

/-- Explicit sufficient length for every sector, with no fixed width bound. -/
def compressionBound : Nat := 2 * 4 ^ k + k

/-- The stable relation remembers multiplicities in the full-colour sectors,
and cyclic order in the missing-colour sectors. Zero boundary entries fail. -/
def StableRelation (x y : Fin k → Color) : Prop :=
  (∀ i, x i ≠ 0) ∧
    ((Full k x ∧ ∀ c, colourCount k x c = colourCount k y c) ∨
      ∃ c : Color, c ≠ 0 ∧ (∀ i, x i ≠ c) ∧
        ∃ j : Fin k, y = (shift k)^[j.val] x)

theorem transfer_colourCount {n : Nat} {x y : Fin k → Color}
    (h : ExactRelationalTransfer (Step k) n x y) (c : Color) :
    colourCount k y c = colourCount k x c := by
  induction h with
  | zero => rfl
  | succ hs ht ih => exact ih.trans (hs.colourCount k c)

private theorem transfer_input_nz {n : Nat} {x y : Fin k → Color}
    (h : ExactRelationalTransfer (Step k) n x y) (hn : 0 < n) : ∀ i, x i ≠ 0 := by
  cases h with
  | zero => omega
  | succ hs ht =>
    obtain ⟨a, ha, _⟩ := (accepts_iff k _ _).mp hs
    exact ha.x_ne_zero

/-- Exact eventual semantics for all words, including the nonmixing sectors. -/
theorem transfer_iff_stable (hk : 3 ≤ k) (x y : Fin k → Color)
    (n : Nat) (hn : compressionBound k ≤ n) :
    ExactRelationalTransfer (Step k) n x y ↔ StableRelation k x y := by
  classical
  have hfullBound : 2 * 4 ^ k ≤ n := (Nat.le_add_right _ _).trans hn
  have hwidth : k ≤ n := (Nat.le_add_left _ _).trans hn
  constructor
  · intro h
    have hx := transfer_input_nz k h (by omega)
    refine ⟨hx, ?_⟩
    by_cases hf : Full k x
    · exact Or.inl ⟨hf, fun c => (transfer_colourCount k h c).symm⟩
    · have hm : ∃ c : Color, c ≠ 0 ∧ ∀ i, x i ≠ c := by
        by_contra hnone
        apply hf
        refine ⟨hx, ?_⟩
        intro c hc
        by_contra hno
        exact hnone ⟨c, hc, by simpa only [not_exists] using hno⟩
      obtain ⟨c, hc, hm⟩ := hm
      exact Or.inr ⟨c, hc, hm, (missing_transfer_iff_rotation k x y hx hc hm n hwidth).mp h⟩
  · rintro ⟨hx, ⟨hf, hc⟩ | ⟨c, hc, hm, hj⟩⟩
    · exact full_transfer_after_word_bound k hk x y hf hc n hfullBound
    · exact (missing_transfer_iff_rotation k x y hx hc hm n hwidth).mpr hj

/-- Any two sufficiently long tubes have exactly the same ordered support. -/
theorem transfer_stabilizes (hk : 3 ≤ k) (x y : Fin k → Color)
    {r s : Nat} (hr : compressionBound k ≤ r) (hs : compressionBound k ≤ s) :
    ExactRelationalTransfer (Step k) r x y ↔ ExactRelationalTransfer (Step k) s x y :=
  (transfer_iff_stable k hk x y r hr).trans (transfer_iff_stable k hk x y s hs).symm

namespace HiddenTangle

variable {L : Type}

noncomputable def appendRings (T : HiddenTangle L (Fin k)) (n : Nat) :
    HiddenTangle L (Fin k) := (appendRing k)^[n] T

/-- Literal serial gluing agrees with the exact-length ring relation. -/
theorem appendRings_accepts_iff (T : HiddenTangle L (Fin k))
    (l : L → Color) (y : Fin k → Color) (n : Nat) :
    (appendRings k T n).Accepts l y ↔
      ∃ x, T.Accepts l x ∧ ExactRelationalTransfer (Step k) n x y := by
  induction n generalizing T with
  | zero =>
    constructor
    · intro h
      exact ⟨y, h, .zero _⟩
    · rintro ⟨x, hx, hp⟩
      cases hp
      exact hx
  | succ n ih =>
    change ((appendRing k)^[n + 1] T).Accepts l y ↔ _
    rw [Function.iterate_succ_apply]
    change (appendRings k (appendRing k T) n).Accepts l y ↔ _
    rw [ih]
    constructor
    · rintro ⟨z, hz, hp⟩
      obtain ⟨x, hx, hs⟩ := (appendRing_accepts_iff k T l z).mp hz
      exact ⟨x, hx, .succ hs hp⟩
    · rintro ⟨x, hx, hp⟩
      cases hp with
      | succ hs ht => exact ⟨_, (appendRing_accepts_iff k T l _).mpr ⟨x, hx, hs⟩, ht⟩

theorem appendRings_support_eq (hk : 3 ≤ k) (T : HiddenTangle L (Fin k))
    (l : L → Color) (y : Fin k → Color) {r s : Nat}
    (hr : compressionBound k ≤ r) (hs : compressionBound k ≤ s) :
    (appendRings k T r).Accepts l y ↔ (appendRings k T s).Accepts l y := by
  simp only [appendRings_accepts_iff, transfer_stabilizes k hk _ _ hr hs]

theorem appendRings_finite (T : HiddenTangle L (Fin k)) [Finite T.V] (n : Nat) :
    Finite (appendRings k T n).V := by
  induction n with
  | zero => exact inferInstanceAs (Finite T.V)
  | succ n ih =>
    change Finite (((appendRing k)^[n + 1]) T).V
    rw [Function.iterate_succ_apply']
    change Finite ((appendRings k T n).V ⊕ Vtx k)
    let := ih
    infer_instance

theorem appendRing_vertex_card (T : HiddenTangle L (Fin k)) [Finite T.V] :
    Nat.card (appendRing k T).V = Nat.card T.V + 2 * k := by
  change Nat.card (T.V ⊕ Vtx k) = _
  simp [Nat.card_sum, Vtx, two_mul]

theorem appendRings_vertex_card (T : HiddenTangle L (Fin k)) [Finite T.V] (n : Nat) :
    Nat.card (appendRings k T n).V = Nat.card T.V + 2 * k * n := by
  induction n with
  | zero => simp [appendRings]
  | succ n ih =>
    change Nat.card (((appendRing k)^[n + 1]) T).V = _
    rw [Function.iterate_succ_apply']
    change Nat.card (appendRing k (appendRings k T n)).V = _
    let := appendRings_finite k T n
    rw [appendRing_vertex_card, ih]
    ring

end HiddenTangle

/-- A nonempty physical tube: `n + 1` rings, hence no artificial identity
piece or port identification is needed. -/
noncomputable def tube (n : Nat) : HiddenTangle (Fin k) (Fin k) :=
  HiddenTangle.appendRings k ⟨Vtx k, Dart k, ring k⟩ n

theorem tube_accepts_iff (n : Nat) (x y : Fin k → Color) :
    (tube k n).Accepts x y ↔ ExactRelationalTransfer (Step k) (n + 1) x y := by
  rw [tube, HiddenTangle.appendRings_accepts_iff]
  constructor
  · rintro ⟨z, hs, ht⟩
    exact .succ hs ht
  · intro h
    cases h with
    | succ hs ht => exact ⟨_, hs, ht⟩

theorem tube_support_eq (hk : 3 ≤ k) (x y : Fin k → Color) {r s : Nat}
    (hr : compressionBound k ≤ r + 1) (hs : compressionBound k ≤ s + 1) :
    (tube k r).Accepts x y ↔ (tube k s).Accepts x y := by
  rw [tube_accepts_iff, tube_accepts_iff]
  exact transfer_stabilizes k hk x y hr hs

theorem tube_vertex_card (n : Nat) : Nat.card (tube k n).V = 2 * k * (n + 1) := by
  rw [tube, HiddenTangle.appendRings_vertex_card]
  simp only [Vtx, Nat.card_sum, Nat.card_fin]
  ring

open OpenTangleWitnessComposition Mettapedia.GSLT.LooseRelationEquipment

/-- Transport actual colouring witnesses while retaining both boundary words.
This is a support-preserving map, not a bijection of colouring fibres. -/
noncomputable def tubeLengthCell (hk : 3 ≤ k) {r s : Nat}
    (hr : compressionBound k ≤ r + 1) (hs : compressionBound k ≤ s + 1) :
    Cell id id (colourRelation (tube k r).data) (colourRelation (tube k s).data) where
  map := fun {x y} w => Classical.choice <|
    (nonempty_colourRelation_iff _ x y).mpr <|
      (tube_support_eq k hk x y hr hs).mp ⟨w.val, w.property⟩

/-- The replacement removes actual vertices and every replacement colouring
reconstructs a colouring of the original with the same ordered seam words. -/
theorem strict_tube_shortening (hk : 3 ≤ k) (n : Nat) (hn : compressionBound k ≤ n) :
    Nat.card (tube k (compressionBound k - 1)).V < Nat.card (tube k n).V ∧
      Nonempty (Cell id id (colourRelation (tube k (compressionBound k - 1)).data)
        (colourRelation (tube k n).data)) ∧
      Nonempty (Cell id id (colourRelation (tube k n).data)
        (colourRelation (tube k (compressionBound k - 1)).data)) := by
  have hb : 0 < compressionBound k := by unfold compressionBound; omega
  refine ⟨?_, ⟨tubeLengthCell k hk (by omega) (by omega)⟩,
    ⟨tubeLengthCell k hk (by omega) (by omega)⟩⟩
  rw [tube_vertex_card, tube_vertex_card]
  exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)

open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData

variable {A W K J P Q : Type}

/-- Reconstruct inside an arbitrary serial context. The generic exterior
theorem proves that both surrounding colourings remain identical. -/
noncomputable def reconstructTubeInContext (hk : 3 ≤ k) {r s : Nat}
    (hr : compressionBound k ≤ r + 1) (hs : compressionBound k ≤ s + 1)
    (initial : TwoSidedOpenTangleData A K P (Fin k))
    (final : TwoSidedOpenTangleData W J (Fin k) Q) :
    Cell id id
      (colourRelation (serialCompose
        (serialCompose initial (tube k r).data (Equiv.refl _)) final (Equiv.refl _)))
      (colourRelation (serialCompose
        (serialCompose initial (tube k s).data (Equiv.refl _)) final (Equiv.refl _))) :=
  replaceInContext initial (tubeLengthCell k hk hr hs) final

theorem reconstructTubeInContext_exterior (hk : 3 ≤ k) {r s : Nat}
    (hr : compressionBound k ≤ r + 1) (hs : compressionBound k ≤ s + 1)
    (initial : TwoSidedOpenTangleData A K P (Fin k))
    (final : TwoSidedOpenTangleData W J (Fin k) Q)
    {x : P → Color} {z : Q → Color}
    (witness : colourRelation (serialCompose
      (serialCompose initial (tube k r).data (Equiv.refl _)) final (Equiv.refl _)) x z) :
    exteriorWitnesses initial (tube k s).data final
        ((reconstructTubeInContext k hk hr hs initial final).map witness) =
      exteriorWitnesses initial (tube k r).data final witness :=
  replaceInContext_exteriorWitnesses initial (tubeLengthCell k hk hr hs) final witness

/-- Every external fibre is simultaneously empty or nonempty after
shortening. Exact colouring counts need not be preserved. -/
theorem tube_context_nonempty_iff (hk : 3 ≤ k) {r s : Nat}
    (hr : compressionBound k ≤ r + 1) (hs : compressionBound k ≤ s + 1)
    (initial : TwoSidedOpenTangleData A K P (Fin k))
    (final : TwoSidedOpenTangleData W J (Fin k) Q)
    (x : P → Color) (z : Q → Color) :
    Nonempty (colourRelation (serialCompose
      (serialCompose initial (tube k r).data (Equiv.refl _)) final (Equiv.refl _)) x z) ↔
    Nonempty (colourRelation (serialCompose
      (serialCompose initial (tube k s).data (Equiv.refl _)) final (Equiv.refl _)) x z) := by
  constructor
  · rintro ⟨w⟩
    exact ⟨(reconstructTubeInContext k hk hr hs initial final).map w⟩
  · rintro ⟨w⟩
    exact ⟨(reconstructTubeInContext k hk hs hr initial final).map w⟩

end Mettapedia.GraphTheory.FourColor.ZigzagRing
