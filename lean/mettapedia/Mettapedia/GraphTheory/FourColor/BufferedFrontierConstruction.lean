import Mettapedia.GraphTheory.FourColor.FrontierCell
import Mettapedia.GraphTheory.FourColor.ZigzagFrontierRecovery
import Mettapedia.GraphTheory.FourColor.OddCappedTubeSaturation

/-!
# Colourings of a family with changing frontier width

The pieces here are literal open tangles. A split attaches one cubic vertex;
a merge attaches a vertex to two boundary ports. Sufficiently many actual
zigzag rings after each split preserve coverage of every nonconstant,
nonzero, zero-sum word. Merges already cover every admissible output word.
A cell, consisting of a split and a merge of a fresh port with its old
neighbour, restores every admissible word without intervening rings.

The construction has no global width bound. It does not assert that arbitrary
planar maps admit this construction or contain the required ring buffers.
Spherical validity of the generated rotation systems is not asserted here.
Merges may create parallel edges; simplicity and normal form are separate
geometric properties, not conclusions of the colouring theorem.
-/

namespace Mettapedia.GraphTheory.FourColor.BufferedFrontierConstruction

open BoundaryWordFrontier ZigzagRing GoertzelV24CorridorPumping
open TubeSlab.VertexTransfer VertexCodePartition VertexCodeRealization
open TwoSidedBoundaryReindex

noncomputable section

abbrev Piece (k : Nat) := HiddenTangle (Fin 0) (Fin k)

def Supported {k : Nat} (T : Piece k) (w : Fin k → Color) : Prop :=
  T.Accepts Fin.elim0 w

def Adequate {k : Nat} (T : Piece k) : Prop :=
  ∀ w : Fin k → Color, Required w → Supported T w

def addVertex {l r : Nat} (a : Code l r) (ha : VertexCodePartition.Valid a)
    (T : Piece l) : Piece r := ⟨_, _, attach a ha T.data⟩

theorem supported_addVertex_iff {l r : Nat} (a : Code l r)
    (ha : VertexCodePartition.Valid a) (T : Piece l) (w : Fin r → Color) :
    Supported (addVertex a ha T) w ↔ ∃ x, Supported T x ∧ CodeAccepts a x w :=
  supports_attach_iff a ha T.data w

def split (n : Nat) (T : Piece (n + 1)) : Piece (n + 2) :=
  addVertex (splitCode n) (splitCode_valid n) T

def merge (n : Nat) (T : Piece (n + 2)) : Piece (n + 1) :=
  addVertex (mergeCode n) (mergeCode_valid n) T

def rings (k : Nat) [NeZero k] : Piece k → Nat → Piece k
  | T, 0 => T
  | T, r + 1 => rings k (HiddenTangle.appendRing k T) r

theorem rings_support_of_transfer (k : Nat) [NeZero k] {r : Nat}
    {x y : Fin k → Color} (h : ExactRelationalTransfer (Step k) r x y) :
    ∀ T : Piece k, Supported T x → Supported (rings k T r) y := by
  induction h with
  | zero => intro T hx; exact hx
  | @succ r x z y hstep htail ih =>
    intro T hx
    exact ih (HiddenTangle.appendRing k T)
      ((HiddenTangle.appendRing_accepts_iff k T Fin.elim0 z).mpr ⟨x, hx, hstep⟩)

/-- A merge supplies all admissible outputs, including constant ones. -/
theorem merge_support (n : Nat) (T : Piece (n + 2)) (hT : Adequate T)
    (w : Fin (n + 1) → Color) (hw : Admissible w) : Supported (merge n T) w := by
  obtain ⟨x, hx, hne, heq⟩ := exists_required_expansion w hw
  exact (supported_addVertex_iff _ _ T w).mpr
    ⟨x, hT x hx, (merge_accepts_iff n x w hx.1.1).mpr ⟨hne, heq⟩⟩

theorem merge_adequate (n : Nat) (T : Piece (n + 2)) (hT : Adequate T) :
    Adequate (merge n T) := fun w hw => merge_support n T hT w hw.1

def cell (n : Nat) (T : Piece (n + 2)) : Piece (n + 2) :=
  addVertex (neighbourMergeCode n) (neighbourMergeCode_valid n) (split (n + 1) T)

/-- The two actual vertex attachments restore all admissible outputs. -/
theorem cell_support (n : Nat) (hn : 1 ≤ n) (T : Piece (n + 2)) (hT : Adequate T)
    (y : Fin (n + 2) → Color) (hy : Admissible y) : Supported (cell n T) y := by
  obtain ⟨x, z, hx, hs, hm⟩ := cell_covers_admissible n hn y hy
  exact (supported_addVertex_iff _ _ _ y).mpr
    ⟨z, (supported_addVertex_iff _ _ T z).mpr ⟨x, hT x hx, hs⟩, hm⟩

def relabel {k : Nat} (T : Piece k) (p : Equiv.Perm (Fin k)) : Piece k :=
  ⟨T.V, T.I, reindex T.data (Equiv.sumCongr (Equiv.refl (Fin 0)) p)⟩

theorem supported_relabel_iff {k : Nat} (T : Piece k) (p : Equiv.Perm (Fin k))
    (w : Fin k → Color) : Supported (relabel T p) (w ∘ p) ↔ Supported T w := by
  have he : (Sum.elim Fin.elim0 w) ∘ Equiv.sumCongr (Equiv.refl (Fin 0)) p =
      Sum.elim Fin.elim0 (w ∘ p) := by
    funext j
    rcases j with j | j
    · exact j.elim0
    · rfl
  have h := accepts_reindex T.data (Equiv.sumCongr (Equiv.refl (Fin 0)) p)
    (Sum.elim Fin.elim0 w)
  rw [he, TwoSidedBoundaryReindex.accepts_iff, TwoSidedBoundaryReindex.accepts_iff] at h
  exact h

theorem relabel_adequate {k : Nat} (T : Piece k) (hT : Adequate T)
    (p : Equiv.Perm (Fin k)) : Adequate (relabel T p) := by
  intro w hw
  have h := (supported_relabel_iff T p (w ∘ p.symm)).mpr
    (hT _ (hw.comp_perm p.symm))
  have he : (w ∘ p.symm) ∘ p = w := by funext i; simp
  rwa [he] at h

/-- A width-dependent sufficient bound, without claiming a sharp formula. -/
def splitBound (n : Nat) (hn : 2 ≤ n) : Nat := Classical.choose (split_recovery n hn)

theorem split_rings_adequate (n : Nat) (hn : 2 ≤ n) (r : Nat)
    (hr : splitBound n hn ≤ r) (T : Piece (n + 1)) (hT : Adequate T) :
    Adequate (rings (n + 2) (split n T) r) := by
  intro y hy
  obtain ⟨z, hza, hz, hne, hpath⟩ := Classical.choose_spec (split_recovery n hn) r hr y hy
  have hs : Supported (split n T) z :=
    (supported_addVertex_iff _ _ T z).mpr
      ⟨contract n z, hT _ hz, (split_accepts_iff n _ z hza.1).mpr ⟨hne, rfl⟩⟩
  exact rings_support_of_transfer (n + 2) hpath _ hs

def initialCode : Code 0 3 := (fun i => Sum.inr i, fun _ => none)

theorem initialCode_valid : VertexCodePartition.Valid initialCode := by
  constructor
  · intro i j h; exact Sum.inr.inj h
  constructor
  · intro j; exact ⟨fun _ => ⟨j, rfl⟩, fun _ => rfl⟩
  constructor
  · intro i; exact i.elim0
  · intro j k i; exact i.elim0

def initialStar : Piece 3 := ⟨_, _, initial initialCode initialCode_valid⟩

theorem initialStar_adequate : Adequate initialStar := by
  intro w hw
  apply (initial_support initialCode initialCode_valid w).mpr
  refine ⟨fun i => i.elim0, hw.1.1, ?_, ?_⟩
  · have ht : ∀ w : Fin 3 → Color, Admissible w →
        ∀ i j : Fin 3, w i = w j → i = j := by
      unfold Admissible
      decide +kernel
    exact ht w hw.1
  · intro j i; exact i.elim0

/-- An odd capped tube is another concrete source for the same invariant. -/
def oddTube (k : Nat) [NeZero k] (hk : 2 ≤ k) (r : Nat) : Piece k :=
  let T := CycleCap.cappedTube k hk r
  ⟨T.V, T.I, reindex T.data (Equiv.sumCongr (Equiv.equivEmpty (Fin 0)) (Equiv.refl _))⟩

theorem oddTube_eventually_adequate (k : Nat) [NeZero k]
    (hk : 2 ≤ k) (hk3 : 3 ≤ k) (hodd : Odd k) :
    ∃ R, ∀ r, R ≤ r → Adequate (oddTube k hk r) := by
  obtain ⟨R, hR⟩ := CycleCap.odd_cappedTube_eventually_full k hk hk3 hodd
  refine ⟨R, ?_⟩
  intro r hr w hw
  have h := (accepts_iff _ Empty.elim w).mpr (hR r hr w hw.1.1 hw.1.2)
  have h' := (accepts_reindex _
    (Equiv.sumCongr (Equiv.equivEmpty (Fin 0)) (Equiv.refl (Fin k))) _).mpr h
  have he : (Sum.elim Empty.elim w) ∘
      (Equiv.sumCongr (Equiv.equivEmpty (Fin 0)) (Equiv.refl (Fin k))) =
      Sum.elim Fin.elim0 w := by
    funext p
    rcases p with p | p
    · exact p.elim0
    · rfl
  rw [he] at h'
  exact (accepts_iff _ Fin.elim0 w).mp h'

def capBound (k : Nat) [NeZero k] (hk : 2 ≤ k) (hk3 : 3 ≤ k) (hodd : Odd k) : Nat :=
  Classical.choose (oddTube_eventually_adequate k hk hk3 hodd)

inductive Built : {k : Nat} → Piece k → Prop where
  | start : Built initialStar
  | cap {k : Nat} [NeZero k] (hk : 2 ≤ k) (hk3 : 3 ≤ k) (hodd : Odd k)
      (r : Nat) (hr : capBound k hk hk3 hodd ≤ r) : Built (oddTube k hk r)
  | split {n : Nat} (hn : 2 ≤ n) {T : Piece (n + 1)} (before : Built T)
      (r : Nat) (hr : splitBound n hn ≤ r) : Built (rings (n + 2) (split n T) r)
  | merge {n : Nat} (hn : 2 ≤ n) {T : Piece (n + 2)} (before : Built T) :
      Built (merge n T)
  | cell {n : Nat} (hn : 1 ≤ n) {T : Piece (n + 2)} (before : Built T) :
      Built (cell n T)
  | rotate {k : Nat} [NeZero k] {T : Piece k} (before : Built T) (j : Fin k) :
      Built (relabel T (Equiv.addRight j))

/-- Every piece in the family supports every nonconstant admissible word. -/
theorem Built.adequate {k : Nat} {T : Piece k} (h : Built T) : Adequate T := by
  induction h with
  | start => exact initialStar_adequate
  | cap hk hk3 hodd r hr =>
    exact Classical.choose_spec (oddTube_eventually_adequate _ hk hk3 hodd) r hr
  | split hn _ r hr ih => exact split_rings_adequate _ hn r hr _ ih
  | merge _ _ ih => exact merge_adequate _ _ ih
  | cell hn _ ih => exact fun w hw => cell_support _ hn _ ih w hw.1
  | rotate _ j ih => exact relabel_adequate _ ih (Equiv.addRight j)

/-- The family reaches every width at least three. -/
theorem exists_built_width (n : Nat) : ∃ T : Piece (n + 3), Built T := by
  induction n with
  | zero => exact ⟨initialStar, .start⟩
  | succ n ih =>
    obtain ⟨T, hT⟩ := ih
    exact ⟨_, .split (n := n + 2) (by omega) hT (splitBound (n + 2) (by omega)) le_rfl⟩

def closingCode : Code 3 0 := (fun i => Sum.inl i, Fin.elim0)

theorem closingCode_valid : VertexCodePartition.Valid closingCode := by
  constructor
  · intro i j h; exact Sum.inl.inj h
  constructor
  · intro j; exact j.elim0
  constructor
  · intro i; exact ⟨fun _ j => j.elim0, fun _ => ⟨i, rfl⟩⟩
  · intro j; exact j.elim0

def close (T : Piece 3) : Piece 0 := addVertex closingCode closingCode_valid T

/-- Closing a constructed three-port piece gives a colouring of the actual
closed object. The witness includes all interior edges. -/
theorem Built.closed_colourable {T : Piece 3} (h : Built T) :
    ∃ c, (close T).data.IsTaitColoring c := by
  let w : Fin 3 → Color := ![red, blue, purple]
  have hw : Required w := by unfold Required Admissible Nonconstant w; decide +kernel
  have hc : CodeAccepts closingCode w Fin.elim0 := by
    refine ⟨hw.1.1, fun i => i.elim0, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [closingCode, w, red, blue, purple]
    · intro j; exact j.elim0
  obtain ⟨c, hc, _, _⟩ := (supported_addVertex_iff _ _ T Fin.elim0).mpr
    ⟨w, h.adequate w hw, hc⟩
  exact ⟨c, hc⟩

end
end Mettapedia.GraphTheory.FourColor.BufferedFrontierConstruction
