import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-!
# The four-block-edge Lift criterion, abstractly

The Lift step for one annular tangle rests on two facts that have nothing to do
with colourings, and both are proved here in full generality.

*Four edges of a five-cycle span.*  At most one block-cycle edge is missing, and
the remaining four form a path through all five blocks, so the block graph is
connected however the missing edge is chosen.

*Fibre connectivity lifts base paths.*  If every fibre of a projection is
connected by moves, and every base edge is realized by at least one move between
the fibres it joins, then the total space is connected whenever the base is.
The routing is exactly the manuscript's: move inside the current fibre to the
state that witnesses the next base edge, take that move, and continue.

Composing them gives the criterion.  The two within-fibre connectivity
hypotheses and the four-edge hypothesis stay hypotheses -- they are what the
finite audits provide evidence for, and this file does not prove them.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FourBlockEdgeLift

/-! ## Four edges of a five-cycle span it -/

/-- One step along an installed block-cycle edge.  Edge `e` joins blocks `e` and
`e+1`, and is available when it lies in the realized set `E`. -/
def BlockStep (E : Finset (Fin 5)) (i j : Fin 5) : Prop :=
  (j = i + 1 ∧ i ∈ E) ∨ (i = j + 1 ∧ j ∈ E)

/-- Connectivity of the block cycle through the installed edges. -/
def BlockConn (E : Finset (Fin 5)) : Fin 5 → Fin 5 → Prop :=
  Relation.ReflTransGen (BlockStep E)

theorem blockStep_symm {E : Finset (Fin 5)} {i j : Fin 5} (h : BlockStep E i j) :
    BlockStep E j i := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩

theorem blockConn_symm {E : Finset (Fin 5)} {i j : Fin 5} (h : BlockConn E i j) :
    BlockConn E j i := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (blockStep_symm hstep)) ih

/-- With four of the five edges installed, at most one is missing. -/
theorem exists_missing_edge {E : Finset (Fin 5)} (hcard : 4 ≤ E.card) :
    ∃ m : Fin 5, ∀ e : Fin 5, e ≠ m → e ∈ E := by
  classical
  have hcompl : Eᶜ.card ≤ 1 := by
    have := Finset.card_add_card_compl E
    simp only [Fintype.card_fin] at this
    omega
  rcases Finset.card_le_one.mp hcompl with hone
  by_cases hempty : Eᶜ = ∅
  · refine ⟨0, fun e _ => ?_⟩
    by_contra hcontra
    exact absurd (Finset.mem_compl.mpr hcontra) (by simp [hempty])
  · obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    refine ⟨m, fun e hne => ?_⟩
    by_contra hcontra
    exact hne (hone e (Finset.mem_compl.mpr hcontra) m hm)

private theorem fin5_offsets (m i : Fin 5) :
    i = m ∨ i = m + 1 ∨ i = m + 2 ∨ i = m + 3 ∨ i = m + 4 := by
  revert m i; decide

private theorem fin5_offset_ne (m : Fin 5) {k : Fin 5} (hk : k ≠ 0) : m + k ≠ m := by
  revert hk; revert m k; decide

private theorem fin5_succ_offset (m : Fin 5) (k : Fin 5) : m + k + 1 = m + (k + 1) := by
  revert m k; decide

private theorem fin5_wrap_five (m : Fin 5) : m + (4 + 1 : Fin 5) = m := by
  revert m; decide

/-- **Four edges of the five-cycle span it.**  Every block is reachable from the
block just past the missing edge, along the four installed edges. -/
theorem blockConn_of_four_edges {E : Finset (Fin 5)} (hcard : 4 ≤ E.card)
    (i j : Fin 5) : BlockConn E i j := by
  obtain ⟨m, hm⟩ := exists_missing_edge hcard
  -- one step along each installed edge of the spanning path
  have hstep : ∀ k : Fin 5, k ≠ 0 → BlockStep E (m + k) (m + k + 1) := by
    intro k hk
    exact Or.inl ⟨rfl, hm _ (fin5_offset_ne m hk)⟩
  have h1 : BlockConn E (m + 1) (m + 2) := by
    have := hstep 1 (by decide)
    rw [fin5_succ_offset m 1] at this
    exact Relation.ReflTransGen.single (by simpa using this)
  have h2 : BlockConn E (m + 2) (m + 3) := by
    have := hstep 2 (by decide)
    rw [fin5_succ_offset m 2] at this
    exact Relation.ReflTransGen.single (by simpa using this)
  have h3 : BlockConn E (m + 3) (m + 4) := by
    have := hstep 3 (by decide)
    rw [fin5_succ_offset m 3] at this
    exact Relation.ReflTransGen.single (by simpa using this)
  have h4 : BlockConn E (m + 4) m := by
    have := hstep 4 (by decide)
    rw [fin5_succ_offset m 4] at this
    rw [fin5_wrap_five m] at this
    exact Relation.ReflTransGen.single this
  -- every block reaches the head of the spanning path
  have hreach : ∀ k : Fin 5, BlockConn E (m + 1) k := by
    intro k
    rcases fin5_offsets m k with rfl | rfl | rfl | rfl | rfl
    · exact ((h1.trans h2).trans h3).trans h4
    · exact Relation.ReflTransGen.refl
    · exact h1
    · exact h1.trans h2
    · exact (h1.trans h2).trans h3
  exact (blockConn_symm (hreach i)).trans (hreach j)

/-! ## Fibre connectivity lifts base paths -/

section Lift

variable {S B : Type*}

/-- **The lift.**  With connected fibres and every base edge realized by some
move, a connected base makes the whole state space connected.

`hfibre` is the within-fibre hypothesis, `hedge` says a base edge is witnessed by
an actual move between the two fibres, and `hbase` is base connectivity. -/
theorem reflTransGen_of_fibre_connected
    {proj : S → B} {Step : S → S → Prop} {BaseStep : B → B → Prop}
    (hfibre : ∀ s t : S, proj s = proj t → Relation.ReflTransGen Step s t)
    (hedge : ∀ b b' : B, BaseStep b b' →
      ∃ s t : S, proj s = b ∧ proj t = b' ∧ Step s t)
    {s t : S} (hbase : Relation.ReflTransGen BaseStep (proj s) (proj t)) :
    Relation.ReflTransGen Step s t := by
  -- carry a state reached so far, lying over the current base point
  have key : ∀ b : B, Relation.ReflTransGen BaseStep (proj s) b →
      ∃ u : S, Relation.ReflTransGen Step s u ∧ proj u = b := by
    intro b hb
    induction hb with
    | refl => exact ⟨s, Relation.ReflTransGen.refl, rfl⟩
    | tail _ hstep ih =>
        obtain ⟨u, hsu, hproj⟩ := ih
        obtain ⟨x, y, hx, hy, hxy⟩ := hedge _ _ hstep
        exact ⟨y, (hsu.trans (hfibre u x (hproj.trans hx.symm))).tail hxy, hy⟩
  obtain ⟨u, hsu, hproj⟩ := key (proj t) hbase
  exact hsu.trans (hfibre u t hproj)

end Lift

/-! ## The criterion -/

/-- **The four-block-edge Lift criterion.**  Connected fibres, connected blocks,
and four of the five block-cycle edges realized put every state in one class.

The three hypotheses are exactly the manuscript's, and none of them is proved
here: they are what the finite audits give evidence for. -/
theorem oneClass_of_fourBlockEdges {S : Type*}
    {proj : S → Fin 5} {Step : S → S → Prop} {E : Finset (Fin 5)}
    (hfibre : ∀ s t : S, proj s = proj t → Relation.ReflTransGen Step s t)
    (hedge : ∀ b b' : Fin 5, BlockStep E b b' →
      ∃ s t : S, proj s = b ∧ proj t = b' ∧ Step s t)
    (hcard : 4 ≤ E.card) (s t : S) :
    Relation.ReflTransGen Step s t :=
  reflTransGen_of_fibre_connected hfibre hedge
    (blockConn_of_four_edges hcard (proj s) (proj t))

/-! ## The word layer

The criterion above collapses the word layer into the block projection, which
silently assumes that two states over the same *block* are connected.  The
manuscript does not assume that; it derives it, from within-block word
connectivity together with fixed-word fibre connectivity.

That derivation is the same generic lift applied one level down, with words as
the base and fixed-word fibres above them.  So the criterion is two nested
applications of one theorem: words over blocks, and states over words. -/

section WordLayer

variable {S W : Type*}

/-- **Same-block states are connected -- derived, not assumed.**  Within a block
the realized words are connected by witnessed moves, and every fixed-word fibre
is connected, so the generic lift applies at the word layer. -/
theorem sameBlock_reflTransGen
    {word : S → W} {blk : W → Fin 5} {Step : S → S → Prop}
    {WithinBlockStep : W → W → Prop}
    (hfibre : ∀ s t : S, word s = word t → Relation.ReflTransGen Step s t)
    (hwitness : ∀ w w' : W, WithinBlockStep w w' →
      ∃ s t : S, word s = w ∧ word t = w' ∧ Step s t)
    (hblockConn : ∀ w w' : W, blk w = blk w' →
      Relation.ReflTransGen WithinBlockStep w w')
    {s t : S} (hsame : blk (word s) = blk (word t)) :
    Relation.ReflTransGen Step s t :=
  reflTransGen_of_fibre_connected hfibre hwitness (hblockConn _ _ hsame)

/-- **The four-block-edge Lift criterion, with the word layer intact.**

The three hypotheses are the manuscript's, in order: every fixed-word fibre is
connected (`hfibre`); within each block the realized words are connected by
moves that are actually witnessed (`hwitness`, `hblockConn`); and at least four
of the five adjacent block edges are realized (`hedge`, `hcard`).

Same-block connectivity is not among them -- it is derived. -/
theorem oneClass_of_fourBlockEdges_word
    {word : S → W} {blk : W → Fin 5} {Step : S → S → Prop}
    {WithinBlockStep : W → W → Prop} {E : Finset (Fin 5)}
    (hfibre : ∀ s t : S, word s = word t → Relation.ReflTransGen Step s t)
    (hwitness : ∀ w w' : W, WithinBlockStep w w' →
      ∃ s t : S, word s = w ∧ word t = w' ∧ Step s t)
    (hblockConn : ∀ w w' : W, blk w = blk w' →
      Relation.ReflTransGen WithinBlockStep w w')
    (hedge : ∀ b b' : Fin 5, BlockStep E b b' →
      ∃ s t : S, blk (word s) = b ∧ blk (word t) = b' ∧ Step s t)
    (hcard : 4 ≤ E.card) (s t : S) :
    Relation.ReflTransGen Step s t :=
  reflTransGen_of_fibre_connected
    (proj := fun x => blk (word x))
    (fun _ _ h => sameBlock_reflTransGen hfibre hwitness hblockConn h)
    hedge
    (blockConn_of_four_edges hcard _ _)

end WordLayer

end GoertzelV24FourBlockEdgeLift

end Mettapedia.GraphTheory.FourColor
