import Mettapedia.GraphTheory.FourColor.GoertzelV24HexagonPenroseGaugeAdversary
import Mettapedia.AutoBooks.GraphTheory.Diestel.Ch01Sec07ContractionMinors

/-!
# The gauge adversary is a crossed pentagon--leaf tensor

The sixty-state positive tensor from
`GoertzelV24HexagonPenroseGaugeAdversary` is not an arbitrary point of the
pairing cone.  It is the exact extension-count tensor of a six-vertex
trivalent network: a pentagon with one pendant vertex.  In cyclic port order
the attachment vertices are

`[3, 0, 2, 4, 5, 5]`.

That order is not the boundary order of a disc embedding of this network.
After adjoining the boundary six-cycle, the resulting twelve-vertex graph
contains a `K_{3,3}` minor.  Thus this example isolates the datum lost by the
pairing-cone relaxation: the three colour-pair webs must arise jointly in one
cofacial plane trivalent network.

The minor certificate below uses only the sound branch-set definition from
the generic graph-theory library.  It deliberately does not use the legacy
`Mettapedia.GraphTheory.IsPlanar`, whose old face carrier was too weak.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexagonCrossedPentagonLeafAdversary

open SimpleGraph
open GoertzelV24RawNooseCountPumping
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24HexagonPersistentKempeAdversary
open GoertzelV24HexagonPenroseGaugeAdversary
open GoertzelV24HexCellPortTangle

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## Exact colouring tensor -/

/-- Colours of the six internal edges, in the order
`01, 04, 12, 15, 23, 34`. -/
abbrev PentagonLeafInternalColoring := Fin 6 → Color

/-- Exact extension predicate for the abstract pentagon--leaf network.

The internal edges are `01, 04, 12, 15, 23, 34`.  Boundary ports
`0,...,5`, in their prescribed cyclic order, attach at vertices
`3,0,2,4,5,5`. -/
def IsCrossedPentagonLeafExtension
    (word : HexagonTaitWord) (x : PentagonLeafInternalColoring) : Prop :=
  ProperColorTriple (x 0) (x 1) (word 1).1 ∧
  ProperColorTriple (x 0) (x 2) (x 3) ∧
  ProperColorTriple (x 2) (x 4) (word 2).1 ∧
  ProperColorTriple (x 4) (x 5) (word 0).1 ∧
  ProperColorTriple (x 1) (x 5) (word 3).1 ∧
  ProperColorTriple (x 3) (word 4).1 (word 5).1
  deriving Decidable

/-- The two possible orientations at the degree-three vertex adjacent to the
leaf.  Once this choice is made, local Tait flow forces every other internal
edge around the pentagon. -/
def crossedPentagonLeafCandidate
    (word : HexagonTaitWord) (swap : Bool) :
    PentagonLeafInternalColoring :=
  let e01 := if swap then (word 5).1 else (word 4).1
  let e12 := if swap then (word 4).1 else (word 5).1
  let e15 := (word 4).1 + (word 5).1
  let e23 := e12 + (word 2).1
  let e34 := e23 + (word 0).1
  let e04 := e34 + (word 3).1
  ![e01, e04, e12, e15, e23, e34]

/-- The valid orientations among the two forced candidates. -/
def crossedPentagonLeafCandidates (word : HexagonTaitWord) : Finset Bool :=
  Finset.univ.filter fun swap =>
    IsCrossedPentagonLeafExtension word
      (crossedPentagonLeafCandidate word swap)

@[simp] theorem mem_crossedPentagonLeafCandidates_iff
    {word : HexagonTaitWord} {swap : Bool} :
    swap ∈ crossedPentagonLeafCandidates word ↔
      IsCrossedPentagonLeafExtension word
        (crossedPentagonLeafCandidate word swap) := by
  simp [crossedPentagonLeafCandidates]

private theorem sum_eq_zero_of_proper {a b c : Color}
    (h : ProperColorTriple a b c) : a + b + c = 0 :=
  (pairwise_ne_iff_sum_eq_zero_of_ne_zero h.1 h.2.1 h.2.2.1).1
    ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem first_eq_add_of_proper {a b c : Color}
    (h : ProperColorTriple a b c) : a = b + c := by
  have hz := sum_eq_zero_of_proper h
  calc
    a = a + 0 := by simp
    _ = a + (a + b + c) := by rw [hz]
    _ = (a + a) + (b + c) := by abel
    _ = b + c := by rw [color_add_self, zero_add]

private theorem second_eq_add_of_proper {a b c : Color}
    (h : ProperColorTriple a b c) : b = a + c := by
  have hz := sum_eq_zero_of_proper h
  calc
    b = b + 0 := by simp
    _ = b + (a + b + c) := by rw [hz]
    _ = (b + b) + (a + c) := by abel
    _ = a + c := by rw [color_add_self, zero_add]

private theorem third_eq_add_of_proper {a b c : Color}
    (h : ProperColorTriple a b c) : c = a + b := by
  have hz := sum_eq_zero_of_proper h
  calc
    c = c + 0 := by simp
    _ = c + (a + b + c) := by rw [hz]
    _ = (c + c) + (a + b) := by abel
    _ = a + b := by rw [color_add_self, zero_add]

/-- Two unordered pairs of distinct nonzero Klein colours with equal sums
are the same unordered pair. -/
private theorem pair_eq_or_swap_of_add_eq
    {a b c d : Color}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hab : a ≠ b) (hcd : c ≠ d) (hsum : a + b = c + d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a ha with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hb with rfl | rfl | rfl <;>
      rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hc with rfl | rfl | rfl <;>
        rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero d hd with rfl | rfl | rfl <;>
          simp_all

/-- Every proper colouring of the abstract network is one of the two forced
candidates.  This is the non-enumerative reason the finite census is small. -/
theorem extension_eq_crossedPentagonLeafCandidate
    {word : HexagonTaitWord} {x : PentagonLeafInternalColoring}
    (hx : IsCrossedPentagonLeafExtension word x) :
    ∃ swap : Bool, x = crossedPentagonLeafCandidate word swap := by
  rcases hx with ⟨h0, h1, h2, h3, h4, h5⟩
  have he15 : x 3 = (word 4).1 + (word 5).1 :=
    first_eq_add_of_proper h5
  have he01e12 : x 0 + x 2 = (word 4).1 + (word 5).1 := by
    rw [← he15]
    exact (third_eq_add_of_proper h1).symm
  have horient :
      (x 0 = (word 4).1 ∧ x 2 = (word 5).1) ∨
        (x 0 = (word 5).1 ∧ x 2 = (word 4).1) :=
    pair_eq_or_swap_of_add_eq h1.1 h1.2.1 (word 4).2 (word 5).2
      h1.2.2.2.1 h5.2.2.2.2.2 he01e12
  have he23 : x 4 = x 2 + (word 2).1 :=
    second_eq_add_of_proper h2
  have he34 : x 5 = x 4 + (word 0).1 :=
    second_eq_add_of_proper h3
  have he04 : x 1 = x 5 + (word 3).1 :=
    first_eq_add_of_proper h4
  rcases horient with ⟨he01, he12⟩ | ⟨he01, he12⟩
  · refine ⟨false, ?_⟩
    funext edge
    fin_cases edge <;>
      simp [crossedPentagonLeafCandidate, he01, he12, he15, he23, he34, he04]
  · refine ⟨true, ?_⟩
    funext edge
    fin_cases edge <;>
      simp [crossedPentagonLeafCandidate, he01, he12, he15, he23, he34, he04]

/-- Two valid candidate orientations cannot give the same internal
colouring. -/
theorem crossedPentagonLeafCandidate_injective_of_valid
    {word : HexagonTaitWord} {left right : Bool}
    (hleft : IsCrossedPentagonLeafExtension word
      (crossedPentagonLeafCandidate word left))
    (heq : crossedPentagonLeafCandidate word left =
      crossedPentagonLeafCandidate word right) :
    left = right := by
  cases left <;> cases right
  · rfl
  · have h5 := hleft.2.2.2.2.2
    have h45 : (word 4).1 ≠ (word 5).1 := h5.2.2.2.2.2
    have := congrFun heq 0
    simp [crossedPentagonLeafCandidate] at this
    exact (h45 this).elim
  · have h5 := hleft.2.2.2.2.2
    have h45 : (word 4).1 ≠ (word 5).1 := h5.2.2.2.2.2
    have := congrFun heq 0
    simp [crossedPentagonLeafCandidate] at this
    exact (h45 this.symm).elim
  · rfl

/-- The actual extension fibre. -/
abbrev CrossedPentagonLeafExtensionFiber (word : HexagonTaitWord) :=
  {x : PentagonLeafInternalColoring //
    IsCrossedPentagonLeafExtension word x}

noncomputable def chosenOrientation
    {word : HexagonTaitWord}
    (coloring : CrossedPentagonLeafExtensionFiber word) : Bool :=
  Classical.choose (extension_eq_crossedPentagonLeafCandidate coloring.2)

theorem coloring_eq_candidate_chosenOrientation
    {word : HexagonTaitWord}
    (coloring : CrossedPentagonLeafExtensionFiber word) :
    coloring.1 = crossedPentagonLeafCandidate word
      (chosenOrientation coloring) :=
  Classical.choose_spec
    (extension_eq_crossedPentagonLeafCandidate coloring.2)

/-- The two-candidate fibre is equivalent to the full colouring fibre. -/
noncomputable def candidateExtensionEquiv (word : HexagonTaitWord) :
    {swap // swap ∈ crossedPentagonLeafCandidates word} ≃
      CrossedPentagonLeafExtensionFiber word where
  toFun swap :=
    ⟨crossedPentagonLeafCandidate word swap,
      mem_crossedPentagonLeafCandidates_iff.1 swap.2⟩
  invFun coloring := by
    exact ⟨chosenOrientation coloring,
      mem_crossedPentagonLeafCandidates_iff.2 <| by
      rw [← coloring_eq_candidate_chosenOrientation coloring]
      exact coloring.2⟩
  left_inv swap := by
    apply Subtype.ext
    change chosenOrientation ⟨crossedPentagonLeafCandidate word swap, _⟩ = swap
    symm
    apply crossedPentagonLeafCandidate_injective_of_valid
      (mem_crossedPentagonLeafCandidates_iff.1 swap.2)
    exact coloring_eq_candidate_chosenOrientation
      (word := word)
      ⟨crossedPentagonLeafCandidate word swap,
        mem_crossedPentagonLeafCandidates_iff.1 swap.2⟩
  right_inv coloring := by
    apply Subtype.ext
    exact (coloring_eq_candidate_chosenOrientation coloring).symm

/-- Counting the two forced candidates really counts the full internal
colouring fibre. -/
theorem card_extensionFiber_eq_card_candidates (word : HexagonTaitWord) :
    Fintype.card (CrossedPentagonLeafExtensionFiber word) =
      (crossedPentagonLeafCandidates word).card := by
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (candidateExtensionEquiv word).symm

private def threeTaitColors : List TaitColor :=
  [⟨red, red_ne_zero⟩, ⟨blue, blue_ne_zero⟩, ⟨purple, purple_ne_zero⟩]

private theorem mem_threeTaitColors (color : TaitColor) :
    color ∈ threeTaitColors := by
  rcases color with ⟨color, hcolor⟩
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero color hcolor with
    rfl | rfl | rfl <;> simp [threeTaitColors]

private def tensorRow (a b c d e f : TaitColor) : Bool :=
  let word :=
    GoertzelV24HexagonPairingTargetAwareBoundary.explicitWord a b c d e f
  decide
    ((crossedPentagonLeafCandidates word).card =
        (if persistentAdversaryBool word = true then 1 else 0) ∧
      (crossedPentagonLeafCandidates word).card =
        Int.natAbs (gaugeCorrectedPenroseTensor word))

private def allTensorRows : Bool :=
  threeTaitColors.all fun a =>
    threeTaitColors.all fun b =>
      threeTaitColors.all fun c =>
        threeTaitColors.all fun d =>
          threeTaitColors.all fun e =>
            threeTaitColors.all fun f => tensorRow a b c d e f

private theorem allTensorRows_eq_true_iff :
    allTensorRows = true ↔
      ∀ a b c d e f : TaitColor, tensorRow a b c d e f = true := by
  simp only [allTensorRows, List.all_eq_true]
  constructor
  · intro h a b c d e f
    exact h a (mem_threeTaitColors a)
      b (mem_threeTaitColors b)
      c (mem_threeTaitColors c)
      d (mem_threeTaitColors d)
      e (mem_threeTaitColors e)
      f (mem_threeTaitColors f)
  · intro h a _ b _ c _ d _ e _ f _
    exact h a b c d e f

private theorem allTensorRows_eq_true : allTensorRows = true := by
  decide

private theorem checkedTensorRow (word : HexagonTaitWord) :
    (crossedPentagonLeafCandidates word).card =
        (if persistentAdversaryBool word = true then 1 else 0) ∧
      (crossedPentagonLeafCandidates word).card =
        Int.natAbs (gaugeCorrectedPenroseTensor word) := by
  rw [← GoertzelV24HexagonPairingTargetAwareBoundary.explicitWord_of_word word]
  have hrow := (allTensorRows_eq_true_iff.mp allTensorRows_eq_true)
    (word 0) (word 1) (word 2) (word 3) (word 4) (word 5)
  exact of_decide_eq_true (by simpa [tensorRow] using hrow)

/-- The abstract crossed pentagon--leaf has one extension on every adversary
word and none on any other six-port Tait word. -/
theorem card_crossedPentagonLeafExtensions
    (word : HexagonTaitWord) :
    Fintype.card (CrossedPentagonLeafExtensionFiber word) =
      if word ∈ persistentAdversary then 1 else 0 := by
  rw [card_extensionFiber_eq_card_candidates]
  change (crossedPentagonLeafCandidates word).card =
    if persistentAdversaryBool word = true then 1 else 0
  exact (checkedTensorRow word).1

/-- Exact support equality, with no projection or closure operation. -/
theorem nonempty_crossedPentagonLeafExtensions_iff
    (word : HexagonTaitWord) :
    Nonempty (CrossedPentagonLeafExtensionFiber word) ↔
      word ∈ persistentAdversary := by
  rw [← Fintype.card_pos_iff, card_crossedPentagonLeafExtensions]
  by_cases h : word ∈ persistentAdversary <;> simp [h]

/-- The same census says every supported word has a unique internal
colouring. -/
theorem existsUnique_crossedPentagonLeafExtension_iff
    (word : HexagonTaitWord) :
    (∃! x, IsCrossedPentagonLeafExtension word x) ↔
      word ∈ persistentAdversary := by
  constructor
  · rintro ⟨x, hx, -⟩
    exact (nonempty_crossedPentagonLeafExtensions_iff word).1
      ⟨⟨x, hx⟩⟩
  · intro hword
    have hcard : Fintype.card (CrossedPentagonLeafExtensionFiber word) = 1 := by
      rw [card_crossedPentagonLeafExtensions, if_pos hword]
    obtain ⟨x, hunique⟩ := Fintype.card_eq_one_iff.mp hcard
    refine ⟨x.1, x.2, ?_⟩
    intro y hy
    have : (⟨y, hy⟩ : CrossedPentagonLeafExtensionFiber word) = x :=
      hunique ⟨y, hy⟩
    exact congrArg Subtype.val this

/-- The gauge-corrected pairing-kernel tensor is exactly the number of
extensions of the crossed pentagon--leaf network. -/
theorem gaugeCorrectedPenroseTensor_eq_extensionCount
    (word : HexagonTaitWord) :
    gaugeCorrectedPenroseTensor word =
      Fintype.card (CrossedPentagonLeafExtensionFiber word) := by
  have hnat := checkedTensorRow word |>.2
  have hnonnegative := gaugeCorrectedPenroseTensor_nonnegative word
  rw [card_extensionFiber_eq_card_candidates]
  omega

/-! ## The prescribed boundary order contains a `K_{3,3}` minor -/

/-- The pentagon--leaf together with one boundary vertex per port and the
boundary six-cycle.  Vertices `0,...,5` are internal and `6,...,11` are the
cyclic boundary vertices. -/
def crossedPentagonLeafBoundaryGraph : SimpleGraph (Fin 12) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(0, 4), s(1, 2), s(1, 5), s(2, 3), s(3, 4),
      s(3, 6), s(0, 7), s(2, 8), s(4, 9), s(5, 10), s(5, 11),
      s(6, 7), s(7, 8), s(8, 9), s(9, 10), s(10, 11), s(11, 6)} :
      Set (Sym2 (Fin 12)))

instance crossedPentagonLeafBoundaryGraph_adj_decidable :
    DecidableRel crossedPentagonLeafBoundaryGraph.Adj := by
  unfold crossedPentagonLeafBoundaryGraph
  infer_instance

instance k33_adj_decidable :
    DecidableRel (completeBipartiteGraph (Fin 3) (Fin 3)).Adj := by
  rintro (i | j) (i' | j') <;> simp <;> infer_instance

/-- Branch sets for a `K_{3,3}` minor.  Suppressing their internal tree
edges gives left branch vertices `2,6,9` and right branch vertices `3,8,11`. -/
def k33BranchSet : Fin 3 ⊕ Fin 3 → Finset (Fin 12)
  | Sum.inl i =>
      if i = 0 then {1, 2, 5}
      else if i = 1 then {6, 7}
      else {4, 9, 10}
  | Sum.inr j =>
      if j = 0 then {3}
      else if j = 1 then {8}
      else {11}

/-- A finite vertex set is connected when one of its vertices is adjacent to
every other member. -/
private theorem induce_preconnected_of_star
    (G : SimpleGraph (Fin 12)) (vertices : Finset (Fin 12))
    (root : Fin 12) (hroot : root ∈ vertices)
    (hadj : ∀ vertex ∈ vertices, vertex ≠ root → G.Adj root vertex) :
    (G.induce (↑vertices : Set (Fin 12))).Preconnected := by
  intro left right
  let center : {vertex // vertex ∈ vertices} := ⟨root, hroot⟩
  have hleft :
      (G.induce (↑vertices : Set (Fin 12))).Reachable left center := by
    by_cases heq : left.1 = root
    · have : left = center := Subtype.ext heq
      subst left
      exact SimpleGraph.Reachable.refl center
    · exact (show (G.induce (↑vertices : Set (Fin 12))).Adj left center from
        (hadj left.1 left.2 heq).symm).reachable
  have hright :
      (G.induce (↑vertices : Set (Fin 12))).Reachable center right := by
    by_cases heq : right.1 = root
    · have : right = center := Subtype.ext heq
      subst right
      exact SimpleGraph.Reachable.refl center
    · exact (show (G.induce (↑vertices : Set (Fin 12))).Adj center right from
        hadj right.1 right.2 heq).reachable
  exact hleft.trans hright

/-- A fully checked branch-set model of `K_{3,3}` in the graph obtained by
adjoining the prescribed boundary circle. -/
def k33MinorModel :
    AutoBooks.GraphTheory.Diestel.Ch01.MinorModel
      (completeBipartiteGraph (Fin 3) (Fin 3))
      crossedPentagonLeafBoundaryGraph where
  branchSet := k33BranchSet
  branchNonempty := by
    rintro (i | j)
    · fin_cases i <;> decide
    · fin_cases j <;> decide
  branchDisjoint := by
    rintro (i | j) (i' | j') hne
    · fin_cases i <;> fin_cases i' <;> simp_all [k33BranchSet]
    · fin_cases i <;> fin_cases j' <;> simp_all [k33BranchSet]
    · fin_cases j <;> fin_cases i' <;> simp_all [k33BranchSet]
    · fin_cases j <;> fin_cases j' <;> simp_all [k33BranchSet]
  branchConnected := by
    rintro (i | j)
    · fin_cases i
      · change (crossedPentagonLeafBoundaryGraph.induce
          (↑({1, 2, 5} : Finset (Fin 12)) : Set (Fin 12))).Preconnected
        apply induce_preconnected_of_star _ _ 1 (by decide)
        intro vertex hvertex hne
        fin_cases vertex <;> simp_all [crossedPentagonLeafBoundaryGraph]
      · change (crossedPentagonLeafBoundaryGraph.induce
          (↑({6, 7} : Finset (Fin 12)) : Set (Fin 12))).Preconnected
        apply induce_preconnected_of_star _ _ 6 (by decide)
        intro vertex hvertex hne
        fin_cases vertex <;> simp_all [crossedPentagonLeafBoundaryGraph]
      · change (crossedPentagonLeafBoundaryGraph.induce
          (↑({4, 9, 10} : Finset (Fin 12)) : Set (Fin 12))).Preconnected
        apply induce_preconnected_of_star _ _ 9 (by decide)
        intro vertex hvertex hne
        fin_cases vertex <;> simp_all [crossedPentagonLeafBoundaryGraph]
    · fin_cases j
      · change (crossedPentagonLeafBoundaryGraph.induce
          (↑({3} : Finset (Fin 12)) : Set (Fin 12))).Preconnected
        apply induce_preconnected_of_star _ _ 3 (by decide)
        intro vertex hvertex hne
        fin_cases vertex <;> simp_all
      · change (crossedPentagonLeafBoundaryGraph.induce
          (↑({8} : Finset (Fin 12)) : Set (Fin 12))).Preconnected
        apply induce_preconnected_of_star _ _ 8 (by decide)
        intro vertex hvertex hne
        fin_cases vertex <;> simp_all
      · change (crossedPentagonLeafBoundaryGraph.induce
          (↑({11} : Finset (Fin 12)) : Set (Fin 12))).Preconnected
        apply induce_preconnected_of_star _ _ 11 (by decide)
        intro vertex hvertex hne
        fin_cases vertex <;> simp_all
  branchAdj := by
    rintro (i | j) (i' | j') hadj
    · simp at hadj
    · fin_cases i <;> fin_cases j' <;>
        simp only [k33BranchSet] <;> decide
    · fin_cases j <;> fin_cases i' <;>
        simp only [k33BranchSet] <;> decide
    · simp at hadj

/-- Consumer-facing obstruction: the graph obtained by adjoining the
prescribed boundary circle contains `K_{3,3}` as a genuine graph minor. -/
theorem k33_isMinor_crossedPentagonLeafBoundaryGraph :
    AutoBooks.GraphTheory.Diestel.Ch01.IsMinor
      (completeBipartiteGraph (Fin 3) (Fin 3))
      crossedPentagonLeafBoundaryGraph :=
  ⟨k33MinorModel⟩

/-- Combined exact diagnosis of the linear Penrose-cone adversary. -/
theorem persistentAdversary_is_crossedPentagonLeafTensor_with_k33Minor :
    (∀ word : HexagonTaitWord,
      gaugeCorrectedPenroseTensor word =
        Fintype.card (CrossedPentagonLeafExtensionFiber word)) ∧
    AutoBooks.GraphTheory.Diestel.Ch01.IsMinor
      (completeBipartiteGraph (Fin 3) (Fin 3))
      crossedPentagonLeafBoundaryGraph :=
  ⟨gaugeCorrectedPenroseTensor_eq_extensionCount,
    k33_isMinor_crossedPentagonLeafBoundaryGraph⟩

end GoertzelV24HexagonCrossedPentagonLeafAdversary

end Mettapedia.GraphTheory.FourColor
