import Mettapedia.GraphTheory.Kempe.Boundary
import Mettapedia.GraphTheory.FourColor.GoertzelLemma814GraphFidelity
import Mettapedia.GraphTheory.Kempe.TauGadgetClosure

/-!
# The canonical three-cell gadget on the generic Kempe layer

The audit of Lemma 8.14 certifies a list model: 192 gadget states, a
breadth-first two-colour component `tauComponent`, and certified moves
`specifiedKempeStep`.  This file identifies that model with genuine Kempe
dynamics.

The gadget's edge colourings are the vertex colourings of its line graph
`tauLineGraph`, whose vertices are the thirteen edges and whose adjacency is
sharing an internal vertex.  (The line graph is used rather than
`EdgeColoring` of a simple graph because gluing gadgets in series creates
parallel edges; the line graph of such a composite is still simple.)

* every colouring of `tauLineGraph` is the colour function of a listed state,
  and conversely (`exists_state`, `stateColoring`);
* for a listed state and a listed colour pair, the breadth-first component of a
  seed is exactly the Kempe component of that seed
  (`tauComponent_eq_kempeComponentSet`);
* a certified move is a genuine Kempe switch avoiding the input stubs
  (`specifiedKempeStep_kempeStepAvoiding`);
* **Lemma 8.14 on the line graph:** `tauLineGraph.FibreConnected LColor tauInputSet`;
* **Lemma 8.15 on the line graph:** every colouring is transparent relative to
  the stub edges, `tauLineGraph.Transparent LColor tauStubSet`.
-/

namespace Mettapedia.GraphTheory.Kempe.TauGadget

open SimpleGraph Relation
open Mettapedia.Combinatorics.Reconfiguration
open Mettapedia.GraphTheory.FourColor
open GoertzelLemma814 GoertzelLemma814GraphFidelity

/-! ## The line graph and its colourings -/

/-- The line graph of the gadget: two edges are adjacent when they share an
internal vertex. -/
def tauLineGraph : SimpleGraph TauEdge where
  Adj e f := shareInternalVertex e f = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel tauLineGraph.Adj := fun e f =>
  inferInstanceAs (Decidable (shareInternalVertex e f = true))

theorem pairwiseDistinct3_iff (x y z : LColor) :
    pairwiseDistinct3 x y z = true ↔ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  cases x <;> cases y <;> cases z <;> decide

/-- Incidence properness gives properness on the line graph. -/
theorem color_ne_of_adj {C : TauEdge → LColor} (hC : tauIncidenceProperColoringCheck C = true)
    {e f : TauEdge} (h : tauLineGraph.Adj e f) : C e ≠ C f := by
  change shareInternalVertex e f = true at h
  unfold shareInternalVertex at h
  split_ifs at h with hef
  obtain ⟨v, hv, hvef⟩ := List.any_eq_true.1 h
  have hCv := List.all_eq_true.1 hC v hv
  simp only [Bool.and_eq_true, List.contains_iff_mem] at hvef
  obtain ⟨he, hf⟩ := hvef
  cases v <;> simp only [incidentEdges, List.mem_cons, List.not_mem_nil, or_false] at he hf <;>
    simp only [incidentEdges] at hCv <;> rw [pairwiseDistinct3_iff] at hCv <;>
    rcases he with rfl | rfl | rfl <;> rcases hf with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hef
    | exact hCv.1
    | exact hCv.2.1
    | exact hCv.2.2
    | exact fun h => hCv.1 h.symm
    | exact fun h => hCv.2.1 h.symm
    | exact fun h => hCv.2.2 h.symm

/-- Properness on the line graph gives incidence properness. -/
theorem incidenceCheck_of_coloring (C : tauLineGraph.Coloring LColor) :
    tauIncidenceProperColoringCheck C = true := by
  unfold tauIncidenceProperColoringCheck
  rw [List.all_eq_true]
  intro v _
  cases v <;> simp only [incidentEdges] <;> rw [pairwiseDistinct3_iff] <;>
    exact ⟨C.valid (by decide), C.valid (by decide), C.valid (by decide)⟩

/-- The line-graph colouring of a properly coloured state. -/
def stateColoring (s : TauState) (hs : tauIncidenceProperColoringCheck s.color = true) :
    tauLineGraph.Coloring LColor :=
  Coloring.mk s.color fun h => color_ne_of_adj hs h

@[simp] theorem stateColoring_apply (s : TauState)
    (hs : tauIncidenceProperColoringCheck s.color = true) (e : TauEdge) :
    stateColoring s hs e = s.color e :=
  rfl

/-- Listed states are properly coloured. -/
theorem check_of_mem {s : TauState} (hs : s ∈ allTauStates) :
    tauIncidenceProperColoringCheck s.color = true :=
  tauIncidenceProperColoring_of_mem_enumeratedTauColorings s.color (List.mem_map_of_mem hs)

set_option maxRecDepth 8192 in
/-- The listed states are the first 192 indexed states. -/
theorem allTauStates_indexed :
    allTauStates.all (fun s => (List.range 192).any fun i => stateAt i == s) = true := by
  decide

set_option maxRecDepth 8192 in
theorem stateAt_mem_allTauStates :
    (List.range 192).all (fun i => allTauStates.contains (stateAt i)) = true := by
  decide

theorem exists_index {s : TauState} (hs : s ∈ allTauStates) :
    ∃ i < 192, stateAt i = s := by
  have h := List.all_eq_true.1 allTauStates_indexed s hs
  obtain ⟨i, hi, heq⟩ := List.any_eq_true.1 h
  exact ⟨i, List.mem_range.1 hi, beq_iff_eq.1 heq⟩

theorem stateAt_mem {i : Nat} (hi : i < 192) : stateAt i ∈ allTauStates :=
  List.contains_iff_mem.1 (List.all_eq_true.1 stateAt_mem_allTauStates i (List.mem_range.2 hi))

/-- **Every colouring of the line graph is a listed state.** -/
theorem exists_state (C : tauLineGraph.Coloring LColor) :
    ∃ i < 192, ∃ hs, C = stateColoring (stateAt i) hs := by
  have hC := incidenceCheck_of_coloring C
  obtain ⟨i, hi, heq⟩ := exists_index (decodeTauState_mem_allTauStates C hC)
  refine ⟨i, hi, check_of_mem (stateAt_mem hi), ?_⟩
  ext e : 1
  rw [stateColoring_apply, heq, decodeTauState_color C hC]

/-- The colouring of the `i`-th listed state (the zeroth one off the list). -/
def idxColoring (i : Nat) : tauLineGraph.Coloring LColor :=
  if h : i < 192 then stateColoring (stateAt i) (check_of_mem (stateAt_mem h))
  else stateColoring (stateAt 0) (check_of_mem (stateAt_mem (by decide)))

theorem idxColoring_of_lt {i : Nat} (h : i < 192) (hs) :
    idxColoring i = stateColoring (stateAt i) hs := by
  rw [idxColoring, dif_pos h]

/-- The four input stubs. -/
def tauInputSet : Set TauEdge := {e | e ∈ tauInputEdges}

/-- The eight stub edges. -/
def tauStubEdges : List TauEdge :=
  [TauEdge.B0, TauEdge.B1, TauEdge.B2, TauEdge.B3,
    TauEdge.B4, TauEdge.B5, TauEdge.B6, TauEdge.B7]

def tauStubSet : Set TauEdge := {e | e ∈ tauStubEdges}

/-! ## The breadth-first component is the Kempe component -/

theorem mem_tauEdges (e : TauEdge) : e ∈ tauEdges := by
  cases e <;> decide

theorem edgeInPair_iff {s : TauState} {a c : LColor} {e : TauEdge} :
    edgeInPair s a c e = true ↔ s.color e = a ∨ s.color e = c := by
  unfold edgeInPair colorInPair
  rw [Bool.or_eq_true, colorEq_eq_true_iff, colorEq_eq_true_iff]

theorem mem_addIfFresh {xs : List TauEdge} {x e : TauEdge} :
    e ∈ addIfFresh xs x ↔ e ∈ xs ∨ e = x := by
  unfold addIfFresh
  split_ifs with h
  · rw [List.contains_iff_mem] at h
    constructor
    · exact Or.inl
    · rintro (h' | rfl)
      · exact h'
      · exact h
  · rw [List.mem_append, List.mem_singleton]

theorem mem_appendFresh {xs ys : List TauEdge} {e : TauEdge} :
    e ∈ appendFresh xs ys ↔ e ∈ xs ∨ e ∈ ys := by
  unfold appendFresh
  induction ys generalizing xs with
  | nil => simp
  | cons y ys ih =>
      rw [List.foldl_cons, ih, mem_addIfFresh, List.mem_cons]
      tauto

theorem mem_nextComponentLayer {s : TauState} {a c : LColor} {seen : List TauEdge}
    {e : TauEdge} :
    e ∈ nextComponentLayer s a c seen ↔
      edgeInPair s a c e = true ∧ e ∉ seen ∧ ∃ f ∈ seen, shareInternalVertex e f = true := by
  unfold nextComponentLayer
  rw [List.mem_filter]
  have hcont : seen.contains e = false ↔ e ∉ seen := by
    rw [← Bool.not_eq_true, List.contains_iff_mem]
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true, hcont]
  constructor
  · rintro ⟨-, ⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨mem_tauEdges e, ⟨h1, h2⟩, h3⟩

theorem subset_closeComponent (s : TauState) (a c : LColor) :
    ∀ (n : Nat) (seen : List TauEdge), ∀ e ∈ seen, e ∈ closeComponent s a c n seen := by
  intro n
  induction n with
  | zero => intro seen e he; exact he
  | succ n ih =>
      intro seen e he
      exact ih _ e (mem_appendFresh.2 (Or.inl he))

section Fidelity

variable {s : TauState} (hs : tauIncidenceProperColoringCheck s.color = true)
  {a c : LColor}

/-- Soundness of the breadth-first search: everything it collects from inside a
Kempe component stays in that component. -/
theorem closeComponent_sound
    (K : ((stateColoring s hs).bicoloredSubgraph a c).ConnectedComponent) :
    ∀ (n : Nat) (seen : List TauEdge),
      (∀ e ∈ seen, e ∈ (stateColoring s hs).kempeComponentSet a c K) →
      ∀ e ∈ closeComponent s a c n seen, e ∈ (stateColoring s hs).kempeComponentSet a c K := by
  intro n
  induction n with
  | zero => intro seen hseen e he; exact hseen e he
  | succ n ih =>
      intro seen hseen
      apply ih
      intro e he
      rcases mem_appendFresh.1 he with he | he
      · exact hseen e he
      · obtain ⟨hpair, -, f, hf, hshare⟩ := mem_nextComponentLayer.1 he
        exact (stateColoring s hs).mem_kempeComponentSet_of_adj (hseen f hf)
          ((show tauLineGraph.Adj e f from hshare).symm) (edgeInPair_iff.1 hpair)

end Fidelity

/-- **The breadth-first component is the Kempe component.** -/
theorem tauComponent_eq_kempeComponentSet {s : TauState} (hmem : s ∈ allTauStates)
    (hs : tauIncidenceProperColoringCheck s.color = true) {a c : LColor}
    (hpair : (a, c) ∈ colorPairs) {seed : TauEdge}
    (hseed : seed ∈ (stateColoring s hs).bicoloredSet a c) :
    {e | e ∈ tauComponent s a c seed} =
      (stateColoring s hs).kempeComponentSet a c
        (((stateColoring s hs).bicoloredSubgraph a c).connectedComponentMk ⟨seed, hseed⟩) := by
  have hpairSeed : edgeInPair s a c seed = true := edgeInPair_iff.2 hseed
  have hcomp : tauComponent s a c seed = closeComponent s a c tauEdges.length [seed] := by
    unfold tauComponent
    rw [if_pos hpairSeed]
  apply Set.Subset.antisymm
  · intro e he
    change e ∈ tauComponent s a c seed at he
    rw [hcomp] at he
    refine closeComponent_sound hs _ _ [seed] ?_ e he
    intro f hf
    rw [List.mem_singleton] at hf
    subst hf
    exact (stateColoring s hs).mem_kempeComponentSet_self hseed
  · apply (stateColoring s hs).kempeComponentSet_subset_of_closed hseed
    · change seed ∈ tauComponent s a c seed
      rw [hcomp]
      exact subset_closeComponent s a c _ [seed] seed (List.mem_singleton_self _)
    · intro u w hu hadj hw
      by_contra hwT
      obtain ⟨i, hi, rfl⟩ := exists_index hmem
      have hclosed := List.all_eq_true.1 (List.all_eq_true.1 (componentsClosedAt_of_lt hi)
        (a, c) hpair) seed (mem_tauEdges seed)
      have hlayer : w ∈ nextComponentLayer (stateAt i) a c (tauComponent (stateAt i) a c seed) :=
        mem_nextComponentLayer.2 ⟨edgeInPair_iff.2 hw, hwT, u, hu, hadj.symm⟩
      rw [List.isEmpty_iff.1 hclosed] at hlayer
      exact List.not_mem_nil hlayer

/-! ## Certified moves are Kempe switches -/

theorem swapColor_eq_swap (a c x : LColor) : swapColor a c x = Equiv.swap a c x := by
  cases a <;> cases c <;> cases x <;> decide

/-- **A certified move is a genuine Kempe switch avoiding the input stubs.** -/
theorem specifiedKempeStep_kempeStepAvoiding {s t : TauState} (hsm : s ∈ allTauStates)
    (htm : t ∈ allTauStates) {move : KempeMove} (hpair : (move.a, move.c) ∈ colorPairs)
    (h : specifiedKempeStep s t move = true) :
    tauLineGraph.KempeStepAvoiding tauInputSet (stateColoring s (check_of_mem hsm))
      (stateColoring t (check_of_mem htm)) := by
  unfold specifiedKempeStep at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hne, havoid⟩, hagree⟩ := h
  have hseedPair : edgeInPair s move.a move.c move.seed = true := by
    by_contra hno
    have hnil : tauComponent s move.a move.c move.seed = [] := by
      unfold tauComponent
      rw [if_neg hno]
    rw [hnil] at hne
    exact absurd hne (by decide)
  have hseed : move.seed ∈ (stateColoring s (check_of_mem hsm)).bicoloredSet move.a move.c :=
    edgeInPair_iff.1 hseedPair
  have hset := tauComponent_eq_kempeComponentSet hsm (check_of_mem hsm) hpair hseed
  refine ⟨move.a, move.c,
    ((stateColoring s (check_of_mem hsm)).bicoloredSubgraph move.a move.c).connectedComponentMk
      ⟨move.seed, hseed⟩, ?_, ?_⟩
  · rw [← hset, Set.disjoint_left]
    intro e he hin
    unfold componentAvoidsInputs at havoid
    rw [Bool.not_eq_true', List.any_eq_false] at havoid
    exact havoid e he (List.contains_iff_mem.2 hin)
  · ext e : 1
    rw [stateColoring_apply]
    have hae := List.all_eq_true.1 hagree e (mem_tauEdges e)
    rw [colorEq_eq_true_iff] at hae
    rw [hae]
    unfold switchedColor
    by_cases he : e ∈ tauComponent s move.a move.c move.seed
    · have heK : e ∈ (stateColoring s (check_of_mem hsm)).kempeComponentSet move.a move.c
          (((stateColoring s (check_of_mem hsm)).bicoloredSubgraph
            move.a move.c).connectedComponentMk ⟨move.seed, hseed⟩) := by
        rw [← hset]; exact he
      rw [if_pos (List.contains_iff_mem.2 he), Coloring.swapOnKempeComponent_apply_of_mem _ heK,
        stateColoring_apply, swapColor_eq_swap]
    · have heK : e ∉ (stateColoring s (check_of_mem hsm)).kempeComponentSet move.a move.c
          (((stateColoring s (check_of_mem hsm)).bicoloredSubgraph
            move.a move.c).connectedComponentMk ⟨move.seed, hseed⟩) := by
        rw [← hset]; exact he
      have hcont : (tauComponent s move.a move.c move.seed).contains e = false := by
        rw [← Bool.not_eq_true, List.contains_iff_mem]; exact he
      rw [hcont, Coloring.swapOnKempeComponent_apply_of_not_mem _ heK, stateColoring_apply]
      rfl

/-- The same for the unspecified single step of the list model. -/
theorem singleKempeStep_kempeStepAvoiding {s t : TauState} (hsm : s ∈ allTauStates)
    (htm : t ∈ allTauStates) (h : singleKempeStep s t = true) :
    tauLineGraph.KempeStepAvoiding tauInputSet (stateColoring s (check_of_mem hsm))
      (stateColoring t (check_of_mem htm)) := by
  unfold singleKempeStep at h
  obtain ⟨pair, hpair, h⟩ := List.any_eq_true.1 h
  obtain ⟨seed, -, h⟩ := List.any_eq_true.1 h
  exact specifiedKempeStep_kempeStepAvoiding hsm htm (move := mv pair.1 pair.2 seed) hpair h

/-! ## Lemma 8.14 on the line graph -/

theorem validRow_of_rowsFrom :
    ∀ (rows : List IndexedPathRow) (k j : Nat), validIndexedRowsFrom k rows = true →
      j < rows.length → validIndexedPathRow (k + j) (rows.getD j default) = true := by
  intro rows
  induction rows with
  | nil => intro k j _ hj; exact absurd hj (Nat.not_lt_zero _)
  | cons r rs ih =>
      intro k j h hj
      simp only [validIndexedRowsFrom, Bool.and_eq_true] at h
      cases j with
      | zero => simpa using h.1
      | succ j =>
          have := ih (k + 1) j h.2 (by simpa using hj)
          simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

theorem reach_of_validSteps :
    ∀ (steps : List IndexedPathStep) (cur rep : Nat), cur < 192 →
      (∀ st ∈ steps, certificateMoveInEncodedDomain st.move = true) →
      validIndexedPathSteps cur steps rep = true →
      rep < 192 ∧ ReflTransGen (tauLineGraph.KempeStepAvoiding tauInputSet)
        (idxColoring cur) (idxColoring rep) := by
  intro steps
  induction steps with
  | nil =>
      intro cur rep hcur _ h
      simp only [validIndexedPathSteps, beq_iff_eq] at h
      subst h
      exact ⟨hcur, ReflTransGen.refl⟩
  | cons st rest ih =>
      intro cur rep hcur hdom h
      simp only [validIndexedPathSteps, Bool.and_eq_true, indexInStateSpace,
        decide_eq_true_eq] at h
      obtain ⟨⟨htarget, hstep⟩, hrest⟩ := h
      have hmove := hdom st List.mem_cons_self
      unfold certificateMoveInEncodedDomain at hmove
      rw [Bool.and_eq_true, List.contains_iff_mem] at hmove
      obtain ⟨hrep, hpath⟩ := ih st.target rep htarget
        (fun st' hst' => hdom st' (List.mem_cons_of_mem _ hst')) hrest
      refine ⟨hrep, ReflTransGen.head ?_ hpath⟩
      rw [idxColoring_of_lt hcur (check_of_mem (stateAt_mem hcur)),
        idxColoring_of_lt htarget (check_of_mem (stateAt_mem htarget))]
      exact specifiedKempeStep_kempeStepAvoiding (stateAt_mem hcur) (stateAt_mem htarget)
        hmove.1 hstep

theorem reach_representative {i : Nat} (hi : i < 192) :
    representativeAt i < 192 ∧ ReflTransGen (tauLineGraph.KempeStepAvoiding tauInputSet)
      (idxColoring i) (idxColoring (representativeAt i)) := by
  have hlen : lemma814PathCertificate.length = 192 := beq_iff_eq.1 lemma814PathCertificate_length_ok
  have hrow := validRow_of_rowsFrom lemma814PathCertificate 0 i lemma814PathCertificate_rows_ok
    (hlen ▸ hi)
  rw [Nat.zero_add] at hrow
  change validIndexedPathRow i (rowAt i) = true at hrow
  unfold validIndexedPathRow at hrow
  simp only [Bool.and_eq_true] at hrow
  have hmem : rowAt i ∈ lemma814PathCertificate := by
    unfold rowAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hi), Option.getD_some]
    exact List.getElem_mem _
  have hdom := List.all_eq_true.1 lemma814CertificateMoveDomainAudit_ok (rowAt i) hmem
  unfold certificateRowMovesInEncodedDomain at hdom
  exact reach_of_validSteps (rowAt i).steps i (representativeAt i) hi
    (fun st hst => List.all_eq_true.1 hdom st hst) hrow.2

/-- **Lemma 8.14 on the line graph.**  Two colourings of the gadget agreeing on
the four input stubs are joined by Kempe switches avoiding them. -/
theorem tau_fibreConnected : tauLineGraph.FibreConnected LColor tauInputSet := by
  intro C D hCD
  obtain ⟨i, hi, hsi, rfl⟩ := exists_state C
  obtain ⟨j, hj, hsj, rfl⟩ := exists_state D
  have hsame : sameInput (stateAt i) (stateAt j) = true := by
    unfold sameInput
    rw [List.all_eq_true]
    intro e he
    rw [colorEq_eq_true_iff]
    exact Coloring.boundaryWord_eq_iff.1 hCD e he
  have hcoh := List.all_eq_true.1 (List.all_eq_true.1 representativeCoherenceAudit_ok i
    (List.mem_range.2 hi)) j (List.mem_range.2 hj)
  rw [hsame, Bool.not_true, Bool.false_or, beq_iff_eq] at hcoh
  obtain ⟨-, hpi⟩ := reach_representative hi
  obtain ⟨-, hpj⟩ := reach_representative hj
  rw [idxColoring_of_lt hi hsi, hcoh] at hpi
  rw [idxColoring_of_lt hj hsj] at hpj
  exact hpi.trans (reflTransGen_kempeStepAvoiding_symm hpj)

/-! ## Lemma 8.15 on the line graph -/

set_option maxRecDepth 4096 in
theorem stub_of_touches_boundary :
    tauEdges.all (fun e => tauEndpoints.all fun v =>
      isInternalEndpoint v || !edgeTouchesEndpoint e v || tauStubEdges.contains e) = true := by
  decide

theorem stub_of_transparentComponent {L : List TauEdge} (h : transparentComponent L = true) :
    ∃ e ∈ L, e ∈ tauStubEdges := by
  unfold transparentComponent at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have hcount := h.1.2
  unfold boundaryDegreeOneCount at hcount
  obtain ⟨v, hv⟩ := List.exists_mem_of_length_pos (by omega :
    0 < (tauEndpoints.filter fun v => !isInternalEndpoint v && degreeInComponent L v == 1).length)
  rw [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hv
  obtain ⟨hvmem, hvint, hdeg⟩ := hv
  unfold degreeInComponent at hdeg
  obtain ⟨e, he⟩ := List.exists_mem_of_length_pos (by omega :
    0 < (L.filter fun e => edgeTouchesEndpoint e v).length)
  rw [List.mem_filter] at he
  refine ⟨e, he.1, ?_⟩
  have hcheck := List.all_eq_true.1 (List.all_eq_true.1 stub_of_touches_boundary e (mem_tauEdges e))
    v hvmem
  rw [hvint, he.2] at hcheck
  simpa using hcheck

theorem transparencyAt_of_lt {i : Nat} (hi : i < 192) : tauTreeTransparencyAtIndex i = true := by
  have hrange (start len k : Nat) (h : tauTreeTransparencyRangeAudit start len = true)
      (hk : k < len) : tauTreeTransparencyAtIndex (start + k) = true :=
    List.all_eq_true.1 h k (List.mem_range.2 hk)
  rcases (by omega : i < 64 ∨ (64 ≤ i ∧ i < 128) ∨ 128 ≤ i) with h | ⟨h1, h2⟩ | h1
  · simpa using hrange 0 64 i tauTreeTransparencyRange_0_64_ok h
  · simpa [Nat.add_sub_cancel' h1] using
      hrange 64 64 (i - 64) tauTreeTransparencyRange_64_64_ok (by omega)
  · simpa [Nat.add_sub_cancel' h1] using
      hrange 128 64 (i - 128) tauTreeTransparencyRange_128_64_ok (by omega)

/-- **Lemma 8.15 on the line graph.**  In every colouring of the gadget, every
two-colour component contains a stub edge. -/
theorem tau_transparent : tauLineGraph.Transparent LColor tauStubSet := by
  intro C c₁ c₂ hab K
  obtain ⟨i, hi, hs, rfl⟩ := exists_state C
  obtain ⟨v, hv, rfl⟩ := (stateColoring (stateAt i) hs).exists_eq_mk_of_kempeComponent K
  obtain ⟨a', c', hpair, hS⟩ : ∃ a' c', (a', c') ∈ colorPairs ∧
      (stateColoring (stateAt i) hs).bicoloredSet c₁ c₂ =
        (stateColoring (stateAt i) hs).bicoloredSet a' c' := by
    cases c₁ <;> cases c₂ <;>
      first
      | exact absurd rfl hab
      | exact ⟨_, _, by decide, rfl⟩
      | exact ⟨_, _, by decide, Coloring.bicoloredSet_comm _ _ _⟩
  have hv' : v ∈ (stateColoring (stateAt i) hs).bicoloredSet a' c' := hS ▸ hv
  rw [← Coloring.kempeComponentSet_mk_eq_of_bicoloredSet_eq _ _ hS hv hv',
    ← tauComponent_eq_kempeComponentSet (stateAt_mem hi) hs hpair hv']
  have haudit := List.all_eq_true.1 (List.all_eq_true.1 (transparencyAt_of_lt hi) (a', c') hpair)
    v (mem_tauEdges v)
  have hvin : v ∈ tauComponent (stateAt i) a' c' v := by
    have := (tauComponent_eq_kempeComponentSet (stateAt_mem hi) hs hpair hv').symm ▸
      (stateColoring (stateAt i) hs).mem_kempeComponentSet_self hv'
    exact this
  have hne : (tauComponent (stateAt i) a' c' v).isEmpty = false := by
    rw [List.isEmpty_eq_false_iff_exists_mem]; exact ⟨v, hvin⟩
  simp only [] at haudit
  rw [hne, Bool.false_or] at haudit
  obtain ⟨e, he, hstub⟩ := stub_of_transparentComponent haudit
  exact ⟨e, he, hstub⟩

end Mettapedia.GraphTheory.Kempe.TauGadget
