import Mettapedia.GraphTheory.FourColor.GoertzelV24HexagonPlanarPairingObstruction
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexCellPortTangle
import Mettapedia.GraphTheory.FourColor.GoertzelV24PortTangleCutParity
import Mettapedia.GraphTheory.FourColor.GoertzelV24TargetAwareReplacementQuantifiers

/-!
# Boundary language for target-aware hexagon replacements

Allowing a replacement to depend on the exterior is useful only when the
exterior ranges over a genuinely restricted physical language.  This file
specializes that quantifier boundary to the five noncrossing pairing caps of
a six-port hexagon, using genuine nonzero Tait boundary words throughout.

Every pairing cap accepts at least one nonzero word which the hexagon does not
accept.  Consequently no pairing-cap support is contained in the hexagon
support.  The complement of the hexagon support is therefore one abstract
zero exterior which meets every pairing support, so even an exterior-dependent
choice among the five caps cannot work against arbitrary exterior supports.

This does not assert that the complement support is realized by a planar
exterior.  It isolates physical realizability as the only remaining loophole
for this particular target-aware repair.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexagonPairingTargetAwareBoundary

open GoertzelV24RawNooseCountPumping
open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleCutParity
open GoertzelV24TargetAwareReplacementQuantifiers
open GoertzelV24HexCycleBoundarySupport
open GoertzelV24HexCellPortTangle

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Genuine nonzero boundary words on the six cyclic ports. -/
abbrev HexagonTaitWord := CutWord (Fin 6)

/-- Forget the nonzero proofs carried by a genuine Tait word. -/
def rawWord (word : HexagonTaitWord) : HexagonBoundaryWord :=
  fun port => (word port).1

/-- The exact support of the literal hexagon, restricted to genuine Tait
boundary words. -/
def hexagonSupport : Set HexagonTaitWord :=
  {word | ∃ coloring, IsHexagonExtension (rawWord word) coloring}

/-- Coordinate-free form of the six explicit local properness clauses. -/
private theorem isHexagonExtension_iff_forall
    (word : HexagonTaitWord) (coloring : HexagonInternalColoring) :
    IsHexagonExtension (rawWord word) coloring ↔
      ∀ port : Fin 6,
        ProperColorTriple (rawWord word port)
          (coloring (hexPred port)) (coloring port) := by
  constructor
  · intro h port
    fin_cases port
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1
    · exact h.2.2.2.2.1
    · exact h.2.2.2.2.2
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5⟩

/-- The explicit hexagon-extension predicate is exactly the already verified
six-step recurrence predicate. -/
theorem exists_hexagonExtension_iff_hexBoundaryRealizable
    (word : HexagonTaitWord) :
    (∃ coloring, IsHexagonExtension (rawWord word) coloring) ↔
      HexBoundaryRealizable word := by
  rw [hexBoundaryRealizable_iff_cycleExtends]
  constructor
  · rintro ⟨coloring, hextends⟩
    have hproper := (isHexagonExtension_iff_forall word coloring).1 hextends
    let edgeColor : Fin 6 → TaitColor := fun port =>
      ⟨coloring port, (hproper port).2.2.1⟩
    refine ⟨edgeColor, ?_⟩
    intro port
    have hlocal := hproper port
    have hsum := (pairwise_ne_iff_sum_eq_zero_of_ne_zero
      hlocal.1 hlocal.2.1 hlocal.2.2.1).1
        ⟨hlocal.2.2.2.1, hlocal.2.2.2.2.1, hlocal.2.2.2.2.2⟩
    simpa [edgeColor, rawWord, add_comm] using hsum
  · rintro ⟨edgeColor, hcycle⟩
    refine ⟨fun port => (edgeColor port).1,
      (isHexagonExtension_iff_forall word _).2 ?_⟩
    intro port
    have hpair := localPairwise_of_cycleEquation hcycle port
    exact ⟨(word port).2, (edgeColor (hexPred port)).2,
      (edgeColor port).2, hpair.1.symm, hpair.2.2, hpair.2.1⟩

/-- The support of one of the five noncrossing planar pairing caps. -/
def planarPairingSupport (side : HexagonPlanarPairing) : Set HexagonTaitWord :=
  {word | side.Compatible (rawWord word)}

@[simp] theorem mem_hexagonSupport_iff (word : HexagonTaitWord) :
    word ∈ hexagonSupport ↔
      ∃ coloring, IsHexagonExtension (rawWord word) coloring :=
  Iff.rfl

@[simp] theorem mem_planarPairingSupport_iff
    (side : HexagonPlanarPairing) (word : HexagonTaitWord) :
    word ∈ planarPairingSupport side ↔ side.Compatible (rawWord word) :=
  Iff.rfl

/-- Every planar pairing cap accepts a genuine nonzero boundary word which
does not extend across the hexagon.  This is the support-inclusion obstruction
needed by the target-aware quantifier theorem. -/
theorem every_planarPairing_accepts_nonextension :
    ∀ side : HexagonPlanarPairing,
      ∃ word : HexagonTaitWord,
        side.Compatible (rawWord word) ∧
          ¬ ∃ coloring, IsHexagonExtension (rawWord word) coloring := by
  decide

/-- No one planar pairing cap is a monotone support replacement for the
hexagon. -/
theorem no_planarPairingSupport_subset :
    ∀ side : HexagonPlanarPairing,
      ¬ planarPairingSupport side ⊆ hexagonSupport := by
  intro side hsubset
  obtain ⟨word, hpairing, hhexagon⟩ :=
    every_planarPairing_accepts_nonextension side
  exact hhexagon (hsubset hpairing)

/-- The maximal abstract zero exterior for the hexagon meets every planar
pairing support. -/
theorem complement_hexagonSupport_meets_every_planarPairing :
    Disjoint hexagonSupportᶜ hexagonSupport ∧
      ∀ side : HexagonPlanarPairing,
        ¬ Disjoint hexagonSupportᶜ (planarPairingSupport side) :=
  complement_adversary_of_no_subset
    hexagonSupport planarPairingSupport no_planarPairingSupport_subset

/-- **Unrestricted target-aware planar-pairing reduction fails.**  Even when
the chosen cap may depend on the exterior, one cannot handle every abstract
exterior support having zero Count with the hexagon. -/
theorem no_unrestricted_targetAware_planarPairing_reduction :
    ¬ (∀ exterior : Set HexagonTaitWord,
        Disjoint exterior hexagonSupport →
          ∃ side : HexagonPlanarPairing,
            Disjoint exterior (planarPairingSupport side)) := by
  intro h
  have hsubset :
      ∃ side : HexagonPlanarPairing,
        planarPairingSupport side ⊆ hexagonSupport :=
    (unrestricted_targetAware_iff_exists_subset
      hexagonSupport planarPairingSupport).1 h
  obtain ⟨side, hside⟩ := hsubset
  exact no_planarPairingSupport_subset side hside

/-- The same failure holds for any proposed physical exterior class which
contains the complement of the hexagon support. -/
theorem no_physical_targetAware_planarPairing_reduction_of_complement_mem
    (physicalExterior : Set (Set HexagonTaitWord))
    (hcomplement : hexagonSupportᶜ ∈ physicalExterior) :
    ¬ (∀ exterior ∈ physicalExterior,
        Disjoint exterior hexagonSupport →
          ∃ side : HexagonPlanarPairing,
            Disjoint exterior (planarPairingSupport side)) := by
  intro h
  have hsubset :
      ∃ side : HexagonPlanarPairing,
        planarPairingSupport side ⊆ hexagonSupport :=
    (physical_targetAware_iff_exists_subset_of_compl_mem
      hexagonSupport planarPairingSupport physicalExterior hcomplement).1 h
  obtain ⟨side, hside⟩ := hsubset
  exact no_planarPairingSupport_subset side hside

/-! ## The parity-admissible adversary

The full set complement contains words which no Tait-coloured tangle can
realize, because every physical cut word has zero total Klein sum.  The
following refinement removes that easy objection. -/

/-- Total Klein colour on the six ports, written explicitly so the finite
checker has no enumeration-order dependency. -/
def boundarySum (word : HexagonTaitWord) : Color :=
  (word 0).1 + (word 1).1 + (word 2).1 +
    (word 3).1 + (word 4).1 + (word 5).1

/-- The universal parity language for a six-edge cut. -/
def parityAdmissible : Set HexagonTaitWord :=
  {word | boundarySum word = 0}

/-- The parity language really is universal for the exact open-tangle
semantics: the support of every finite cubic six-port tangle lies inside it.
No planarity assumption is needed for this necessary condition. -/
theorem portTangle_taitSupport_subset_parityAdmissible
    {V I : Type} [Fintype V] [Fintype I]
    [DecidableEq V] [DecidableEq I]
    (T : PortTangle V I (Fin 6)) (hcubic : IsCubic T) :
    taitSupport T ⊆ parityAdmissible := by
  intro word hword
  have hsum := taitSupport_subset_zeroSum T hcubic hword
  change boundarySum word = 0
  simpa [boundarySum, Fin.sum_univ_succ, add_assoc] using hsum

/-- Every word accepted by a pairing cap obeys the cut-parity equation. -/
private theorem boundarySum_eq_zero_of_compatible :
    ∀ side : HexagonPlanarPairing, ∀ word : HexagonTaitWord,
      side.Compatible (rawWord word) → boundarySum word = 0 := by
  decide

theorem planarPairingSupport_subset_parityAdmissible :
    ∀ side : HexagonPlanarPairing,
      planarPairingSupport side ⊆ parityAdmissible := by
  intro side word hword
  exact boundarySum_eq_zero_of_compatible side word hword

/-- The parity-admissible part of the hexagon complement. -/
def parityAdversary : Set HexagonTaitWord :=
  parityAdmissible \ hexagonSupport

/-- Executable membership test for the parity adversary.  The six-step
recurrence avoids re-enumerating all internal edge-colouring functions. -/
def parityAdversaryBool (word : HexagonTaitWord) : Bool :=
  decide (boundarySum word = 0) && !hexBoundaryRealizableBool word

theorem parityAdversaryBool_eq_true_iff (word : HexagonTaitWord) :
    parityAdversaryBool word = true ↔ word ∈ parityAdversary := by
  simp only [parityAdversaryBool, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, Bool.eq_false_iff, parityAdversary,
    parityAdmissible, Set.mem_sdiff,
    Set.mem_setOf_eq, mem_hexagonSupport_iff,
    exists_hexagonExtension_iff_hexBoundaryRealizable]
  constructor
  · rintro ⟨hparity, hnotBool⟩
    exact ⟨hparity, fun hrealizable =>
      hnotBool ((hexBoundaryRealizableBool_eq_true_iff word).2 hrealizable)⟩
  · rintro ⟨hparity, hnotRealizable⟩
    exact ⟨hparity, fun hbool =>
      hnotRealizable ((hexBoundaryRealizableBool_eq_true_iff word).1 hbool)⟩

theorem parityAdversary_subset_parityAdmissible :
    parityAdversary ⊆ parityAdmissible := by
  intro word hword
  exact hword.1

theorem parityAdversary_disjoint_hexagonSupport :
    Disjoint parityAdversary hexagonSupport := by
  rw [Set.disjoint_left]
  intro word hword hhexagon
  exact hword.2 hhexagon

/-- The parity-admissible adversary still meets every planar pairing cap. -/
theorem parityAdversary_meets_every_planarPairing :
    ∀ side : HexagonPlanarPairing,
      ¬ Disjoint parityAdversary (planarPairingSupport side) := by
  intro side hdisjoint
  obtain ⟨word, hpairing, hhexagon⟩ :=
    every_planarPairing_accepts_nonextension side
  have hparity : word ∈ parityAdmissible :=
    planarPairingSupport_subset_parityAdmissible side hpairing
  rw [Set.disjoint_left] at hdisjoint
  exact hdisjoint ⟨hparity, hhexagon⟩ hpairing

/-- **Parity does not rescue target-aware pairing reduction.**  Even after
restricting the exterior language to genuine words with zero total colour,
there is one zero exterior support against which every pairing cap fails. -/
theorem no_parityRestricted_targetAware_planarPairing_reduction :
    ¬ (∀ exterior : Set HexagonTaitWord,
        exterior ⊆ parityAdmissible →
        Disjoint exterior hexagonSupport →
          ∃ side : HexagonPlanarPairing,
            Disjoint exterior (planarPairingSupport side)) := by
  intro h
  obtain ⟨side, hside⟩ :=
    h parityAdversary parityAdversary_subset_parityAdmissible
      parityAdversary_disjoint_hexagonSupport
  exact parityAdversary_meets_every_planarPairing side hside

/-! ## Boundary Kempe closure

Parity is not the only visible necessary condition on the support of a planar
exterior.  In a fixed colouring, each bichromatic component meeting a cyclic
boundary pairs two active ports, those pairs are noncrossing, and switching
any union of components produces another supported word.  The definitions
below state exactly that boundary-language condition at six ports.

The final finite theorem shows that this stronger test still does not remove
the parity adversary.  It is deliberately a theorem about the abstract
boundary language.  Deriving this condition from a literal planar tangle
requires the generic component-to-noncrossing-matching theorem; no such
topological bridge is assumed here.
-/

/-- The three unordered pairs of genuine Tait colours. -/
inductive TaitColorPair where
  | redBlue
  | redPurple
  | bluePurple
  deriving DecidableEq, Fintype

/-- Ambient colours represented by a `TaitColorPair`. -/
def TaitColorPair.colors : TaitColorPair → Color × Color
  | .redBlue => (red, blue)
  | .redPurple => (red, purple)
  | .bluePurple => (blue, purple)

/-- Ports active in the selected two-colour subgraph. -/
def activePort (word : HexagonTaitWord) (pair : TaitColorPair)
    (port : Fin 6) : Prop :=
  (word port).1 = pair.colors.1 ∨ (word port).1 = pair.colors.2

private instance activePortDecidable
    (word : HexagonTaitWord) (pair : TaitColorPair) (port : Fin 6) :
    Decidable (activePort word pair port) := by
  unfold activePort
  infer_instance

private theorem swapPairColor_ne_zero
    (pair : TaitColorPair) (color : {color : Color // color ≠ 0}) :
    Color.swap pair.colors.1 pair.colors.2 color.1 ≠ 0 := by
  cases pair <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero color.1 color.2 with
      h | h | h <;>
    simp [TaitColorPair.colors, Color.swap, h, red, blue, purple]

/-- Boundary action of switching the selected union of bichromatic
components. -/
def swapBoundaryWord (word : HexagonTaitWord) (pair : TaitColorPair)
    (selected : Finset (Fin 6)) : HexagonTaitWord :=
  fun port =>
    if port ∈ selected then
      ⟨Color.swap pair.colors.1 pair.colors.2 (word port).1,
        swapPairColor_ne_zero pair (word port)⟩
    else word port

/-- Two chords cross when their four endpoints interleave in the displayed
linearization of the cyclic order.  Taking the smaller endpoint first makes
this independent of chord orientation. -/
def ChordsCross (first second third fourth : Fin 6) : Prop :=
  let a := min first.1 second.1
  let b := max first.1 second.1
  let c := min third.1 fourth.1
  let d := max third.1 fourth.1
  (a < c ∧ c < b ∧ b < d) ∨ (c < a ∧ a < d ∧ d < b)

private instance chordsCrossDecidable
    (first second third fourth : Fin 6) :
    Decidable (ChordsCross first second third fourth) := by
  unfold ChordsCross
  infer_instance

/-- A port permutation pairs precisely the active ports, fixes inactive
ports, and is a fixed-point-free involution on the active set. -/
def IsActiveMatching (word : HexagonTaitWord) (pair : TaitColorPair)
    (mate : Fin 6 → Fin 6) : Prop :=
  ∀ port,
    (activePort word pair port ↔ activePort word pair (mate port)) ∧
      mate (mate port) = port ∧
      (activePort word pair port → mate port ≠ port) ∧
      (¬ activePort word pair port → mate port = port)

/-- No two chords of the matching cross in the boundary disk. -/
def IsNoncrossingMatching (mate : Fin 6 → Fin 6) : Prop :=
  ∀ first third, ¬ ChordsCross first (mate first) third (mate third)

/-- A selected set is a union of complete matched components. -/
def IsComponentUnion (mate : Fin 6 → Fin 6)
    (selected : Finset (Fin 6)) : Prop :=
  ∀ port, port ∈ selected ↔ mate port ∈ selected

private instance isComponentUnionDecidable
    (mate : Fin 6 → Fin 6) (selected : Finset (Fin 6)) :
    Decidable (IsComponentUnion mate selected) := by
  unfold IsComponentUnion
  infer_instance

/-- One colouring-word and one colour pair have a noncrossing component
matching whose every component-union switch stays in the support. -/
def HasBoundaryKempeWitness (support : Set HexagonTaitWord)
    [DecidablePred (fun word => word ∈ support)]
    (word : HexagonTaitWord) (pair : TaitColorPair) : Prop :=
  ∃ mate : Fin 6 → Fin 6,
    IsActiveMatching word pair mate ∧
      IsNoncrossingMatching mate ∧
      ∀ selected : Finset (Fin 6),
        IsComponentUnion mate selected →
          swapBoundaryWord word pair selected ∈ support

/-- Necessary boundary-language closure suggested by planar Kempe components:
each supported word has a suitable matching for each colour pair. -/
def BoundaryKempeClosed (support : Set HexagonTaitWord)
    [DecidablePred (fun word => word ∈ support)] : Prop :=
  ∀ word ∈ support, ∀ pair : TaitColorPair,
    HasBoundaryKempeWitness support word pair

/-- Active ports in their inherited cyclic order. -/
def activePorts (word : HexagonTaitWord) (pair : TaitColorPair) :
    Finset (Fin 6) :=
  Finset.univ.filter fun port => activePort word pair port

/-- Zero-based rank of a port among the active ports before it. -/
def activeRank (word : HexagonTaitWord) (pair : TaitColorPair)
    (port : Fin 6) : Nat :=
  ((activePorts word pair).filter fun earlier => earlier < port).card

/-- The active port of a requested rank, with an irrelevant default outside
the range.  All uses below request a rank paired with an existing active
port; the finite checker verifies that fact as part of `IsActiveMatching`. -/
def activePortAtRank (word : HexagonTaitWord) (pair : TaitColorPair)
    (rank : Nat) : Fin 6 :=
  let candidates :=
    (activePorts word pair).filter fun port => activeRank word pair port = rank
  if h : candidates.Nonempty then candidates.min' h else 0

private def partnerRankFour (pattern rank : Nat) : Nat :=
  if pattern = 0 then
    match rank with
    | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | other => other
  else
    match rank with
    | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | other => other

private def partnerRankSix (pattern rank : Nat) : Nat :=
  match pattern with
  | 0 => match rank with
    | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | other => other
  | 1 => match rank with
    | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 4 | 4 => 3 | 5 => 2 | other => other
  | 2 => match rank with
    | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 5 | 5 => 4 | other => other
  | 3 => match rank with
    | 0 => 5 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 0 | other => other
  | _ => match rank with
    | 0 => 5 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 0 | other => other

/-- One of the five Catalan matchings on the active ports.  At four active
ports only the first two patterns differ; at two active ports the matching is
unique. -/
def candidateMate (word : HexagonTaitWord) (pair : TaitColorPair)
    (pattern : Fin 5) : Fin 6 → Fin 6 :=
  fun port =>
    if activePort word pair port then
      let count := (activePorts word pair).card
      let rank := activeRank word pair port
      let partnerRank :=
        if count = 2 then
          if rank = 0 then 1 else 0
        else if count = 4 then
          partnerRankFour pattern.1 rank
        else if count = 6 then
          partnerRankSix pattern.1 rank
        else rank
      activePortAtRank word pair partnerRank
    else port

/-- The full certificate checked for one candidate matching. -/
def CandidateKempeWitness (support : Set HexagonTaitWord)
    [DecidablePred (fun word => word ∈ support)]
    (word : HexagonTaitWord) (pair : TaitColorPair) (pattern : Fin 5) : Prop :=
  let mate := candidateMate word pair pattern
  IsActiveMatching word pair mate ∧
    IsNoncrossingMatching mate ∧
    ∀ selected : Finset (Fin 6),
      IsComponentUnion mate selected →
        swapBoundaryWord word pair selected ∈ support

private instance parityAdversaryDecidablePred :
    DecidablePred (fun word : HexagonTaitWord => word ∈ parityAdversary) :=
  fun word => by
    unfold parityAdversary parityAdmissible hexagonSupport
    infer_instance

private def twoBooleans : List Bool := [false, true]

private theorem mem_twoBooleans (value : Bool) : value ∈ twoBooleans := by
  cases value <;> simp [twoBooleans]

/-- The subset of the six ports encoded by six Boolean flags. -/
private def selectedPorts (b0 b1 b2 b3 b4 b5 : Bool) : Finset (Fin 6) :=
  Finset.univ.filter fun port => ![b0, b1, b2, b3, b4, b5] port

private theorem selectedPorts_of_finset (selected : Finset (Fin 6)) :
    selectedPorts
      (decide (0 ∈ selected)) (decide (1 ∈ selected))
      (decide (2 ∈ selected)) (decide (3 ∈ selected))
      (decide (4 ∈ selected)) (decide (5 ∈ selected)) = selected := by
  ext port
  fin_cases port <;> simp [selectedPorts]

/-- Executable universal quantifier over all `2^6` subsets of the ports. -/
private def allSelectedPortSets (test : Finset (Fin 6) → Bool) : Bool :=
  twoBooleans.all fun b0 =>
    twoBooleans.all fun b1 =>
      twoBooleans.all fun b2 =>
        twoBooleans.all fun b3 =>
          twoBooleans.all fun b4 =>
            twoBooleans.all fun b5 => test (selectedPorts b0 b1 b2 b3 b4 b5)

private theorem allSelectedPortSets_eq_true_iff
    (test : Finset (Fin 6) → Bool) :
    allSelectedPortSets test = true ↔ ∀ selected, test selected = true := by
  simp only [allSelectedPortSets, List.all_eq_true]
  constructor
  · intro h selected
    have hselected := h
      (decide (0 ∈ selected)) (mem_twoBooleans _)
      (decide (1 ∈ selected)) (mem_twoBooleans _)
      (decide (2 ∈ selected)) (mem_twoBooleans _)
      (decide (3 ∈ selected)) (mem_twoBooleans _)
      (decide (4 ∈ selected)) (mem_twoBooleans _)
      (decide (5 ∈ selected)) (mem_twoBooleans _)
    rw [selectedPorts_of_finset] at hselected
    exact hselected
  · intro h b0 _ b1 _ b2 _ b3 _ b4 _ b5 _
    exact h (selectedPorts b0 b1 b2 b3 b4 b5)

/-- Boolean checker for the three finite clauses of a proposed matching.  It
uses lists deliberately: the resulting certificate is a small closed Boolean
computation, rather than a materialized proof tree for every boundary word. -/
def candidateKempeWitnessBool (member : HexagonTaitWord → Bool)
    (word : HexagonTaitWord) (pair : TaitColorPair) (pattern : Fin 5) : Bool :=
  let mate := candidateMate word pair pattern
  ((List.ofFn fun port : Fin 6 =>
      decide
        ((activePort word pair port ↔ activePort word pair (mate port)) ∧
          mate (mate port) = port ∧
          (activePort word pair port → mate port ≠ port) ∧
          (¬ activePort word pair port → mate port = port))).all id) &&
    ((List.ofFn fun first : Fin 6 =>
      (List.ofFn fun third : Fin 6 =>
        decide (¬ ChordsCross first (mate first) third (mate third))).all id).all id) &&
    (allSelectedPortSets fun selected =>
      (!decide (IsComponentUnion mate selected)) ||
        member (swapBoundaryWord word pair selected))

private theorem all_ofFn_eq_true_iff {n : Nat} (test : Fin n → Bool) :
    (List.ofFn test).all id = true ↔ ∀ index, test index = true := by
  rw [List.all_eq_true]
  constructor
  · intro h index
    exact h (test index) (List.mem_ofFn.mpr ⟨index, rfl⟩)
  · intro h value hvalue
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hvalue
    exact h index

/-- The Boolean checker is a verified decoder for the mathematical matching
certificate. -/
theorem candidateKempeWitnessBool_eq_true_iff
    (support : Set HexagonTaitWord)
    [DecidablePred (fun word => word ∈ support)]
    (member : HexagonTaitWord → Bool)
    (hmember : ∀ candidate, member candidate = true ↔ candidate ∈ support)
    (word : HexagonTaitWord) (pair : TaitColorPair) (pattern : Fin 5) :
    candidateKempeWitnessBool member word pair pattern = true ↔
      CandidateKempeWitness support word pair pattern := by
  simp only [candidateKempeWitnessBool, Bool.and_eq_true,
    all_ofFn_eq_true_iff, allSelectedPortSets_eq_true_iff,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, hmember, CandidateKempeWitness,
    IsActiveMatching, IsNoncrossingMatching]
  constructor
  · rintro ⟨⟨hactive, hnoncrossing⟩, hclosure⟩
    exact ⟨hactive, hnoncrossing, fun selected hselected =>
      (hclosure selected).resolve_left (fun hnot => hnot hselected)⟩
  · rintro ⟨hactive, hnoncrossing, hclosure⟩
    refine ⟨⟨hactive, hnoncrossing⟩, ?_⟩
    intro selected
    by_cases hselected : IsComponentUnion (candidateMate word pair pattern) selected
    · exact Or.inr (hclosure selected hselected)
    · exact Or.inl hselected

/-- Numeric code of a genuine Tait colour in the fixed certificate order. -/
private def taitColorDigit (color : TaitColor) : Nat :=
  if color.1 = red then 0 else if color.1 = blue then 1 else 2

private def colorPairDigit : TaitColorPair → Nat
  | .redBlue => 0
  | .redPurple => 1
  | .bluePurple => 2

/-- Base-three position of a six-port word, with port five varying fastest. -/
private def explicitWordIndex (word : HexagonTaitWord) : Nat :=
  taitColorDigit (word 0) * 243 + taitColorDigit (word 1) * 81 +
    taitColorDigit (word 2) * 27 + taitColorDigit (word 3) * 9 +
      taitColorDigit (word 4) * 3 + taitColorDigit (word 5)

/-- Flat pattern certificate: three blocks of 729 ASCII digits, one block for
each colour pair.  Non-adversary rows carry the irrelevant default zero. -/
@[reducible] private def certifiedPatternPayload : ByteArray :=
  ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The certified Catalan matching for one word and colour pair. -/
def certifiedPattern (word : HexagonTaitWord) (pair : TaitColorPair) : Fin 5 :=
  Fin.ofNat 5
    ((certifiedPatternPayload.get!
      (colorPairDigit pair * 729 + explicitWordIndex word)).toNat)

/- Enumerating the six scalar colours is much smaller than asking Lean to
enumerate the function-space representation of a boundary word. -/
def explicitWord (a b c d e f : TaitColor) : HexagonTaitWord :=
  ![a, b, c, d, e, f]

theorem explicitWord_of_word (word : HexagonTaitWord) :
    explicitWord (word 0) (word 1) (word 2) (word 3) (word 4) (word 5) = word := by
  funext port
  fin_cases port <;> rfl

private def threeTaitColors : List TaitColor :=
  [⟨red, red_ne_zero⟩, ⟨blue, blue_ne_zero⟩, ⟨purple, purple_ne_zero⟩]

private theorem mem_threeTaitColors (color : TaitColor) :
    color ∈ threeTaitColors := by
  rcases color with ⟨color, hcolor⟩
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero color hcolor with
    rfl | rfl | rfl <;> simp [threeTaitColors]

def candidateRow (a b c d e f : TaitColor)
    (pair : TaitColorPair) : Bool :=
  let word := explicitWord a b c d e f
  if parityAdversaryBool word = true then
    candidateKempeWitnessBool parityAdversaryBool word pair
      (certifiedPattern word pair)
  else true

/-- Closed finite certificate over the scalar presentation of all `3^6`
boundary words. -/
def allSixCandidateCheck (pair : TaitColorPair) : Bool :=
  threeTaitColors.all fun a =>
    threeTaitColors.all fun b =>
      threeTaitColors.all fun c =>
        threeTaitColors.all fun d =>
          threeTaitColors.all fun e =>
            threeTaitColors.all fun f => candidateRow a b c d e f pair

theorem candidateRow_eq_true
    (pair : TaitColorPair) (a b c d e f : TaitColor) :
    allSixCandidateCheck pair = true → candidateRow a b c d e f pair = true := by
  simp only [allSixCandidateCheck, List.all_eq_true]
  intro h
  exact h a (mem_threeTaitColors a)
    b (mem_threeTaitColors b)
    c (mem_threeTaitColors c)
    d (mem_threeTaitColors d)
    e (mem_threeTaitColors e)
    f (mem_threeTaitColors f)

end GoertzelV24HexagonPairingTargetAwareBoundary

end Mettapedia.GraphTheory.FourColor
