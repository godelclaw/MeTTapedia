import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnCarrierSweep
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnSeparatorNesting

/-!
# Physical return triples extracted from a deep residual stack

The LIFO sweep records residual returns as ordered labelled arcs.  The
existing sweep-to-cut bridge realizes each such arc as its original physical
return chord.  This file consumes that bridge three times at one deep stack.

Consequently a residual stack of depth at least three supplies three literal
same-shore return chords in strict nesting order.  These are the direct input
to the separator-side nesting theorem; no abstract family of cuts is assumed.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualReturnNestedFamily

open GoertzelV24NoncrossingSweepLifo
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open NoncrossingPairingSweep
open ResidualReturnCarrierSweep
open ResidualReturnSweep
open ResidualReturnSweepCyclicCut
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A finite family of original residual-return chords on one facial shore,
strictly nested in its `Fin n` order.  This is the physical interpretation of
one prefix of a deep LIFO stack. -/
def StrictlyNestedReturnFamily
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (n : Nat) : Prop :=
  ∃ (shore : Bool)
      (chord : Fin n → OrderedReturnChord
        (orderedSiteReturnPairing hG sigma hSigma bond.site)),
    (∀ i, orderedReturnShore rotation hG sigma hSigma bond
      (chord i).left = shore) ∧
      ∀ i j, i < j →
        (chord i).left < (chord j).left ∧
          (chord j).right < (chord i).right

/-- Every requested finite prefix of a sufficiently deep abstract return
stack consists of literal physical returns, with its whole nesting order and
common shore preserved. -/
theorem strictlyNestedReturnFamily_of_deep_stack
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (depth : Nat)
    (hdeep : ∃ shore cut,
      depth < (((residualReturnSweepData rotation minimal hG sigma hSigma bond).family
        shore).stackAt cut).length) :
    StrictlyNestedReturnFamily rotation hG sigma hSigma bond (depth + 1) := by
  rcases exists_long_strictlyNested_return_family_of_deep
      rotation minimal hG sigma hSigma bond depth hdeep with
    ⟨shoreIndex, cut, hlength, hpairwise⟩
  let matching :=
    returnShoreMatching rotation minimal hG sigma hSigma bond
      (returnShoreIndex shoreIndex)
  let arcs := matching.openArcs cut
  change depth < arcs.length at hlength
  have hlength' : depth + 1 ≤ arcs.length := by
    omega
  let arcIndex (i : Fin (depth + 1)) : Fin arcs.length :=
    ⟨i.val, i.isLt.trans_le hlength'⟩
  let arc (i : Fin (depth + 1)) := arcs.get (arcIndex i)
  have harc (i : Fin (depth + 1)) : arc i ∈ matching.openArcs cut := by
    simpa only [arcs, arc] using List.get_mem arcs (arcIndex i)
  have hphysical (i : Fin (depth + 1)) :
      ∃ physical : OrderedReturnChord
          (orderedSiteReturnPairing hG sigma hSigma bond.site),
        physical.left = (arc i).left ∧
          physical.right = (arc i).right ∧
          orderedReturnShore rotation hG sigma hSigma bond physical.left =
            returnShoreIndex shoreIndex :=
    exists_physical_chord_of_mem_openArcs rotation minimal hG sigma hSigma
      bond shoreIndex cut (arc i) (harc i)
  let chord (i : Fin (depth + 1)) := Classical.choose (hphysical i)
  have hchord (i : Fin (depth + 1)) := Classical.choose_spec (hphysical i)
  refine ⟨returnShoreIndex shoreIndex, chord, ?_, ?_⟩
  · intro i
    exact (hchord i).2.2
  · intro i j hij
    have hindex : arcIndex i < arcIndex j := by
      exact Fin.mk_lt_mk.mpr (Fin.mk_lt_mk.mp hij)
    have hnested := hpairwise.rel_get_of_lt hindex
    constructor
    · simpa only [chord, (hchord i).1, (hchord j).1] using hnested.1
    · simpa only [chord, (hchord i).2.1, (hchord j).2.1] using hnested.2

/-- Three physical residual returns on one facial shore, strictly nested in
the linear display of the carrier cycle. -/
def StrictlyNestedReturnTriple
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second) :
    Prop :=
  ∃ (shore : Bool)
      (outer middle inner : OrderedReturnChord
        (orderedSiteReturnPairing hG sigma hSigma bond.site)),
    orderedReturnShore rotation hG sigma hSigma bond outer.left = shore ∧
      orderedReturnShore rotation hG sigma hSigma bond middle.left = shore ∧
      orderedReturnShore rotation hG sigma hSigma bond inner.left = shore ∧
      outer.left < middle.left ∧ middle.left < inner.left ∧
      inner.right < middle.right ∧ middle.right < outer.right

/-- A residual-return stack deeper than two is not merely an abstract list:
it contains three literal physical return chords on one shore, in strict
nesting order. -/
theorem strictlyNestedReturnTriple_of_deep_stack
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (hdeep : ∃ shore cut,
      2 < (((residualReturnSweepData rotation minimal hG sigma hSigma bond).family
        shore).stackAt cut).length) :
    StrictlyNestedReturnTriple rotation hG sigma hSigma bond := by
  rcases strictlyNestedReturnFamily_of_deep_stack
      rotation minimal hG sigma hSigma bond 2 hdeep with
    ⟨shore, chord, hshore, hnested⟩
  have hzeroOne := hnested (0 : Fin 3) (1 : Fin 3) (by decide)
  have honeTwo := hnested (1 : Fin 3) (2 : Fin 3) (by decide)
  exact ⟨shore, chord 0, chord 1, chord 2,
    hshore 0, hshore 1, hshore 2,
    hzeroOne.1, honeTwo.1, honeTwo.2, hzeroOne.2⟩

/-- Four physical residual returns on one facial shore, in strict nesting
order.  The outer and inner guards orient the two middle separators and leave
the shallow return path as literal material between them. -/
def StrictlyNestedReturnQuadruple
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second) :
    Prop :=
  ∃ (shore : Bool)
      (outer shallow deep inner : OrderedReturnChord
        (orderedSiteReturnPairing hG sigma hSigma bond.site)),
    orderedReturnShore rotation hG sigma hSigma bond outer.left = shore ∧
      orderedReturnShore rotation hG sigma hSigma bond shallow.left = shore ∧
      orderedReturnShore rotation hG sigma hSigma bond deep.left = shore ∧
      orderedReturnShore rotation hG sigma hSigma bond inner.left = shore ∧
      outer.left < shallow.left ∧ shallow.left < deep.left ∧
      deep.left < inner.left ∧ inner.right < deep.right ∧
      deep.right < shallow.right ∧ shallow.right < outer.right

/-- Stack depth at least four supplies the guarded nested pair used to prove
strict material between the two middle connected cut shores. -/
theorem strictlyNestedReturnQuadruple_of_deep_stack
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (hdeep : ∃ shore cut,
      3 < (((residualReturnSweepData rotation minimal hG sigma hSigma bond).family
        shore).stackAt cut).length) :
    StrictlyNestedReturnQuadruple rotation hG sigma hSigma bond := by
  rcases strictlyNestedReturnFamily_of_deep_stack
      rotation minimal hG sigma hSigma bond 3 hdeep with
    ⟨shore, chord, hshore, hnested⟩
  have hzeroOne := hnested (0 : Fin 4) (1 : Fin 4) (by decide)
  have honeTwo := hnested (1 : Fin 4) (2 : Fin 4) (by decide)
  have htwoThree := hnested (2 : Fin 4) (3 : Fin 4) (by decide)
  exact ⟨shore, chord 0, chord 1, chord 2, chord 3,
    hshore 0, hshore 1, hshore 2, hshore 3,
    hzeroOne.1, honeTwo.1, htwoThree.1,
    htwoThree.2, honeTwo.2, hzeroOne.2⟩

/-- The deep horn of the carrier-local geometric alternative at depth two
therefore supplies the literal nested return triple consumed by separator
geometry. -/
theorem strictlyNestedReturnTriple_of_nestedCarrierDeepReturnStack
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (hdeep : HasNestedCarrierDeepReturnStack
      rotation minimal hG sigma hSigma bond 2) :
    StrictlyNestedReturnTriple rotation hG sigma hSigma bond := by
  rcases hdeep with ⟨_outer, _inner, _hshore, _hleft, _hright,
    shore, cut, _hcut, hdepth⟩
  exact strictlyNestedReturnTriple_of_deep_stack
    rotation minimal hG sigma hSigma bond ⟨shore, cut, hdepth⟩

/-- The depth-three carrier horn supplies the four guarded physical returns
needed for strict connected-shore nesting. -/
theorem strictlyNestedReturnQuadruple_of_nestedCarrierDeepReturnStack
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (hdeep : HasNestedCarrierDeepReturnStack
      rotation minimal hG sigma hSigma bond 3) :
    StrictlyNestedReturnQuadruple rotation hG sigma hSigma bond := by
  rcases hdeep with ⟨_outer, _inner, _hshore, _hleft, _hright,
    shore, cut, _hcut, hdepth⟩
  exact strictlyNestedReturnQuadruple_of_deep_stack
    rotation minimal hG sigma hSigma bond ⟨shore, cut, hdepth⟩

end

end ResidualReturnNestedFamily

end Mettapedia.GraphTheory.FourColor.Compositional
