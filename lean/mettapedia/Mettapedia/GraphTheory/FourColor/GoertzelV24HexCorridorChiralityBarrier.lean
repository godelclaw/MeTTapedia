import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorPumping
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexCorridorFiniteColorTransition

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexCorridorChiralityBarrier

open GoertzelV24CorridorPumping
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24WindingClassification

/-- A state occurs on an exact transfer path when the path factors through
it at some prefix length. -/
def OccursOnExactFlankingTransfer
    {length : Nat} (start finish middle : HexSlabColorState) : Prop :=
  ∃ preLength postLength : Nat,
    preLength + postLength = length ∧
    ExactRelationalTransfer FlankingTaitColorTransition preLength start middle ∧
    ExactRelationalTransfer FlankingTaitColorTransition postLength middle finish

/-- Positive-to-negative chirality reversal along an exact finite slab path
must pass through a zero-winding state. -/
theorem exactFlankingTransfer_positiveToNegative_hasZeroWinding
    {length : Nat} {start finish : HexSlabColorState}
    (hpath : ExactRelationalTransfer FlankingTaitColorTransition
      length start finish)
    (hstart : windingScore start.color = 6)
    (hfinish : windingScore finish.color = -6) :
    ∃ middle : HexSlabColorState,
      OccursOnExactFlankingTransfer (length := length) start finish middle ∧
      windingScore middle.color = 0 := by
  induction hpath with
  | zero =>
      rw [hstart] at hfinish
      norm_num at hfinish
  | @succ tailLength source next target hstep htail ih =>
      have hnextProper : IsProperCyclicColorWord next.color :=
        hstep.2.1.2.2
      have hnextClass := proper_hexagon_windingScore next.color hnextProper
      have hnextNotNegative : windingScore next.color ≠ -6 :=
        (flankingTaitColorTransition_no_direct_chiral_reversal
          source next hstep).1 hstart
      have hfirst : ExactRelationalTransfer FlankingTaitColorTransition
          1 source next := by
        simpa using ExactRelationalTransfer.succ hstep
          (ExactRelationalTransfer.zero next)
      rcases hnextClass with hnextZero | hnextPositive | hnextNegative
      · exact ⟨next, ⟨1, tailLength, by omega, hfirst, htail⟩, hnextZero⟩
      · rcases ih hnextPositive hfinish with
          ⟨middle, ⟨preLength, postLength, hlength, hprePath, hpostPath⟩,
            hmiddle⟩
        refine ⟨middle, ⟨1 + preLength, postLength, by omega, ?_, hpostPath⟩,
          hmiddle⟩
        exact hfirst.comp hprePath
      · exact (hnextNotNegative hnextNegative).elim

/-- Negative-to-positive chirality reversal has the same zero-winding
barrier. -/
theorem exactFlankingTransfer_negativeToPositive_hasZeroWinding
    {length : Nat} {start finish : HexSlabColorState}
    (hpath : ExactRelationalTransfer FlankingTaitColorTransition
      length start finish)
    (hstart : windingScore start.color = -6)
    (hfinish : windingScore finish.color = 6) :
    ∃ middle : HexSlabColorState,
      OccursOnExactFlankingTransfer (length := length) start finish middle ∧
      windingScore middle.color = 0 := by
  induction hpath with
  | zero =>
      rw [hstart] at hfinish
      norm_num at hfinish
  | @succ tailLength source next target hstep htail ih =>
      have hnextProper : IsProperCyclicColorWord next.color :=
        hstep.2.1.2.2
      have hnextClass := proper_hexagon_windingScore next.color hnextProper
      have hnextNotPositive : windingScore next.color ≠ 6 :=
        (flankingTaitColorTransition_no_direct_chiral_reversal
          source next hstep).2 hstart
      have hfirst : ExactRelationalTransfer FlankingTaitColorTransition
          1 source next := by
        simpa using ExactRelationalTransfer.succ hstep
          (ExactRelationalTransfer.zero next)
      rcases hnextClass with hnextZero | hnextPositive | hnextNegative
      · exact ⟨next, ⟨1, tailLength, by omega, hfirst, htail⟩, hnextZero⟩
      · exact (hnextNotPositive hnextPositive).elim
      · rcases ih hnextNegative hfinish with
          ⟨middle, ⟨preLength, postLength, hlength, hprePath, hpostPath⟩,
            hmiddle⟩
        refine ⟨middle, ⟨1 + preLength, postLength, by omega, ?_, hpostPath⟩,
          hmiddle⟩
        exact hfirst.comp hprePath

/-- Sign-independent corridor form: opposite chiral endpoint scores force a
zero-winding state somewhere on the exact transfer path. -/
theorem exactFlankingTransfer_oppositeChirality_hasZeroWinding
    {length : Nat} {start finish : HexSlabColorState}
    (hpath : ExactRelationalTransfer FlankingTaitColorTransition
      length start finish)
    (hopposite :
      (windingScore start.color = 6 ∧ windingScore finish.color = -6) ∨
      (windingScore start.color = -6 ∧ windingScore finish.color = 6)) :
    ∃ middle : HexSlabColorState,
      OccursOnExactFlankingTransfer (length := length) start finish middle ∧
      windingScore middle.color = 0 := by
  rcases hopposite with ⟨hstart, hfinish⟩ | ⟨hstart, hfinish⟩
  · exact exactFlankingTransfer_positiveToNegative_hasZeroWinding
      hpath hstart hfinish
  · exact exactFlankingTransfer_negativeToPositive_hasZeroWinding
      hpath hstart hfinish

/-- A positive chiral raw slab state used to test sharpness of the finite
color-only transition. -/
def positiveChiralTransferWitness : HexSlabColorState :=
  ⟨0, 2, ![.a, .b, .c, .a, .b, .c]⟩

/-- A zero-winding rainbow state between the two opposite chiral witnesses. -/
def meltedTransferWitness : HexSlabColorState :=
  ⟨0, 2, ![.c, .a, .c, .b, .a, .b]⟩

/-- A negative chiral raw slab state. -/
def negativeChiralTransferWitness : HexSlabColorState :=
  ⟨0, 2, ![.c, .b, .a, .c, .b, .a]⟩

theorem positiveChiralTransferWitness_windingScore :
    windingScore positiveChiralTransferWitness.color = 6 := by
  decide

theorem meltedTransferWitness_windingScore :
    windingScore meltedTransferWitness.color = 0 := by
  decide

theorem negativeChiralTransferWitness_windingScore :
    windingScore negativeChiralTransferWitness.color = -6 := by
  decide

theorem positiveToMeltedTransferWitness :
    FlankingTaitColorTransition positiveChiralTransferWitness
      meltedTransferWitness := by
  decide

theorem meltedToNegativeTransferWitness :
    FlankingTaitColorTransition meltedTransferWitness
      negativeChiralTransferWitness := by
  decide

/-- The zero-winding barrier is sharp for the finite color-only relation:
opposite chiral states are joined in exactly two steps through a melted
rainbow word. Thus winding alone cannot supply the corridor-splicing or
self-loop invariant; strand-connectivity data is essential. -/
theorem colorOnlyTransfer_twoStep_chiralReversal :
    ExactRelationalTransfer FlankingTaitColorTransition 2
      positiveChiralTransferWitness negativeChiralTransferWitness := by
  exact ExactRelationalTransfer.succ positiveToMeltedTransferWitness
    (ExactRelationalTransfer.succ meltedToNegativeTransferWitness
      (ExactRelationalTransfer.zero negativeChiralTransferWitness))

end GoertzelV24HexCorridorChiralityBarrier

end Mettapedia.GraphTheory.FourColor
