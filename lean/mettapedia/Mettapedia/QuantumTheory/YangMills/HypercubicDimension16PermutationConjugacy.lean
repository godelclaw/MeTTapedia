import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PermutationFixedSector
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Conjugacy invariance of permutation decoration summands

The local-decoration character and the trace-centralizer factor are each
constant on ordinary permutation conjugacy classes.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PermutationConjugacy

open V14HypercubicFDCensus
open HypercubicDimension16CycleBlockDecoration
open HypercubicDimension16PermutationDecorationTransport

theorem indexedDecorationCharacter_isConj
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (h : Hypercubic4) (derivativeBudget targetDegree : ℕ)
    {left right : Equiv.Perm Label} (conjugate : IsConj left right) :
    indexedDecorationCharacter h left derivativeBudget targetDegree =
      indexedDecorationCharacter h right derivativeBudget targetDegree := by
  obtain ⟨transport, transported⟩ := isConj_iff.mp conjugate
  calc
    indexedDecorationCharacter h left derivativeBudget targetDegree =
        indexedDecorationCharacter h (transport.permCongr left)
          derivativeBudget targetDegree :=
      indexedDecorationCharacter_permCongr transport h left
        derivativeBudget targetDegree
    _ = indexedDecorationCharacter h right derivativeBudget targetDegree := by
      rw [Equiv.permCongr_eq_mul, transported]

theorem natCardCentralizer_isConj
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    {left right : Equiv.Perm Label} (conjugate : IsConj left right) :
    Nat.card (Subgroup.centralizer
        ({left} : Set (Equiv.Perm Label))) =
      Nat.card (Subgroup.centralizer
        ({right} : Set (Equiv.Perm Label))) := by
  have cycleTypeEq :=
    (Equiv.Perm.isConj_iff_cycleType_eq.mp conjugate)
  rw [Equiv.Perm.nat_card_centralizer,
    Equiv.Perm.nat_card_centralizer, cycleTypeEq]

theorem centralizerDecorationSummand_isConj
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (h : Hypercubic4) (derivativeBudget targetDegree : ℕ)
    {left right : Equiv.Perm Label} (conjugate : IsConj left right) :
    Nat.card (Subgroup.centralizer
        ({left} : Set (Equiv.Perm Label))) *
        indexedDecorationCharacter h left derivativeBudget targetDegree =
      Nat.card (Subgroup.centralizer
        ({right} : Set (Equiv.Perm Label))) *
        indexedDecorationCharacter h right derivativeBudget targetDegree := by
  rw [natCardCentralizer_isConj conjugate,
    indexedDecorationCharacter_isConj h derivativeBudget targetDegree
      conjugate]

end HypercubicDimension16PermutationConjugacy
end YangMills
end QuantumTheory
end Mettapedia
