import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllInverseMethods

/-!
# Object-level inverse of the All universe maps

The original Vector eliminator assembles the checked identity-producing
nil and cons methods over an unknown length and vector. The resulting term
proves identity of the supplied evidence with its round trip. Identity
inhabitation, judgmental equality and raw syntax equality remain distinct.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation TypedEquality

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllInverse
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeVectorIdentityComparison
open NativeVectorAllTypedMaps
open NativeVectorAllMapComputation
open NativeVectorAllMapInverse

def nilInterface (direction : Direction) : Tower.Tm 4 :=
  nilTypeAt (.var 3) (NativeVectorAllInverseMotive.motive direction (.var 3) (.var 2))

def consInterface (direction : Direction) : Tower.Tm 4 :=
  .pi NativeNaturalVectorFamilies.natTm (.pi (.var 4)
    (.pi (NativeNaturalVectorFamilies.vecApp (.var 5) (.var 1))
      (.pi (.app (.app (NativeVectorAllInverseMotive.motive direction (.var 6) (.var 5)) (.var 2)) (.var 0))
        (rename wk (.app (.app (NativeVectorAllInverseMotive.motive direction (.var 6) (.var 5))
          (NativeNaturalVectorFamilies.succApp (.var 2)))
          (NativeNaturalVectorFamilies.vconsApp (.var 6) (.var 2) (.var 1) (.var 0)))))))

theorem cons_interface_readback (direction : Direction) :
    consTypeAt (.var 3) (NativeVectorAllInverseMotive.motive direction (.var 3) (.var 2)) = consInterface direction := by
  norm_num [consTypeAt, consInterface, NativeVectorAllInverseMotive.rename_motive,
    NativeNaturalVectorFamilies.natTm, NativeNaturalVectorFamilies.vecApp,
    NativeNaturalVectorFamilies.succApp, NativeNaturalVectorFamilies.vconsApp,
    rename, wk, liftRen, Fin.instOfNat, Fin.ofNat, Fin.succ, Fin.cases, Fin.induction, Fin.induction.go]
  repeat' apply And.intro
  all_goals first
    | (apply congrArg₂ (NativeVectorAllInverseMotive.motive direction) <;> apply congrArg Tm.var <;> decide +kernel)
    | decide +kernel

theorem nil_method_typed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    NativeVectorAllInverseMethods.nilCase (nilInterface direction) :=
  .conv (NativeVectorAllInverseMethods.nil_method_typed direction)
    (.symm (NativeVectorAllInverseMotive.motive_beta_at direction AllComputation.Nil.element_typed
      AllComputation.Nil.predicate_typed (Congruence.NaturalControl.zero_typed _) AllComputation.Nil.nil_typed)) (.sort _)

theorem cons_types_equal (direction : Direction) : Equal rules NativeVectorAll.Universes.context
    (consInterface direction) (NativeVectorAllInverseMethods.expandedConsType direction)
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  have tailBeta := NativeVectorAllInverseMotive.motive_beta_at direction (context := NativeVectorAllMapMethods.context)
    (element := .var 6) (predicate := .var 5) (number := .var 2) (vector := .var 0)
    (.var 6) (.var 5) (.var 2) (.var 0)
  have constructorBeta := NativeVectorAllInverseMotive.motive_beta_at direction (context := NativeVectorAllMapMethods.context)
    (element := .var 6) (predicate := .var 5) (.var 6) (.var 5)
    NativeVectorAllTypedMaps.successor_typed NativeVectorAllTypedMaps.constructor_typed
  exact NativeVectorAllMapMethods.pi_equal_upper (.refl NativeVectorAllMapMethods.length_domain_typed)
    (NativeVectorAllMapMethods.pi_equal_upper (.refl NativeVectorAllMapMethods.head_domain_typed)
      (NativeVectorAllMapMethods.pi_equal_upper (.refl NativeVectorAllMapMethods.vector_domain_typed)
        (NativeVectorAllMapMethods.pi_equal_upper tailBeta constructorBeta.weaken)))

theorem cons_method_typed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    (NativeVectorAllInverseMethods.consCase direction (.var 3) (.var 2))
    (consTypeAt (.var 3) (NativeVectorAllInverseMotive.motive direction (.var 3) (.var 2))) := by
  rw [cons_interface_readback]
  exact .conv (NativeVectorAllInverseMethods.expanded_cons_method_typed direction)
    (.symm (cons_types_equal direction)) (.sort _)

def program {n : Nat} (direction : Direction) (element predicate number vector : Tower.Tm n) : Tower.Tm n :=
  NativeNaturalVectorFamilies.vecEliminateApp element (NativeVectorAllInverseMotive.motive direction element predicate)
    NativeVectorAllInverseMethods.nilCase (NativeVectorAllInverseMethods.consCase direction element predicate) number vector

theorem after_nil_typed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    (.app (.app (.app (.const NativeNaturalVectorFamilies.vecEliminateName) (.var 3))
      (NativeVectorAllInverseMotive.motive direction (.var 3) (.var 2))) NativeVectorAllInverseMethods.nilCase)
    (.pi (consTypeAt (.var 3) (NativeVectorAllInverseMotive.motive direction (.var 3) (.var 2)))
      (rename wk (resultTypeAt (.var 3) (NativeVectorAllInverseMotive.motive direction (.var 3) (.var 2))))) := by
  have applied := Derivable.appElim
    (after_motive_generic (context := NativeVectorAll.Universes.context) (element := .var 3)
      (.var 3) (NativeVectorAllInverseMotive.native_motive_typed direction))
    (nil_method_typed direction)
  simpa only [afterMotiveTypeAt, inst0_rename_wk] using applied

theorem after_cons_typed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    (.app (.app (.app (.app (.const NativeNaturalVectorFamilies.vecEliminateName) (.var 3))
      (NativeVectorAllInverseMotive.motive direction (.var 3) (.var 2))) NativeVectorAllInverseMethods.nilCase)
      (NativeVectorAllInverseMethods.consCase direction (.var 3) (.var 2)))
    (resultTypeAt (.var 3) (NativeVectorAllInverseMotive.motive direction (.var 3) (.var 2))) := by
  have applied := Derivable.appElim (after_nil_typed direction) (cons_method_typed direction)
  simpa only [inst0_rename_wk] using applied

theorem program_typed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    (program direction (.var 3) (.var 2) (.var 1) (.var 0))
    (NativeVectorAllInverseMotive.goalType direction (.var 3) (.var 2) (.var 1) (.var 0)) :=
  .conv (result_apply (after_cons_typed direction) (.var 1) (.var 0))
    (NativeVectorAllInverseMotive.motive_beta direction) (.sort _)

def inverse {n : Nat} (direction : Direction) (element predicate number vector evidence : Tower.Tm n) : Tower.Tm n :=
  .app (subst (NativeVectorAll.Universes.arguments element predicate number vector)
    (program direction (.var 3) (.var 2) (.var 1) (.var 0))) evidence

theorem inverse_typed (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number vector evidence : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (vectorTyped : Typed rules context vector (NativeNaturalVectorFamilies.vecApp element number))
    (evidenceTyped : Typed rules context evidence
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate number vector)) :
    Typed rules context (inverse direction element predicate number vector evidence)
      (.id (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate number vector)
        (roundtrip direction element predicate number vector evidence) evidence) := by
  let sigma := NativeVectorAll.Universes.arguments element predicate number vector
  have atInputs := (program_typed direction).substitute
    (all_inputs_typed elementTyped predicateTyped numberTyped vectorTyped)
  have goalReadback : subst sigma (NativeVectorAllInverseMotive.goalType direction (.var 3) (.var 2) (.var 1) (.var 0)) =
      NativeVectorAllInverseMotive.goalType direction element predicate number vector := by
    rw [NativeVectorAllInverseMotive.substitute_goalType]
    rfl
  rw [goalReadback] at atInputs
  exact NativeVectorAllInverseMotive.goal_apply_typed direction atInputs evidenceTyped

#print axioms program_typed
#print axioms inverse_typed

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllInverse
