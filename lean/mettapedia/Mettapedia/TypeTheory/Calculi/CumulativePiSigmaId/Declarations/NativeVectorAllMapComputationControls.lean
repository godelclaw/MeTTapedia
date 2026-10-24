import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllMapComputation

/-!
# Closed controls for the native All cons computation

The controls use the actual joined signature with unknown typed fields and
supplied evidence. They expose the constructor-field prefix, the native
method application and the final pair-map beta step independently.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation TypedEquality

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllMapComputationControls
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeVectorIdentityComparison
open NativeVectorAllTypedMaps
open NativeVectorAllMapComputation

theorem forward_prefix_beta : Equal rules AllComputation.Cons.context
    (.app (.app (.app NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.consCase
      AllComputation.Cons.number) AllComputation.Cons.head) AllComputation.Cons.tail)
    PairSecondMap.subject
    (expandedPrefixType .forward AllComputation.Cons.element AllComputation.Cons.predicate
      AllComputation.Cons.number AllComputation.Cons.head AllComputation.Cons.tail) :=
  cons_prefix_beta_at .forward AllComputation.Cons.element_typed AllComputation.Cons.predicate_typed
    AllComputation.Cons.number_typed AllComputation.Cons.head_typed AllComputation.Cons.tail_typed

theorem forward_method_application : Typed rules AllComputation.Cons.context
    (consRight .forward AllComputation.Cons.element AllComputation.Cons.predicate
      AllComputation.Cons.number AllComputation.Cons.head AllComputation.Cons.tail)
    (.app (.app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
      (source .forward) (target .forward) AllComputation.Cons.element AllComputation.Cons.predicate)
      (NativeNaturalVectorFamilies.succApp AllComputation.Cons.number))
      (NativeNaturalVectorFamilies.vconsApp AllComputation.Cons.element AllComputation.Cons.number
        AllComputation.Cons.head AllComputation.Cons.tail)) :=
  cons_method_apply
    (cons_method_at .forward AllComputation.Cons.element_typed AllComputation.Cons.predicate_typed
      AllComputation.Cons.number_typed AllComputation.Cons.tail_typed)
    AllComputation.Cons.number_typed AllComputation.Cons.head_typed AllComputation.Cons.tail_typed
    (.conv (map_typed_at .forward AllComputation.Cons.element_typed AllComputation.Cons.predicate_typed
      AllComputation.Cons.number_typed AllComputation.Cons.tail_typed)
      (.symm (motive_beta_at .forward AllComputation.Cons.element_typed AllComputation.Cons.predicate_typed
        AllComputation.Cons.number_typed AllComputation.Cons.tail_typed)) (.sort _))

def context := consEvidenceContext .forward
def element : Tower.Tm 6 := .var 5
def predicate : Tower.Tm 6 := .var 4
def number : Tower.Tm 6 := .var 3
def head : Tower.Tm 6 := .var 1
def tail : Tower.Tm 6 := .var 2
def evidence : Tower.Tm 6 := .var 0

theorem element_typed : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel) := .var 5
theorem predicate_typed : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)) := .var 4
theorem number_typed : Typed rules context number NativeNaturalVectorFamilies.natTm := .var 3
theorem head_typed : Typed rules context head element := .var 1
theorem tail_typed : Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number) := .var 2

def sourceTail := NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source .forward) element predicate number tail
def targetTail := NativeVectorAll.Universes.Canonical.allTypeAtUniverse (target .forward) element predicate number tail
def recursive := NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map
  (source .forward) (target .forward) element predicate number tail

theorem predicate_head_formed : Typed rules context (.app predicate head)
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  .sub (.appElim predicate_typed head_typed)
    (.subUniv (by intro valuation; exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)))

theorem source_tail_formed : Typed rules context sourceTail
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  source_all_formed .forward element_typed predicate_typed number_typed tail_typed

theorem target_tail_formed : Typed rules context targetTail
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  target_all_formed .forward element_typed predicate_typed number_typed tail_typed

theorem recursive_typed : Typed rules context recursive (.pi sourceTail (rename wk targetTail)) :=
  map_typed_at .forward element_typed predicate_typed number_typed tail_typed

theorem evidence_pair_typed : Typed rules context evidence (.sigma (.app predicate head) (rename wk sourceTail)) :=
  .conv (cons_evidence_variable_typed .forward)
    (cons_source_equal_at .forward element_typed predicate_typed number_typed head_typed tail_typed) (.sort _)

theorem forward_pair_beta : Equal rules context
    (.app (.app PairSecondMap.subject recursive) evidence)
    (.pair (.fst evidence) (.app recursive (.snd evidence)))
    (.sigma (.app predicate head) (rename wk targetTail)) :=
  PairSecondMap.beta_at signature predicate_head_formed source_tail_formed target_tail_formed recursive_typed evidence_pair_typed

def pairParameters := PairSecondMap.arguments (.app predicate head) sourceTail targetTail

theorem pair_parameters_typed : SubstMor rules
    (PairSecondMap.context NativeVectorAll.Universes.CumulativeElimination.upperLevel
      NativeVectorAll.Universes.CumulativeElimination.upperLevel NativeVectorAll.Universes.CumulativeElimination.upperLevel)
    context pairParameters :=
  PairSecondMap.assignment signature predicate_head_formed source_tail_formed target_tail_formed

theorem pair_function_at_source : Typed rules context recursive
    (subst pairParameters (.pi (.var 1) (.var 1) : Tower.Tm 3)) := recursive_typed

theorem pair_evidence_at_source : Typed rules context evidence
    (subst (consSub recursive pairParameters) (.sigma (.var 3) (.var 3) : Tower.Tm 4)) := evidence_pair_typed

/-- The installed pair equation in its source-substitution presentation. -/
theorem forward_pair_source_beta : Equal rules context
    (.app (.app (subst pairParameters (PairSecondMap.subject : Tower.Tm 3)) recursive) evidence)
    (subst (consSub evidence (consSub recursive pairParameters)) PairSecondMap.body)
    (subst (consSub evidence (consSub recursive pairParameters)) PairSecondMap.resultType) :=
  betaPi_two_substitute
    ((PairSecondMap.displayed_typed NativeVectorAll.Universes.CumulativeElimination.upperLevel
      NativeVectorAll.Universes.CumulativeElimination.upperLevel NativeVectorAll.Universes.CumulativeElimination.upperLevel).of_morphism
        (Declaration.includeMorphism Tower.rules signature)) (.sort _)
    ((PairSecondMap.inner_formed NativeVectorAll.Universes.CumulativeElimination.upperLevel
      NativeVectorAll.Universes.CumulativeElimination.upperLevel NativeVectorAll.Universes.CumulativeElimination.upperLevel).of_morphism
        (Declaration.includeMorphism Tower.rules signature)) (.sort _)
    ((PairSecondMap.body_typed NativeVectorAll.Universes.CumulativeElimination.upperLevel
      NativeVectorAll.Universes.CumulativeElimination.upperLevel NativeVectorAll.Universes.CumulativeElimination.upperLevel).of_morphism
        (Declaration.includeMorphism Tower.rules signature))
    pair_parameters_typed pair_function_at_source pair_evidence_at_source

def methodParameters := NativeVectorAll.Universes.arguments AllComputation.Cons.element AllComputation.Cons.predicate
  AllComputation.Cons.number AllComputation.Cons.tail

theorem method_parameters_typed : SubstMor rules NativeVectorAll.Universes.context AllComputation.Cons.context methodParameters :=
  all_inputs_typed AllComputation.Cons.element_typed AllComputation.Cons.predicate_typed
    AllComputation.Cons.number_typed AllComputation.Cons.tail_typed

theorem method_number_at_source : Typed rules AllComputation.Cons.context AllComputation.Cons.number
    (subst methodParameters NativeNaturalVectorFamilies.natTm) := AllComputation.Cons.number_typed

theorem method_head_at_source : Typed rules AllComputation.Cons.context AllComputation.Cons.head
    (subst (consSub AllComputation.Cons.number methodParameters) (.var 4 : Tower.Tm 5)) := AllComputation.Cons.head_typed

theorem method_tail_at_source : Typed rules AllComputation.Cons.context AllComputation.Cons.tail
    (subst (consSub AllComputation.Cons.head (consSub AllComputation.Cons.number methodParameters))
      (NativeNaturalVectorFamilies.vecApp (.var 5) (.var 1) : Tower.Tm 6)) := AllComputation.Cons.tail_typed

/-- The three-field equation before restoring its displayed target syntax. -/
theorem forward_prefix_source_beta : Equal rules AllComputation.Cons.context
    (.app (.app (.app (subst methodParameters
      (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.consCase : Tower.Tm 4))
        AllComputation.Cons.number) AllComputation.Cons.head) AllComputation.Cons.tail)
    (subst (consSub AllComputation.Cons.tail (consSub AllComputation.Cons.head (consSub AllComputation.Cons.number methodParameters)))
      (PairSecondMap.subject : Tower.Tm 7))
    (subst (consSub AllComputation.Cons.tail (consSub AllComputation.Cons.head (consSub AllComputation.Cons.number methodParameters)))
      (NativeVectorAllMapMethods.innerType NativeVectorAll.Universes.resultLevel NativeVectorAll.Universes.CumulativeElimination.upperLevel)) :=
  betaPi_three_substitute
    (NativeVectorAllMapMethods.method_type_typed _ _ NativeVectorAllMapMethods.lower_tail_upper NativeVectorAllMapMethods.upper_tail_typed) (.sort _)
    (NativeVectorAllMapMethods.pi_upper NativeVectorAllMapMethods.head_domain_typed
      (NativeVectorAllMapMethods.pi_upper NativeVectorAllMapMethods.vector_domain_typed
        (NativeVectorAllMapMethods.inner_type_typed _ _ NativeVectorAllMapMethods.lower_tail_upper NativeVectorAllMapMethods.upper_tail_typed))) (.sort _)
    (NativeVectorAllMapMethods.pi_upper NativeVectorAllMapMethods.vector_domain_typed
      (NativeVectorAllMapMethods.inner_type_typed _ _ NativeVectorAllMapMethods.lower_tail_upper NativeVectorAllMapMethods.upper_tail_typed)) (.sort _)
    (NativeVectorAllMapMethods.inner_typed _ _ NativeVectorAllMapMethods.lower_tail_upper NativeVectorAllMapMethods.upper_tail_typed)
    method_parameters_typed method_number_at_source method_head_at_source method_tail_at_source

#print axioms forward_prefix_beta
#print axioms forward_method_application
#print axioms forward_pair_beta
#print axioms forward_pair_source_beta
#print axioms forward_prefix_source_beta

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllMapComputationControls
