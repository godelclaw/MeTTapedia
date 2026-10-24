import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllInverseMotive
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeIdentityPairApplication

/-!
# Identity evidence for the All inverse induction methods

The nil method uses the proved round-trip equation and reflexivity at the
supplied evidence. The cons method's carrier is reconstructed from its
head and tail; identity of the recursive tail is lifted with the existing
checked native pair-congruence program.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation TypedEquality

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllInverseMethods
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeVectorIdentityComparison
open NativeVectorAllTypedMaps
open NativeVectorAllMapComputation
open NativeVectorAllMapInverse

theorem nil_identity_at (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate evidence : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (evidenceTyped : Typed rules context evidence
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate
        NativeNaturalVectorFamilies.zeroTm (NativeNaturalVectorFamilies.vnilApp element))) :
    Typed rules context (.refl evidence)
      (.id (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate
        NativeNaturalVectorFamilies.zeroTm (NativeNaturalVectorFamilies.vnilApp element))
        (roundtrip direction element predicate NativeNaturalVectorFamilies.zeroTm
          (NativeNaturalVectorFamilies.vnilApp element) evidence) evidence) := by
  have carrierFormed := source_all_formed direction elementTyped predicateTyped
    (Congruence.NaturalControl.zero_typed context) (.appElim (primitive_typed context 5) elementTyped)
  have same := roundtrip_nil_equal direction elementTyped predicateTyped evidenceTyped
  exact .conv (.reflIntro evidenceTyped)
    (.idCong (.refl carrierFormed) (.sort _) (.symm same) (.refl evidenceTyped)) (.sort _)

def nilCase {n : Nat} : Tower.Tm n := .lam (.refl (.var 0))

def nilContext (direction : Direction) : Tower.Ctx 5 :=
  .snoc NativeVectorAll.Universes.context (nilCarrier (source direction))

theorem nil_variable_typed (direction : Direction) : Typed rules (nilContext direction) (.var 0)
    (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) (.var 4) (.var 3)
      NativeNaturalVectorFamilies.zeroTm (NativeNaturalVectorFamilies.vnilApp (.var 4))) := by
  have checked := Derivable.var (R := rules) (Γ := nilContext direction) 0
  change Typed rules (nilContext direction) (.var 0) (rename wk (nilCarrier (source direction))) at checked
  unfold nilCarrier at checked
  rw [NativeVectorAllInverseMotive.rename_all] at checked
  exact checked

theorem nil_method_typed (direction : Direction) : Typed rules NativeVectorAll.Universes.context nilCase
    (NativeVectorAllInverseMotive.goalType direction (.var 3) (.var 2)
      NativeNaturalVectorFamilies.zeroTm (NativeNaturalVectorFamilies.vnilApp (.var 3))) := by
  have body := nil_identity_at direction (context := nilContext direction) (element := .var 4) (predicate := .var 3)
    (.var 4) (.var 3) (nil_variable_typed direction)
  refine Derivable.lamIntro
    (NativeVectorAllInverseMotive.goal_type_formed direction AllComputation.Nil.element_typed AllComputation.Nil.predicate_typed
      (Congruence.NaturalControl.zero_typed _) AllComputation.Nil.nil_typed) (.sort _) ?_
  change Typed rules (nilContext direction) (.refl (.var 0))
    (.id (rename wk (nilCarrier (source direction)))
      (roundtrip direction (.var 4) (.var 3) (rename wk NativeNaturalVectorFamilies.zeroTm)
        (rename wk (NativeNaturalVectorFamilies.vnilApp (.var 3))) (.var 0)) (.var 0))
  unfold nilCarrier
  rw [NativeVectorAllInverseMotive.rename_all]
  exact body

def tailFamily {n : Nat} (direction : Direction) (element predicate number tail : Tower.Tm n) : Tower.Tm n :=
  .lam (rename wk (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate number tail))

theorem rename_tailFamily {n m : Nat} (rho : Ren n m) (direction : Direction)
    (element predicate number tail : Tower.Tm n) :
    rename rho (tailFamily direction element predicate number tail) =
      tailFamily direction (rename rho element) (rename rho predicate) (rename rho number) (rename rho tail) := by
  change Tm.lam (rename (liftRen rho) (rename wk _)) = _
  rw [TypedEquality.rename_liftRen_wk, NativeVectorAllInverseMotive.rename_all]
  rfl

def consProof {n : Nat} (direction : Direction)
    (element predicate number head tail evidence hypothesis : Tower.Tm n) : Tower.Tm n :=
  NativeIdentityPairApplication.application (.app predicate head) (tailFamily direction element predicate number tail)
    (.fst evidence) (roundtrip direction element predicate number tail (.snd evidence)) (.snd evidence)
    (.app hypothesis (.snd evidence))

section Cons

variable (direction : Direction) {n : Nat} {context : Tower.Ctx n}
  {element predicate number head tail evidence hypothesis : Tower.Tm n}
  (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
  (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
  (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
  (headTyped : Typed rules context head element)
  (tailTyped : Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number))
  (evidenceTyped : Typed rules context evidence (consCarrier (source direction) element predicate number head tail))
  (hypothesisTyped : Typed rules context hypothesis
    (NativeVectorAllInverseMotive.goalType direction element predicate number tail))

include predicateTyped headTyped in
theorem head_carrier_formed : Typed rules context (.app predicate head)
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  .sub (.appElim predicateTyped headTyped)
    (.subUniv (by intro valuation; exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)))

include predicateTyped headTyped in
theorem tail_family_type_formed : Typed rules context
    (.pi (.app predicate head) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel))
    (sortTm (.max NativeVectorAll.Universes.CumulativeElimination.upperLevel
      (.succ NativeVectorAll.Universes.CumulativeElimination.upperLevel))) :=
  .piForm (head_carrier_formed predicateTyped headTyped) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

include elementTyped predicateTyped numberTyped headTyped tailTyped in
theorem tail_family_typed : Typed rules context (tailFamily direction element predicate number tail)
    (.pi (.app predicate head) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel)) :=
  .lamIntro (tail_family_type_formed predicateTyped headTyped) (.sort _)
    (source_all_formed direction elementTyped predicateTyped numberTyped tailTyped).weaken

include elementTyped predicateTyped numberTyped headTyped tailTyped in
theorem tail_family_beta {value : Tower.Tm n} (valueTyped : Typed rules context value (.app predicate head)) :
    Equal rules context (.app (tailFamily direction element predicate number tail) value)
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate number tail)
      (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  have beta := Derivable.betaPi (tail_family_type_formed predicateTyped headTyped) (.sort _)
    (source_all_formed direction elementTyped predicateTyped numberTyped tailTyped).weaken valueTyped
  rw [inst0_rename_wk] at beta
  simpa only [tailFamily, sortTm, inst0, subst] using beta

include elementTyped predicateTyped numberTyped headTyped tailTyped in
theorem pair_carrier_equal : Equal rules context
    (Congruence.Pair.carrier (.app predicate head) (tailFamily direction element predicate number tail))
    (consPair (source direction) element predicate number head tail)
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  have vectorWeak : Typed rules (.snoc context (.app predicate head)) (rename wk tail)
      (NativeNaturalVectorFamilies.vecApp (rename wk element) (rename wk number)) := by
    simpa only [NativeNaturalVectorFamilies.rename_vecApp] using tailTyped.weaken
  have beta := tail_family_beta direction elementTyped.weaken predicateTyped.weaken numberTyped.weaken
    headTyped.weaken vectorWeak (value := .var 0) (.var 0)
  rw [← rename_tailFamily, ← NativeVectorAllInverseMotive.rename_all] at beta
  refine Derivable.subEq (.sigmaCong (.refl (head_carrier_formed predicateTyped headTyped)) (.sort _)
    beta (.sort _) (.sorts _ _)) (.subUniv ?_)
  intro valuation
  exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩

include elementTyped predicateTyped numberTyped headTyped tailTyped evidenceTyped in
theorem supplied_pair_eta : Equal rules context (.pair (.fst evidence) (.snd evidence)) evidence
    (consPair (source direction) element predicate number head tail) := by
  have supplied := Derivable.conv evidenceTyped
    (cons_source_equal_at direction elementTyped predicateTyped numberTyped headTyped tailTyped) (.sort _)
  have firstTyped := cons_head_typed direction elementTyped predicateTyped numberTyped headTyped tailTyped evidenceTyped
  have secondTyped := cons_tail_typed direction elementTyped predicateTyped numberTyped headTyped tailTyped evidenceTyped
  have tailAt : Typed rules context (.snd evidence)
      (inst0 (.fst evidence) (rename wk
        (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate number tail))) := by
    rw [inst0_rename_wk]
    exact secondTyped
  have formed := source_cons_pair_formed direction elementTyped predicateTyped numberTyped headTyped tailTyped
  have expanded := Derivable.pairIntro formed (.sort _) firstTyped tailAt
  have firstBeta := Derivable.betaFst formed (.sort _) firstTyped tailAt
  have secondBeta := Derivable.betaSnd formed (.sort _) firstTyped tailAt
  have fiber : Equal rules context (.snd (.pair (.fst evidence) (.snd evidence))) (.snd evidence)
      (inst0 (.fst (.pair (.fst evidence) (.snd evidence))) (rename wk
        (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate number tail))) := by
    rw [inst0_rename_wk]
    simpa only [inst0_rename_wk] using secondBeta
  exact .etaSigma expanded supplied firstBeta fiber

include elementTyped predicateTyped numberTyped headTyped tailTyped evidenceTyped hypothesisTyped in
theorem cons_identity_at : Typed rules context
    (consProof direction element predicate number head tail evidence hypothesis)
    (.id (consCarrier (source direction) element predicate number head tail)
      (roundtrip direction element predicate (NativeNaturalVectorFamilies.succApp number)
        (NativeNaturalVectorFamilies.vconsApp element number head tail) evidence) evidence) := by
  have firstTyped := cons_head_typed direction elementTyped predicateTyped numberTyped headTyped tailTyped evidenceTyped
  have secondTyped := cons_tail_typed direction elementTyped predicateTyped numberTyped headTyped tailTyped evidenceTyped
  have recursiveTyped := roundtrip_typed direction elementTyped predicateTyped numberTyped tailTyped secondTyped
  have recursiveProof := NativeVectorAllInverseMotive.goal_apply_typed direction hypothesisTyped secondTyped
  have familyBeta := tail_family_beta direction elementTyped predicateTyped numberTyped headTyped tailTyped firstTyped
  have atFamilyLeft := Derivable.conv recursiveTyped (.symm familyBeta) (.sort _)
  have atFamilyRight := Derivable.conv secondTyped (.symm familyBeta) (.sort _)
  have atFamilyProof := Derivable.conv recursiveProof
    (.idCong (.symm familyBeta) (.sort _) (.refl recursiveTyped) (.refl secondTyped)) (.sort _)
  have pairProof := NativeIdentityPairApplication.apply_typed (head_carrier_formed predicateTyped headTyped)
    (tail_family_typed direction elementTyped predicateTyped numberTyped headTyped tailTyped)
    firstTyped atFamilyLeft atFamilyRight atFamilyProof
  have pairCarrier := pair_carrier_equal direction elementTyped predicateTyped numberTyped headTyped tailTyped
  have carrierToSource := Derivable.trans pairCarrier
    (.symm (cons_source_equal_at direction elementTyped predicateTyped numberTyped headTyped tailTyped))
  have leftEndpoint := Derivable.convEq
    (.symm (roundtrip_cons_equal direction elementTyped predicateTyped numberTyped headTyped tailTyped evidenceTyped))
    (.symm carrierToSource) (.sort _)
  have rightEndpoint := Derivable.convEq
    (supplied_pair_eta direction elementTyped predicateTyped numberTyped headTyped tailTyped evidenceTyped)
    (.symm pairCarrier) (.sort _)
  exact .conv pairProof (.idCong carrierToSource (.sort _) leftEndpoint rightEndpoint) (.sort _)

end Cons

def hypothesisType (direction : Direction) : Tower.Tm 7 :=
  NativeVectorAllInverseMotive.goalType direction (.var 6) (.var 5) (.var 2) (.var 0)

def constructorGoal (direction : Direction) : Tower.Tm 7 :=
  NativeVectorAllInverseMotive.goalType direction (.var 6) (.var 5) (NativeNaturalVectorFamilies.succApp (.var 2))
    (NativeNaturalVectorFamilies.vconsApp (.var 6) (.var 2) (.var 1) (.var 0))

def hypothesisContext (direction : Direction) : Tower.Ctx 8 :=
  .snoc NativeVectorAllMapMethods.context (hypothesisType direction)

def bodyCarrier (direction : Direction) : Tower.Tm 8 :=
  consCarrier (source direction) (.var 7) (.var 6) (.var 3) (.var 2) (.var 1)

def bodyContext (direction : Direction) : Tower.Ctx 9 := .snoc (hypothesisContext direction) (bodyCarrier direction)

def consBody (direction : Direction) : Tower.Tm 9 :=
  consProof direction (.var 8) (.var 7) (.var 4) (.var 3) (.var 2) (.var 0) (.var 1)

def consCase {n : Nat} (direction : Direction) (element predicate : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.lam (.lam (.lam (consProof direction
    (rename wk (rename wk (rename wk (rename wk (rename wk element)))))
    (rename wk (rename wk (rename wk (rename wk (rename wk predicate)))))
    (.var (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0)))))
    (.var (Fin.succ (Fin.succ (Fin.succ 0)))) (.var (Fin.succ (Fin.succ 0))) (.var 0) (.var (Fin.succ 0)))))))

def expandedConsType (direction : Direction) : Tower.Tm 4 :=
  .pi NativeNaturalVectorFamilies.natTm (.pi (.var 4)
    (.pi (NativeNaturalVectorFamilies.vecApp (.var 5) (.var 1))
      (.pi (hypothesisType direction) (rename wk (constructorGoal direction)))))

theorem hypothesis_formed (direction : Direction) : Typed rules NativeVectorAllMapMethods.context (hypothesisType direction)
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  NativeVectorAllInverseMotive.goal_type_formed direction (context := NativeVectorAllMapMethods.context)
    (element := .var 6) (predicate := .var 5) (number := .var 2) (vector := .var 0)
    (.var 6) (.var 5) (.var 2) (.var 0)

theorem constructor_goal_formed (direction : Direction) : Typed rules NativeVectorAllMapMethods.context (constructorGoal direction)
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  NativeVectorAllInverseMotive.goal_type_formed direction (context := NativeVectorAllMapMethods.context)
    (element := .var 6) (predicate := .var 5) (.var 6) (.var 5)
    NativeVectorAllTypedMaps.successor_typed NativeVectorAllTypedMaps.constructor_typed

theorem hypothesis_context_formed (direction : Direction) : Normalization.CtxFormed rules (hypothesisContext direction) :=
  .snoc NativeVectorAllMapMethods.context_formed ⟨_, .sort _, hypothesis_formed direction⟩

theorem body_carrier_formed (direction : Direction) : Typed rules (hypothesisContext direction) (bodyCarrier direction)
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  source_all_formed direction (context := hypothesisContext direction) (element := .var 7) (predicate := .var 6)
    (.var 7) (.var 6) (.appElim (primitive_typed _ 2) (.var 3))
    (cons_constructor_typed (context := hypothesisContext direction) (element := .var 7) (predicate := .var 6)
      (number := .var 3) (head := .var 2) (tail := .var 1) (.var 7) (.var 6) (.var 3) (.var 2) (.var 1))

theorem body_context_formed (direction : Direction) : Normalization.CtxFormed rules (bodyContext direction) :=
  .snoc (hypothesis_context_formed direction) ⟨_, .sort _, body_carrier_formed direction⟩

theorem body_evidence_typed (direction : Direction) : Typed rules (bodyContext direction) (.var 0)
    (consCarrier (source direction) (.var 8) (.var 7) (.var 4) (.var 3) (.var 2)) := by
  have checked := Derivable.var (R := rules) (Γ := bodyContext direction) 0
  change Typed rules (bodyContext direction) (.var 0) (rename wk (bodyCarrier direction)) at checked
  unfold bodyCarrier at checked
  rw [rename_consCarrier] at checked
  exact checked

theorem body_hypothesis_typed (direction : Direction) : Typed rules (bodyContext direction) (.var 1)
    (NativeVectorAllInverseMotive.goalType direction (.var 8) (.var 7) (.var 4) (.var 2)) := by
  have checked := Derivable.var (R := rules) (Γ := bodyContext direction) 1
  change Typed rules (bodyContext direction) (.var 1) (rename wk (rename wk (hypothesisType direction))) at checked
  unfold hypothesisType at checked
  rw [NativeVectorAllInverseMotive.rename_goalType, NativeVectorAllInverseMotive.rename_goalType] at checked
  exact checked

theorem cons_body_typed (direction : Direction) : Typed rules (bodyContext direction) (consBody direction)
    (.id (consCarrier (source direction) (.var 8) (.var 7) (.var 4) (.var 3) (.var 2))
      (roundtrip direction (.var 8) (.var 7) (NativeNaturalVectorFamilies.succApp (.var 4))
        (NativeNaturalVectorFamilies.vconsApp (.var 8) (.var 4) (.var 3) (.var 2)) (.var 0)) (.var 0)) :=
  cons_identity_at direction (context := bodyContext direction)
    (element := .var 8) (predicate := .var 7) (number := .var 4) (head := .var 3) (tail := .var 2)
    (.var 8) (.var 7) (.var 4) (.var 3) (.var 2) (body_evidence_typed direction) (body_hypothesis_typed direction)

theorem constructor_goal_weaken (direction : Direction) : rename wk (constructorGoal direction) =
    NativeVectorAllInverseMotive.goalType direction (.var 7) (.var 6) (NativeNaturalVectorFamilies.succApp (.var 3))
      (NativeNaturalVectorFamilies.vconsApp (.var 7) (.var 3) (.var 2) (.var 1)) := by
  rw [constructorGoal, NativeVectorAllInverseMotive.rename_goalType]
  rfl

theorem cons_value_method_typed (direction : Direction) : Typed rules (hypothesisContext direction)
    (.lam (consBody direction)) (rename wk (constructorGoal direction)) := by
  rw [constructor_goal_weaken]
  have formed := (constructor_goal_formed direction).weaken (extension := hypothesisType direction)
  rw [constructor_goal_weaken] at formed
  refine Derivable.lamIntro formed (.sort _) ?_
  change Typed rules (bodyContext direction) (consBody direction)
    (.id (rename wk (bodyCarrier direction))
      (roundtrip direction (.var 8) (.var 7) (rename wk (NativeNaturalVectorFamilies.succApp (.var 3)))
        (rename wk (NativeNaturalVectorFamilies.vconsApp (.var 7) (.var 3) (.var 2) (.var 1))) (.var 0)) (.var 0))
  unfold bodyCarrier
  rw [rename_consCarrier]
  exact cons_body_typed direction

theorem expanded_cons_type_formed (direction : Direction) : Typed rules NativeVectorAll.Universes.context (expandedConsType direction)
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  NativeVectorAllMapMethods.pi_upper NativeVectorAllMapMethods.length_domain_typed
    (NativeVectorAllMapMethods.pi_upper NativeVectorAllMapMethods.head_domain_typed
      (NativeVectorAllMapMethods.pi_upper NativeVectorAllMapMethods.vector_domain_typed
        (NativeVectorAllMapMethods.pi_upper (hypothesis_formed direction) (constructor_goal_formed direction).weaken)))

theorem expanded_cons_method_typed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    (consCase direction (.var 3) (.var 2)) (expandedConsType direction) :=
  .lamIntro (expanded_cons_type_formed direction) (.sort _)
    (.lamIntro (NativeVectorAllMapMethods.pi_upper NativeVectorAllMapMethods.head_domain_typed
      (NativeVectorAllMapMethods.pi_upper NativeVectorAllMapMethods.vector_domain_typed
        (NativeVectorAllMapMethods.pi_upper (hypothesis_formed direction) (constructor_goal_formed direction).weaken))) (.sort _)
      (.lamIntro (NativeVectorAllMapMethods.pi_upper NativeVectorAllMapMethods.vector_domain_typed
        (NativeVectorAllMapMethods.pi_upper (hypothesis_formed direction) (constructor_goal_formed direction).weaken)) (.sort _)
        (.lamIntro (NativeVectorAllMapMethods.pi_upper (hypothesis_formed direction) (constructor_goal_formed direction).weaken)
          (.sort _) (cons_value_method_typed direction))))

#print axioms nil_identity_at
#print axioms nil_method_typed
#print axioms cons_identity_at
#print axioms expanded_cons_method_typed

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllInverseMethods
