import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PairSecondMap
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorIdentityComparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.BetaApplication

/-!
# Expanded pair methods for the native All evidence maps

The original five-lambda cons method is typed by installing independently
formed All tail types in the second-component map, then abstracting its
length, head and tail inputs. Both result annotations use the actual joined
Vector/identity signature. The recursive and supplied evidence arguments
have expanded pair interfaces. Typed constructor equations also convert them
to the constructor-indexed All interface. NativeVectorAllTypedMaps assembles
the complete original eliminator applications. The inverse is a separate
obligation.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation TypedEquality

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllMapMethods
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeVectorIdentityComparison

def lengthContext : Tower.Ctx 5 := .snoc NativeVectorAll.Universes.context Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.natTm
def headContext : Tower.Ctx 6 := .snoc lengthContext (.var 4)
def context : Tower.Ctx 7 := .snoc headContext (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.vecApp (.var 5) (.var 1))

def tailType (level : LevelExpr Nat) : Tower.Tm 7 :=
  NativeVectorAll.Universes.Canonical.allTypeAtUniverse level (.var 6) (.var 5) (.var 2) (.var 0)

def innerType (source target : LevelExpr Nat) : Tower.Tm 7 :=
  PairSecondMap.typeAt (.app (.var 5) (.var 1)) (tailType source) (tailType target)

def tailMethodType (source target : LevelExpr Nat) : Tower.Tm 6 :=
  .pi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.vecApp (.var 5) (.var 1)) (innerType source target)

def headMethodType (source target : LevelExpr Nat) : Tower.Tm 5 :=
  .pi (.var 4) (tailMethodType source target)

def methodType (source target : LevelExpr Nat) : Tower.Tm 4 :=
  .pi Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.natTm (headMethodType source target)

theorem lower_tail_typed : Typed rules context (tailType NativeVectorAll.Universes.resultLevel) (sortTm NativeVectorAll.Universes.resultLevel) :=
  lower_all_at (context := context) (element := .var 6) (predicate := .var 5)
    (length := .var 2) (vector := .var 0) (.var 6) (.var 5) (.var 2) (.var 0)

theorem upper_tail_typed : Typed rules context (tailType NativeVectorAll.Universes.CumulativeElimination.upperLevel) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  upper_all_at (context := context) (element := .var 6) (predicate := .var 5)
    (length := .var 2) (vector := .var 0) (.var 6) (.var 5) (.var 2) (.var 0)

theorem lower_tail_upper : Typed rules context (tailType NativeVectorAll.Universes.resultLevel) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  .sub lower_tail_typed (.subUniv (by intro valuation; exact Nat.le_max_left _ _))

theorem head_predicate_typed : Typed rules context (.app (.var 5) (.var 1)) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  refine Derivable.sub (A := sortTm NativeVectorAll.Universes.predicateLevel) (B := sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) ?_ (.subUniv ?_)
  · exact .appElim (A := .var 6) (B := sortTm NativeVectorAll.Universes.predicateLevel) (.var 5) (.var 1)
  · intro valuation
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)

theorem pi_upper {n : Nat} {ambient : Tower.Ctx n}
    {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)}
    (domainTyped : Typed rules ambient domain (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel))
    (codomainTyped : Typed rules (.snoc ambient domain) codomain (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel)) :
    Typed rules ambient (.pi domain codomain) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  refine Derivable.sub (.piForm domainTyped (.sort _) codomainTyped (.sort _) (.sorts _ _))
    (.subUniv ?_)
  intro valuation
  exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem inner_typed (source target : LevelExpr Nat)
    (sourceTyped : Typed rules context (tailType source) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel))
    (targetTyped : Typed rules context (tailType target) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel)) :
    Typed rules context PairSecondMap.subject (innerType source target) :=
  PairSecondMap.instantiate_typed signature head_predicate_typed sourceTyped targetTyped

theorem inner_type_typed (source target : LevelExpr Nat)
    (sourceTyped : Typed rules context (tailType source) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel))
    (targetTyped : Typed rules context (tailType target) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel)) :
    Typed rules context (innerType source target) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  refine Derivable.sub (PairSecondMap.instantiate_type_typed signature
    head_predicate_typed sourceTyped targetTyped) (.subUniv ?_)
  intro valuation
  exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩,
    Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩,
      Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩⟩⟩

theorem vector_domain_typed : Typed rules headContext (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.vecApp (.var 5) (.var 1))
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  refine Derivable.sub (A := sortTm NativeVectorAll.Universes.dataLevel) (B := sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) ?_ (.subUniv ?_)
  · exact .appElim (.appElim (primitive_typed headContext 4) (.var 5)) (.var 1)
  · intro valuation
    exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)

theorem head_domain_typed : Typed rules lengthContext (.var 4) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  .sub (.var 4) (.subUniv (by
    intro valuation
    exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)))

theorem length_domain_typed : Typed rules NativeVectorAll.Universes.context Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.natTm
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  .sub (Congruence.NaturalControl.natural_typed _) (.subUniv (by
    intro valuation; exact Nat.zero_le _))

theorem length_context_formed : Normalization.CtxFormed rules lengthContext :=
  .snoc all_context_formed ⟨_, .sort _, length_domain_typed⟩

theorem head_context_formed : Normalization.CtxFormed rules headContext :=
  .snoc length_context_formed ⟨_, .sort _, head_domain_typed⟩

theorem context_formed : Normalization.CtxFormed rules context :=
  .snoc head_context_formed ⟨_, .sort _, vector_domain_typed⟩

theorem method_type_typed (source target : LevelExpr Nat)
    (sourceTyped : Typed rules context (tailType source) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel))
    (targetTyped : Typed rules context (tailType target) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel)) :
    Typed rules NativeVectorAll.Universes.context (methodType source target) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  pi_upper length_domain_typed (pi_upper head_domain_typed
    (pi_upper vector_domain_typed (inner_type_typed source target sourceTyped targetTyped)))

theorem method_typed (source target : LevelExpr Nat)
    (sourceTyped : Typed rules context (tailType source) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel))
    (targetTyped : Typed rules context (tailType target) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel)) :
    Typed rules NativeVectorAll.Universes.context
      NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.consCase (methodType source target) := by
  refine Derivable.lamIntro (method_type_typed source target sourceTyped targetTyped) (.sort _) ?_
  refine Derivable.lamIntro (pi_upper head_domain_typed
    (pi_upper vector_domain_typed (inner_type_typed source target sourceTyped targetTyped))) (.sort _) ?_
  exact .lamIntro (pi_upper vector_domain_typed
    (inner_type_typed source target sourceTyped targetTyped)) (.sort _)
      (inner_typed source target sourceTyped targetTyped)

theorem forward_method_typed : Typed rules NativeVectorAll.Universes.context
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.consCase
      (methodType NativeVectorAll.Universes.resultLevel NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  method_typed NativeVectorAll.Universes.resultLevel NativeVectorAll.Universes.CumulativeElimination.upperLevel lower_tail_upper upper_tail_typed

theorem backward_method_typed : Typed rules NativeVectorAll.Universes.context
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.consCase
      (methodType NativeVectorAll.Universes.CumulativeElimination.upperLevel NativeVectorAll.Universes.resultLevel) :=
  method_typed NativeVectorAll.Universes.CumulativeElimination.upperLevel NativeVectorAll.Universes.resultLevel upper_tail_typed lower_tail_upper

def constructorType (level : LevelExpr Nat) : Tower.Tm 7 :=
  NativeVectorAll.Universes.Canonical.allTypeAtUniverse level (.var 6) (.var 5)
    (NativeNaturalVectorFamilies.succApp (.var 2))
    (NativeNaturalVectorFamilies.vconsApp (.var 6) (.var 2) (.var 1) (.var 0))

def constructorInnerType (source target : LevelExpr Nat) : Tower.Tm 7 :=
  .pi (.pi (tailType source) (rename wk (tailType target)))
    (rename wk (.pi (constructorType source) (rename wk (constructorType target))))

def constructorMethodType (source target : LevelExpr Nat) : Tower.Tm 4 :=
  .pi NativeNaturalVectorFamilies.natTm (.pi (.var 4)
    (.pi (NativeNaturalVectorFamilies.vecApp (.var 5) (.var 1))
      (constructorInnerType source target)))

def constructorArguments : Sub Tower.Head 5 7 :=
  consSub (.var 1) (consSub (.var 0) (consSub (.var 2)
    (consSub (.var 5) (consSub (.var 6) Fin.elim0))))

theorem constructor_assignment : SubstMor rules AllComputation.Cons.context context constructorArguments := by
  intro index
  fin_cases index
  · exact .var 1
  · exact .var 0
  · exact .var 2
  · exact .var 5
  · exact .var 6

theorem lower_constructor_equal : Equal rules context
    (constructorType NativeVectorAll.Universes.resultLevel)
    (.sigma (.app (.var 5) (.var 1)) (rename wk (tailType NativeVectorAll.Universes.resultLevel)))
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  have linked := AllComputation.Cons.lower_equal.substitute constructor_assignment
  apply Derivable.subEq (B := sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) linked
  exact .subUniv (by intro valuation; exact Nat.le_max_left _ _)

theorem upper_constructor_equal : Equal rules context
    (constructorType NativeVectorAll.Universes.CumulativeElimination.upperLevel)
    (.sigma (.app (.var 5) (.var 1)) (rename wk (tailType NativeVectorAll.Universes.CumulativeElimination.upperLevel)))
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  AllComputation.Cons.upper_equal.substitute constructor_assignment

theorem pi_equal_upper {n : Nat} {ambient : Tower.Ctx n}
    {domain otherDomain : Tower.Tm n} {codomain otherCodomain : Tower.Tm (n + 1)}
    (domains : Equal rules ambient domain otherDomain (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel))
    (codomains : Equal rules (.snoc ambient domain) codomain otherCodomain
      (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel)) :
    Equal rules ambient (.pi domain codomain) (.pi otherDomain otherCodomain)
      (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  refine Derivable.subEq (.piCong domains (.sort _) codomains (.sort _) (.sorts _ _)) (.subUniv ?_)
  intro valuation
  exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem method_types_equal (source target : LevelExpr Nat)
    (sourceTyped : Typed rules context (tailType source) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel))
    (targetTyped : Typed rules context (tailType target) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel))
    (sourceEquation : Equal rules context (constructorType source)
      (.sigma (.app (.var 5) (.var 1)) (rename wk (tailType source)))
      (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel))
    (targetEquation : Equal rules context (constructorType target)
      (.sigma (.app (.var 5) (.var 1)) (rename wk (tailType target)))
      (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel)) :
    Equal rules NativeVectorAll.Universes.context (constructorMethodType source target)
      (methodType source target) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  have arrows : Equal rules context
      (.pi (constructorType source) (rename wk (constructorType target)))
      (.pi (.sigma (.app (.var 5) (.var 1)) (rename wk (tailType source)))
        (rename wk (.sigma (.app (.var 5) (.var 1)) (rename wk (tailType target)))))
      (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
    pi_equal_upper sourceEquation targetEquation.weaken
  have recursiveType : Typed rules context (.pi (tailType source) (rename wk (tailType target)))
      (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
    pi_upper sourceTyped targetTyped.weaken
  have inner : Equal rules context (constructorInnerType source target) (innerType source target)
      (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
    rw [innerType, PairSecondMap.typeAt_expanded]
    exact pi_equal_upper (.refl recursiveType) arrows.weaken
  exact pi_equal_upper (.refl length_domain_typed)
    (pi_equal_upper (.refl head_domain_typed) (pi_equal_upper (.refl vector_domain_typed) inner))

theorem forward_constructor_method_typed : Typed rules NativeVectorAll.Universes.context
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.consCase
      (constructorMethodType NativeVectorAll.Universes.resultLevel NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  .conv forward_method_typed (.symm (method_types_equal _ _ lower_tail_upper upper_tail_typed
    lower_constructor_equal upper_constructor_equal)) (.sort _)

theorem backward_constructor_method_typed : Typed rules NativeVectorAll.Universes.context
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.consCase
      (constructorMethodType NativeVectorAll.Universes.CumulativeElimination.upperLevel NativeVectorAll.Universes.resultLevel) :=
  .conv backward_method_typed (.symm (method_types_equal _ _ upper_tail_typed lower_tail_upper
    upper_constructor_equal lower_constructor_equal)) (.sort _)

def nilMethodType (source target : LevelExpr Nat) : Tower.Tm 4 :=
  NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.functionType source target
    (.var 3) (.var 2) NativeNaturalVectorFamilies.zeroTm
    (NativeNaturalVectorFamilies.vnilApp (.var 3))

theorem nil_identity_typed : Typed rules NativeVectorAll.Universes.context (.lam (.var 0))
    (.pi NativeVectorAll.unitType (rename wk NativeVectorAll.unitType)) := by
  refine Derivable.lamIntro (pi_upper
    (AllComputation.Nil.unit_typed NativeVectorAll.Universes.CumulativeElimination.upperLevel)
    (AllComputation.Nil.unit_typed NativeVectorAll.Universes.CumulativeElimination.upperLevel).weaken)
    (.sort _) ?_
  exact .var 0

theorem lower_nil_equal : Equal rules NativeVectorAll.Universes.context
    (NativeVectorAll.Universes.Canonical.allTypeAtUniverse NativeVectorAll.Universes.resultLevel
      (.var 3) (.var 2) NativeNaturalVectorFamilies.zeroTm
      (NativeNaturalVectorFamilies.vnilApp (.var 3))) NativeVectorAll.unitType
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  .subEq AllComputation.Nil.lower_equal (.subUniv (by intro valuation; exact Nat.le_max_left _ _))

theorem forward_nil_method_typed : Typed rules NativeVectorAll.Universes.context (.lam (.var 0))
    (nilMethodType NativeVectorAll.Universes.resultLevel NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  .conv nil_identity_typed
    (.symm (pi_equal_upper lower_nil_equal AllComputation.Nil.upper_equal.weaken)) (.sort _)

theorem backward_nil_method_typed : Typed rules NativeVectorAll.Universes.context (.lam (.var 0))
    (nilMethodType NativeVectorAll.Universes.CumulativeElimination.upperLevel NativeVectorAll.Universes.resultLevel) :=
  .conv nil_identity_typed
    (.symm (pi_equal_upper AllComputation.Nil.upper_equal lower_nil_equal.weaken)) (.sort _)

namespace Motive

def context : Tower.Ctx 6 := .snoc lengthContext
  (NativeNaturalVectorFamilies.vecApp (.var 4) (.var 0))

def family (level : LevelExpr Nat) : Tower.Tm 6 :=
  NativeVectorAll.Universes.Canonical.allTypeAtUniverse level (.var 5) (.var 4) (.var 1) (.var 0)

def type : Tower.Tm 4 :=
  .pi NativeNaturalVectorFamilies.natTm
    (.pi (NativeNaturalVectorFamilies.vecApp (.var 4) (.var 0))
      (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel))

theorem lower_typed : Typed rules context (family NativeVectorAll.Universes.resultLevel)
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  refine Derivable.sub (A := sortTm NativeVectorAll.Universes.resultLevel) ?_
    (.subUniv (by intro valuation; exact Nat.le_max_left _ _))
  exact lower_all_at (context := context) (element := .var 5) (predicate := .var 4)
    (length := .var 1) (vector := .var 0) (.var 5) (.var 4) (.var 1) (.var 0)

theorem upper_typed : Typed rules context (family NativeVectorAll.Universes.CumulativeElimination.upperLevel)
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  upper_all_at (context := context) (element := .var 5) (predicate := .var 4)
    (length := .var 1) (vector := .var 0) (.var 5) (.var 4) (.var 1) (.var 0)

theorem vector_typed : Typed rules lengthContext
    (NativeNaturalVectorFamilies.vecApp (.var 4) (.var 0)) (sortTm NativeVectorAll.Universes.dataLevel) :=
  .appElim (.appElim (primitive_typed lengthContext 4) (.var 4)) (.var 0)

def innerLevel : LevelExpr Nat := .max NativeVectorAll.Universes.dataLevel
  (.succ NativeVectorAll.Universes.CumulativeElimination.upperLevel)

theorem inner_formed : Typed rules lengthContext
    (.pi (NativeNaturalVectorFamilies.vecApp (.var 4) (.var 0))
      (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel)) (sortTm innerLevel) :=
  .piForm vector_typed (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

theorem type_formed : Typed rules NativeVectorAll.Universes.context type
    (sortTm (.max NativeNaturalVectorFamilies.natLevel innerLevel)) :=
  .piForm (Congruence.NaturalControl.natural_typed _) (.sort _) inner_formed (.sort _) (.sorts _ _)

def body (source target : LevelExpr Nat) : Tower.Tm 6 :=
  NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.functionType source target
    (.var 5) (.var 4) (.var 1) (.var 0)

theorem body_typed (source target : LevelExpr Nat)
    (sourceTyped : Typed rules context (family source) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel))
    (targetTyped : Typed rules context (family target) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel)) :
    Typed rules context (body source target) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  pi_upper sourceTyped targetTyped.weaken

theorem typed (source target : LevelExpr Nat)
    (sourceTyped : Typed rules context (family source) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel))
    (targetTyped : Typed rules context (family target) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel)) :
    Typed rules NativeVectorAll.Universes.context
      (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive source target (.var 3) (.var 2)) type := by
  have innerForm : Typed rules lengthContext
      (.pi (NativeNaturalVectorFamilies.vecApp (.var 4) (.var 0))
        (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel))
      (sortTm (.max NativeVectorAll.Universes.dataLevel
      (.succ NativeVectorAll.Universes.CumulativeElimination.upperLevel))) := inner_formed
  refine Derivable.lamIntro
    (.piForm (Congruence.NaturalControl.natural_typed _) (.sort _) innerForm (.sort _) (.sorts _ _))
    (.sort _) ?_
  exact .lamIntro innerForm (.sort _) (pi_upper sourceTyped targetTyped.weaken)

theorem beta (source target : LevelExpr Nat)
    (sourceTyped : Typed rules context (family source) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel))
    (targetTyped : Typed rules context (family target) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel)) :
    Equal rules NativeVectorAll.Universes.context
      (.app (.app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
        source target (.var 3) (.var 2)) (.var 1)) (.var 0))
      (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.functionType
        source target (.var 3) (.var 2) (.var 1) (.var 0))
      (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  have equation := betaPi_two type_formed (.sort _) inner_formed (.sort _)
    (body_typed source target sourceTyped targetTyped)
    (first := .var 1) (second := .var 0) (.var 1) (.var 0)
  change Equal rules NativeVectorAll.Universes.context _
    (subst (consSub (.var 0) (consSub (.var 1) ids)) (body source target)) _ at equation
  unfold body at equation
  rw [NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.substitute_functionType] at equation
  exact equation

theorem forward_typed : Typed rules NativeVectorAll.Universes.context
    (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
      NativeVectorAll.Universes.resultLevel NativeVectorAll.Universes.CumulativeElimination.upperLevel
      (.var 3) (.var 2)) type :=
  typed _ _ lower_typed upper_typed

theorem backward_typed : Typed rules NativeVectorAll.Universes.context
    (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
      NativeVectorAll.Universes.CumulativeElimination.upperLevel NativeVectorAll.Universes.resultLevel
      (.var 3) (.var 2)) type :=
  typed _ _ upper_typed lower_typed

theorem forward_beta : Equal rules NativeVectorAll.Universes.context
    (.app (.app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
      NativeVectorAll.Universes.resultLevel NativeVectorAll.Universes.CumulativeElimination.upperLevel
      (.var 3) (.var 2)) (.var 1)) (.var 0))
    (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.forwardType)
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  beta _ _ lower_typed upper_typed

theorem backward_beta : Equal rules NativeVectorAll.Universes.context
    (.app (.app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
      NativeVectorAll.Universes.CumulativeElimination.upperLevel NativeVectorAll.Universes.resultLevel
      (.var 3) (.var 2)) (.var 1)) (.var 0))
    (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.backwardType)
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  beta _ _ upper_typed lower_typed

#print axioms forward_typed
#print axioms backward_typed
#print axioms forward_beta
#print axioms backward_beta

end Motive

#print axioms forward_method_typed
#print axioms backward_method_typed
#print axioms forward_constructor_method_typed
#print axioms backward_constructor_method_typed
#print axioms context_formed
#print axioms method_types_equal
#print axioms forward_nil_method_typed
#print axioms backward_nil_method_typed

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllMapMethods
