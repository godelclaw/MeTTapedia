import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllTypedMaps

/-!
# Local typed computation of the All evidence maps

The nil function equation is one original Vector iota root between independently
typed endpoints. Applying that function to supplied evidence then uses the
primitive typed beta equation. No unit eta or uniqueness of identity proofs
is used: the evidence itself is retained. Typed substitution supplies the
same nil application law at arbitrary typed element/predicate inputs and
supplied evidence. The cons law combines one original iota root with the
typed beta laws for the three fields and the two evidence-map arguments.
It retains the head and recursively maps the tail for arbitrary typed inputs
and supplied evidence, including an unknown tail and evidence variable.
The neutral-vector inverse is a separate obligation.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation TypedEquality

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllMapComputation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeVectorIdentityComparison
open NativeVectorAllTypedMaps

def nilCarrier (level : LevelExpr Nat) : Tower.Tm 4 :=
  NativeVectorAll.Universes.Canonical.allTypeAtUniverse level (.var 3) (.var 2)
    NativeNaturalVectorFamilies.zeroTm (NativeNaturalVectorFamilies.vnilApp (.var 3))

def nilMap (direction : Direction) : Tower.Tm 4 :=
  NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map (source direction) (target direction)
    (.var 3) (.var 2) NativeNaturalVectorFamilies.zeroTm (NativeNaturalVectorFamilies.vnilApp (.var 3))

theorem nil_map_typed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    (nilMap direction) (NativeVectorAllMapMethods.nilMethodType (source direction) (target direction)) :=
  map_typed_at direction AllComputation.Nil.element_typed AllComputation.Nil.predicate_typed
    (Congruence.NaturalControl.zero_typed _) AllComputation.Nil.nil_typed

theorem nil_identity_typed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    (.lam (.var 0)) (NativeVectorAllMapMethods.nilMethodType (source direction) (target direction)) := by
  cases direction
  · exact NativeVectorAllMapMethods.forward_nil_method_typed
  · exact NativeVectorAllMapMethods.backward_nil_method_typed

theorem nil_root (direction : Direction) : rules.computation.step (nilMap direction) (.lam (.var 0)) :=
  Declaration.RootStep.declared (Or.inl ⟨NativeNaturalVectorFamilies.IotaEvidence.vecNil _ _ _ _⟩)

theorem nil_function_equal (direction : Direction) : Equal rules NativeVectorAll.Universes.context
    (nilMap direction) (.lam (.var 0))
    (NativeVectorAllMapMethods.nilMethodType (source direction) (target direction)) :=
  .root (nil_root direction) (nil_map_typed direction) (nil_identity_typed direction)

theorem nil_source_formed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    (nilCarrier (source direction)) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  cases direction
  · exact .sub AllComputation.Nil.lower_typed (.subUniv (by intro valuation; exact Nat.le_max_left _ _))
  · exact AllComputation.Nil.upper_typed

theorem nil_target_formed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    (nilCarrier (target direction)) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  cases direction
  · exact AllComputation.Nil.upper_typed
  · exact .sub AllComputation.Nil.lower_typed (.subUniv (by intro valuation; exact Nat.le_max_left _ _))

theorem nil_function_type_formed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    (NativeVectorAllMapMethods.nilMethodType (source direction) (target direction))
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  NativeVectorAllMapMethods.pi_upper (nil_source_formed direction) (nil_target_formed direction).weaken

theorem nil_carriers_equal (direction : Direction) : Equal rules NativeVectorAll.Universes.context
    (nilCarrier (source direction)) (nilCarrier (target direction))
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  cases direction
  · exact AllComputation.Nil.annotations_equal
  · exact .symm AllComputation.Nil.annotations_equal

theorem nil_application_equal (direction : Direction) {evidence : Tower.Tm 4}
    (checked : Typed rules NativeVectorAll.Universes.context evidence (nilCarrier (source direction))) :
    Equal rules NativeVectorAll.Universes.context (.app (nilMap direction) evidence) evidence
      (nilCarrier (target direction)) := by
  have applied := Derivable.appCong (nil_function_equal direction) (Derivable.refl checked)
  have beta := betaPi_identity (nil_function_type_formed direction) (.sort _)
    (nil_carriers_equal direction) (.sort _) checked
  exact .trans (by simpa only [nilCarrier, NativeVectorAllMapMethods.nilMethodType,
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.functionType, inst0_rename_wk] using applied) beta

def nilEvidence : Tower.Tm 4 := .refl NativeNaturalVectorFamilies.zeroTm

theorem nil_evidence_typed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    nilEvidence (nilCarrier (source direction)) := by
  have unitTyped : Typed rules NativeVectorAll.Universes.context nilEvidence NativeVectorAll.unitType :=
    .reflIntro (Congruence.NaturalControl.zero_typed _)
  cases direction
  · exact .conv unitTyped (.symm AllComputation.Nil.lower_equal) (.sort _)
  · exact .conv unitTyped (.symm AllComputation.Nil.upper_equal) (.sort _)

theorem forward_nil_control : Equal rules NativeVectorAll.Universes.context
    (.app (nilMap .forward) nilEvidence) nilEvidence (nilCarrier (target .forward)) :=
  nil_application_equal .forward (nil_evidence_typed .forward)

theorem backward_nil_control : Equal rules NativeVectorAll.Universes.context
    (.app (nilMap .backward) nilEvidence) nilEvidence (nilCarrier (target .backward)) :=
  nil_application_equal .backward (nil_evidence_typed .backward)

def nilInputs {n : Nat} (element predicate : Tower.Tm n) : Sub Tower.Head 4 n :=
  NativeVectorAll.Universes.arguments element predicate NativeNaturalVectorFamilies.zeroTm
    (NativeNaturalVectorFamilies.vnilApp element)

theorem nil_inputs_typed {n : Nat} {context : Tower.Ctx n} {element predicate : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel))) :
    SubstMor rules NativeVectorAll.Universes.context context (nilInputs element predicate) :=
  all_inputs_typed elementTyped predicateTyped (Congruence.NaturalControl.zero_typed _)
    (.appElim (primitive_typed context 5) elementTyped)

theorem nil_carrier_readback {n : Nat} (level : LevelExpr Nat) (element predicate : Tower.Tm n) :
    subst (nilInputs element predicate) (nilCarrier level) =
      NativeVectorAll.Universes.Canonical.allTypeAtUniverse level element predicate
        NativeNaturalVectorFamilies.zeroTm (NativeNaturalVectorFamilies.vnilApp element) := by
  rw [nilCarrier, NativeVectorAll.Universes.Canonical.substitute_allTypeAtUniverse]
  rfl

theorem nil_type_readback {n : Nat} (direction : Direction) (element predicate : Tower.Tm n) :
    subst (nilInputs element predicate)
      (NativeVectorAllMapMethods.nilMethodType (source direction) (target direction)) =
      NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.functionType
        (source direction) (target direction) element predicate NativeNaturalVectorFamilies.zeroTm
          (NativeNaturalVectorFamilies.vnilApp element) := by
  rw [NativeVectorAllMapMethods.nilMethodType,
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.substitute_functionType]
  rfl

theorem nil_map_readback {n : Nat} (direction : Direction) (element predicate : Tower.Tm n) :
    subst (nilInputs element predicate) (nilMap direction) =
      NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map
        (source direction) (target direction) element predicate NativeNaturalVectorFamilies.zeroTm
          (NativeNaturalVectorFamilies.vnilApp element) := by
  rw [nilMap, NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.substitute_map]
  rfl

theorem nil_application_equal_at (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate evidence : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (checked : Typed rules context evidence
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate
        NativeNaturalVectorFamilies.zeroTm (NativeNaturalVectorFamilies.vnilApp element))) :
    Equal rules context
      (.app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map
        (source direction) (target direction) element predicate NativeNaturalVectorFamilies.zeroTm
          (NativeNaturalVectorFamilies.vnilApp element)) evidence)
      evidence
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (target direction) element predicate
        NativeNaturalVectorFamilies.zeroTm (NativeNaturalVectorFamilies.vnilApp element)) := by
  have assignment := nil_inputs_typed elementTyped predicateTyped
  have functionEqual := (nil_function_equal direction).substitute assignment
  rw [nil_map_readback, nil_type_readback] at functionEqual
  have identityReadback : subst (nilInputs element predicate) (.lam (.var 0)) =
      (.lam (.var 0) : Tower.Tm n) := rfl
  rw [identityReadback] at functionEqual
  have formed := (nil_function_type_formed direction).substitute assignment
  rw [nil_type_readback] at formed
  have carriers := (nil_carriers_equal direction).substitute assignment
  rw [nil_carrier_readback, nil_carrier_readback] at carriers
  have beta := betaPi_identity formed (.sort _) carriers (.sort _) checked
  have applied := Derivable.appCong functionEqual (Derivable.refl checked)
  exact .trans (by simpa only [NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.functionType,
    inst0_rename_wk] using applied) beta

theorem forward_nil_at_original : Equal rules NativeVectorAll.Universes.context
    (.app (nilMap .forward) nilEvidence) nilEvidence (nilCarrier (target .forward)) :=
  nil_application_equal_at .forward AllComputation.Nil.element_typed AllComputation.Nil.predicate_typed
    (nil_evidence_typed .forward)

def consRight {n : Nat} (direction : Direction)
    (element predicate number head tail : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.app NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.consCase number) head) tail)
    (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map
      (source direction) (target direction) element predicate number tail)

def consInputs {n : Nat} (element predicate number head tail : Tower.Tm n) : Sub Tower.Head 5 n :=
  consSub head (NativeVectorAll.Universes.arguments element predicate number tail)

theorem cons_inputs_typed {n : Nat} {context : Tower.Ctx n}
    {element predicate number head tail : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (headTyped : Typed rules context head element)
    (tailTyped : Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number)) :
    SubstMor rules AllComputation.Cons.context context (consInputs element predicate number head tail) := by
  apply SubstMor.cons (all_inputs_typed elementTyped predicateTyped numberTyped tailTyped) (.var 3)
  change Typed rules context head element
  exact headTyped

theorem cons_constructor_typed {n : Nat} {context : Tower.Ctx n}
    {element predicate number head tail : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (headTyped : Typed rules context head element)
    (tailTyped : Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number)) :
    Typed rules context (NativeNaturalVectorFamilies.vconsApp element number head tail)
      (NativeNaturalVectorFamilies.vecApp element (NativeNaturalVectorFamilies.succApp number)) := by
  have linked := AllComputation.Cons.constructor_typed.substitute
    (cons_inputs_typed elementTyped predicateTyped numberTyped headTyped tailTyped)
  have termReadback : subst (consInputs element predicate number head tail)
      (NativeNaturalVectorFamilies.vconsApp AllComputation.Cons.element AllComputation.Cons.number
        AllComputation.Cons.head AllComputation.Cons.tail) =
      NativeNaturalVectorFamilies.vconsApp element number head tail := rfl
  have typeReadback : subst (consInputs element predicate number head tail)
      (NativeNaturalVectorFamilies.vecApp AllComputation.Cons.element
        (NativeNaturalVectorFamilies.succApp AllComputation.Cons.number)) =
      NativeNaturalVectorFamilies.vecApp element (NativeNaturalVectorFamilies.succApp number) := rfl
  rw [termReadback, typeReadback] at linked
  exact linked

theorem cons_right_typed (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number head tail : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (headTyped : Typed rules context head element)
    (tailTyped : Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number)) :
    Typed rules context (consRight direction element predicate number head tail)
      (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.functionType
        (source direction) (target direction) element predicate (NativeNaturalVectorFamilies.succApp number)
        (NativeNaturalVectorFamilies.vconsApp element number head tail)) := by
  have recursive := map_typed_at direction elementTyped predicateTyped numberTyped tailTyped
  have recursiveMotive := Derivable.conv recursive
    (.symm (motive_beta_at direction elementTyped predicateTyped numberTyped tailTyped)) (.sort _)
  have applied := cons_method_apply (cons_method_at direction elementTyped predicateTyped numberTyped tailTyped)
    numberTyped headTyped tailTyped recursiveMotive
  have nextTyped := Derivable.appElim (primitive_typed context 2) numberTyped
  have constructorTyped := cons_constructor_typed elementTyped predicateTyped numberTyped headTyped tailTyped
  exact .conv applied (motive_beta_at direction elementTyped predicateTyped nextTyped constructorTyped) (.sort _)

theorem cons_function_equal_at (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number head tail : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (headTyped : Typed rules context head element)
    (tailTyped : Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number)) :
    Equal rules context
      (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map
        (source direction) (target direction) element predicate (NativeNaturalVectorFamilies.succApp number)
        (NativeNaturalVectorFamilies.vconsApp element number head tail))
      (consRight direction element predicate number head tail)
      (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.functionType
        (source direction) (target direction) element predicate (NativeNaturalVectorFamilies.succApp number)
        (NativeNaturalVectorFamilies.vconsApp element number head tail)) := by
  have nextTyped := Derivable.appElim (primitive_typed context 2) numberTyped
  have constructorTyped := cons_constructor_typed elementTyped predicateTyped numberTyped headTyped tailTyped
  have before := map_typed_at direction elementTyped predicateTyped nextTyped constructorTyped
  have after := cons_right_typed direction elementTyped predicateTyped numberTyped headTyped tailTyped
  exact .root (Declaration.RootStep.declared
    (Or.inl ⟨NativeNaturalVectorFamilies.IotaEvidence.vecCons _ _ _ _ _ _ _⟩)) before after

theorem source_all_formed (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number vector : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (vectorTyped : Typed rules context vector (NativeNaturalVectorFamilies.vecApp element number)) :
    Typed rules context (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction)
      element predicate number vector) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  cases direction
  · exact .sub (lower_all_at elementTyped predicateTyped numberTyped vectorTyped)
      (.subUniv (by intro valuation; exact Nat.le_max_left _ _))
  · exact upper_all_at elementTyped predicateTyped numberTyped vectorTyped

theorem target_all_formed (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number vector : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (vectorTyped : Typed rules context vector (NativeNaturalVectorFamilies.vecApp element number)) :
    Typed rules context (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (target direction)
      element predicate number vector) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  cases direction
  · exact upper_all_at elementTyped predicateTyped numberTyped vectorTyped
  · exact .sub (lower_all_at elementTyped predicateTyped numberTyped vectorTyped)
      (.subUniv (by intro valuation; exact Nat.le_max_left _ _))

def expandedPrefixType {n : Nat} (direction : Direction)
    (element predicate number head tail : Tower.Tm n) : Tower.Tm n :=
  PairSecondMap.typeAt (.app predicate head)
    (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate number tail)
    (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (target direction) element predicate number tail)

theorem cons_prefix_beta_at (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number head tail : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (headTyped : Typed rules context head element)
    (tailTyped : Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number)) :
    Equal rules context
      (.app (.app (.app NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.consCase number) head) tail)
      PairSecondMap.subject (expandedPrefixType direction element predicate number head tail) := by
  have sourceTail := source_all_formed direction (context := NativeVectorAllMapMethods.context)
    (element := .var 6) (predicate := .var 5) (number := .var 2) (vector := .var 0)
    (.var 6) (.var 5) (.var 2) (.var 0)
  have targetTail := target_all_formed direction (context := NativeVectorAllMapMethods.context)
    (element := .var 6) (predicate := .var 5) (number := .var 2) (vector := .var 0)
    (.var 6) (.var 5) (.var 2) (.var 0)
  have inner := NativeVectorAllMapMethods.inner_type_typed _ _ sourceTail targetTail
  have thirdFormed := NativeVectorAllMapMethods.pi_upper NativeVectorAllMapMethods.vector_domain_typed inner
  have secondFormed := NativeVectorAllMapMethods.pi_upper NativeVectorAllMapMethods.head_domain_typed thirdFormed
  let sigma := NativeVectorAll.Universes.arguments element predicate number tail
  have firstAt : Typed rules context number (subst sigma NativeNaturalVectorFamilies.natTm) := numberTyped
  have secondAt : Typed rules context head (subst (consSub number sigma) (.var 4 : Tower.Tm 5)) := by
    change Typed rules context head element
    exact headTyped
  have thirdAt : Typed rules context tail
      (subst (consSub head (consSub number sigma)) (NativeNaturalVectorFamilies.vecApp (.var 5) (.var 1) : Tower.Tm 6)) := by
    change Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number)
    exact tailTyped
  have equation := betaPi_three_substitute
    (NativeVectorAllMapMethods.method_type_typed _ _ sourceTail targetTail) (.sort _)
    secondFormed (.sort _) thirdFormed (.sort _)
    (NativeVectorAllMapMethods.inner_typed _ _ sourceTail targetTail)
    (all_inputs_typed elementTyped predicateTyped numberTyped tailTyped) firstAt secondAt thirdAt
  have programReadback : subst sigma (.lam (.lam (.lam (PairSecondMap.subject : Tower.Tm 7)))) =
      (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.consCase : Tower.Tm n) := rfl
  have typeReadback : subst (consSub tail (consSub head (consSub number sigma)))
      (NativeVectorAllMapMethods.innerType (source direction) (target direction)) =
      expandedPrefixType direction element predicate number head tail := by
    rw [NativeVectorAllMapMethods.innerType, PairSecondMap.substitute_typeAt]
    simp only [NativeVectorAllMapMethods.tailType, NativeVectorAll.Universes.Canonical.substitute_allTypeAtUniverse]
    rfl
  change Equal rules context
    (.app (.app (.app (subst sigma (.lam (.lam (.lam (PairSecondMap.subject : Tower.Tm 7))))) number) head) tail)
    (subst (consSub tail (consSub head (consSub number sigma))) PairSecondMap.subject)
    (subst (consSub tail (consSub head (consSub number sigma)))
      (NativeVectorAllMapMethods.innerType (source direction) (target direction))) at equation
  rw [programReadback, typeReadback, PairSecondMap.substitute_subject] at equation
  exact equation

def consCarrier {n : Nat} (level : LevelExpr Nat)
    (element predicate number head tail : Tower.Tm n) : Tower.Tm n :=
  NativeVectorAll.Universes.Canonical.allTypeAtUniverse level element predicate
    (NativeNaturalVectorFamilies.succApp number) (NativeNaturalVectorFamilies.vconsApp element number head tail)

def consPair {n : Nat} (level : LevelExpr Nat)
    (element predicate number head tail : Tower.Tm n) : Tower.Tm n :=
  .sigma (.app predicate head)
    (rename wk (NativeVectorAll.Universes.Canonical.allTypeAtUniverse level element predicate number tail))

theorem rename_consCarrier {n m : Nat} (rho : Ren n m) (level : LevelExpr Nat)
    (element predicate number head tail : Tower.Tm n) :
    rename rho (consCarrier level element predicate number head tail) =
      consCarrier level (rename rho element) (rename rho predicate) (rename rho number) (rename rho head) (rename rho tail) := by
  have constructorRename : rename rho (NativeNaturalVectorFamilies.vconsApp element number head tail) =
      NativeNaturalVectorFamilies.vconsApp (rename rho element) (rename rho number) (rename rho head) (rename rho tail) := rfl
  have mapped := NativeVectorAll.Universes.Canonical.substitute_allTypeAtUniverse (renSub rho) level
    element predicate (NativeNaturalVectorFamilies.succApp number)
    (NativeNaturalVectorFamilies.vconsApp element number head tail)
  simpa only [consCarrier, subst_renSub, NativeNaturalVectorFamilies.rename_succApp, constructorRename] using mapped

theorem cons_carrier_readback {n : Nat} (level : LevelExpr Nat)
    (element predicate number head tail : Tower.Tm n) :
    subst (consInputs element predicate number head tail)
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse level AllComputation.Cons.element AllComputation.Cons.predicate
        (NativeNaturalVectorFamilies.succApp AllComputation.Cons.number)
        (NativeNaturalVectorFamilies.vconsApp AllComputation.Cons.element AllComputation.Cons.number
          AllComputation.Cons.head AllComputation.Cons.tail)) =
      consCarrier level element predicate number head tail := by
  rw [NativeVectorAll.Universes.Canonical.substitute_allTypeAtUniverse]
  rfl

theorem cons_pair_readback {n : Nat} (level : LevelExpr Nat)
    (element predicate number head tail : Tower.Tm n) :
    subst (consInputs element predicate number head tail) (AllComputation.Cons.result level) =
      consPair level element predicate number head tail := by
  simp only [AllComputation.Cons.result, AllComputation.Cons.tailType, subst, subst_liftSub_wk,
    NativeVectorAll.Universes.Canonical.substitute_allTypeAtUniverse]
  rfl

theorem cons_source_equal_at (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number head tail : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (headTyped : Typed rules context head element)
    (tailTyped : Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number)) :
    Equal rules context (consCarrier (source direction) element predicate number head tail)
      (consPair (source direction) element predicate number head tail)
      (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  have original : Equal rules AllComputation.Cons.context
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction)
        AllComputation.Cons.element AllComputation.Cons.predicate
        (NativeNaturalVectorFamilies.succApp AllComputation.Cons.number)
        (NativeNaturalVectorFamilies.vconsApp AllComputation.Cons.element AllComputation.Cons.number
          AllComputation.Cons.head AllComputation.Cons.tail)) (AllComputation.Cons.result (source direction))
      (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
    cases direction
    · exact .subEq AllComputation.Cons.lower_equal (.subUniv (by intro valuation; exact Nat.le_max_left _ _))
    · exact AllComputation.Cons.upper_equal
  have linked := original.substitute (cons_inputs_typed elementTyped predicateTyped numberTyped headTyped tailTyped)
  rw [cons_carrier_readback, cons_pair_readback] at linked
  exact linked

theorem cons_target_equal_at (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number head tail : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (headTyped : Typed rules context head element)
    (tailTyped : Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number)) :
    Equal rules context (consCarrier (target direction) element predicate number head tail)
      (consPair (target direction) element predicate number head tail)
      (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  have original : Equal rules AllComputation.Cons.context
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (target direction)
        AllComputation.Cons.element AllComputation.Cons.predicate
        (NativeNaturalVectorFamilies.succApp AllComputation.Cons.number)
        (NativeNaturalVectorFamilies.vconsApp AllComputation.Cons.element AllComputation.Cons.number
          AllComputation.Cons.head AllComputation.Cons.tail)) (AllComputation.Cons.result (target direction))
      (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
    cases direction
    · exact AllComputation.Cons.upper_equal
    · exact .subEq AllComputation.Cons.lower_equal (.subUniv (by intro valuation; exact Nat.le_max_left _ _))
  have linked := original.substitute (cons_inputs_typed elementTyped predicateTyped numberTyped headTyped tailTyped)
  rw [cons_carrier_readback, cons_pair_readback] at linked
  exact linked

theorem cons_application_equal_at (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number head tail evidence : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (headTyped : Typed rules context head element)
    (tailTyped : Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number))
    (evidenceTyped : Typed rules context evidence (consCarrier (source direction) element predicate number head tail)) :
    Equal rules context
      (.app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map
        (source direction) (target direction) element predicate (NativeNaturalVectorFamilies.succApp number)
        (NativeNaturalVectorFamilies.vconsApp element number head tail)) evidence)
      (.pair (.fst evidence) (.app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map
        (source direction) (target direction) element predicate number tail) (.snd evidence)))
      (consCarrier (target direction) element predicate number head tail) := by
  have sourceEqual := cons_source_equal_at direction elementTyped predicateTyped numberTyped headTyped tailTyped
  have targetEqual := cons_target_equal_at direction elementTyped predicateTyped numberTyped headTyped tailTyped
  have evidencePair := Derivable.conv evidenceTyped sourceEqual (.sort _)
  have recursive := map_typed_at direction elementTyped predicateTyped numberTyped tailTyped
  have prefixEquality := cons_prefix_beta_at direction elementTyped predicateTyped numberTyped headTyped tailTyped
  unfold expandedPrefixType at prefixEquality
  rw [PairSecondMap.typeAt_expanded] at prefixEquality
  have applyRecursive := Derivable.appCong prefixEquality (Derivable.refl recursive)
  rw [inst0_rename_wk] at applyRecursive
  have applyEvidence := Derivable.appCong applyRecursive (Derivable.refl evidencePair)
  rw [inst0_rename_wk] at applyEvidence
  have predicateHead : Typed rules context (.app predicate head)
      (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
    .sub (.appElim predicateTyped headTyped)
      (.subUniv (by intro valuation; exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)))
  have beta := PairSecondMap.beta_at signature predicateHead
    (source_all_formed direction elementTyped predicateTyped numberTyped tailTyped)
    (target_all_formed direction elementTyped predicateTyped numberTyped tailTyped) recursive evidencePair
  have pairEqual := Derivable.trans applyEvidence beta
  have typedPairEqual := Derivable.convEq pairEqual (.symm targetEqual) (.sort _)
  have iota := Derivable.appCong
    (cons_function_equal_at direction elementTyped predicateTyped numberTyped headTyped tailTyped) (Derivable.refl evidenceTyped)
  rw [inst0_rename_wk] at iota
  exact .trans iota typedPairEqual

def consEvidenceContext (direction : Direction) : Tower.Ctx 6 :=
  .snoc AllComputation.Cons.context (consCarrier (source direction) AllComputation.Cons.element AllComputation.Cons.predicate
    AllComputation.Cons.number AllComputation.Cons.head AllComputation.Cons.tail)

theorem cons_evidence_context_formed (direction : Direction) : Normalization.CtxFormed rules (consEvidenceContext direction) :=
  .snoc (.snoc all_context_formed ⟨_, .sort NativeVectorAll.Universes.dataLevel, .var 3⟩)
    ⟨_, .sort _, source_all_formed direction AllComputation.Cons.element_typed AllComputation.Cons.predicate_typed
      AllComputation.Cons.successor_typed AllComputation.Cons.constructor_typed⟩

theorem cons_evidence_variable_typed (direction : Direction) : Typed rules (consEvidenceContext direction) (.var 0)
    (consCarrier (source direction) (.var 5) (.var 4) (.var 3) (.var 1) (.var 2)) := by
  have checked := Derivable.var (R := rules) (Γ := consEvidenceContext direction) 0
  change Typed rules (consEvidenceContext direction) (.var 0)
    (rename wk (consCarrier (source direction) AllComputation.Cons.element AllComputation.Cons.predicate
      AllComputation.Cons.number AllComputation.Cons.head AllComputation.Cons.tail)) at checked
  rw [rename_consCarrier] at checked
  exact checked

theorem unknown_cons_control (direction : Direction) : Equal rules (consEvidenceContext direction)
    (.app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map (source direction) (target direction)
      (.var 5) (.var 4) (NativeNaturalVectorFamilies.succApp (.var 3))
      (NativeNaturalVectorFamilies.vconsApp (.var 5) (.var 3) (.var 1) (.var 2))) (.var 0))
    (.pair (.fst (.var 0)) (.app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map
      (source direction) (target direction) (.var 5) (.var 4) (.var 3) (.var 2)) (.snd (.var 0))))
    (consCarrier (target direction) (.var 5) (.var 4) (.var 3) (.var 1) (.var 2)) :=
  cons_application_equal_at direction (context := consEvidenceContext direction)
    (element := .var 5) (predicate := .var 4) (number := .var 3) (head := .var 1) (tail := .var 2)
    (.var 5) (.var 4) (.var 3) (.var 1) (.var 2) (cons_evidence_variable_typed direction)

theorem forward_unknown_cons_control : Equal rules (consEvidenceContext .forward)
    (.app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map (source .forward) (target .forward)
      (.var 5) (.var 4) (NativeNaturalVectorFamilies.succApp (.var 3))
      (NativeNaturalVectorFamilies.vconsApp (.var 5) (.var 3) (.var 1) (.var 2))) (.var 0))
    (.pair (.fst (.var 0)) (.app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map
      (source .forward) (target .forward) (.var 5) (.var 4) (.var 3) (.var 2)) (.snd (.var 0))))
    (consCarrier (target .forward) (.var 5) (.var 4) (.var 3) (.var 1) (.var 2)) :=
  cons_application_equal_at .forward (context := consEvidenceContext .forward)
    (element := .var 5) (predicate := .var 4) (number := .var 3) (head := .var 1) (tail := .var 2)
    (.var 5) (.var 4) (.var 3) (.var 1) (.var 2) (cons_evidence_variable_typed .forward)

theorem forward_cons_function_control : Equal rules AllComputation.Cons.context
    (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map
      (source .forward) (target .forward) AllComputation.Cons.element AllComputation.Cons.predicate
      (NativeNaturalVectorFamilies.succApp AllComputation.Cons.number)
      (NativeNaturalVectorFamilies.vconsApp AllComputation.Cons.element AllComputation.Cons.number
        AllComputation.Cons.head AllComputation.Cons.tail))
    (consRight .forward AllComputation.Cons.element AllComputation.Cons.predicate
      AllComputation.Cons.number AllComputation.Cons.head AllComputation.Cons.tail)
    (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.functionType
      (source .forward) (target .forward) AllComputation.Cons.element AllComputation.Cons.predicate
      (NativeNaturalVectorFamilies.succApp AllComputation.Cons.number)
      (NativeNaturalVectorFamilies.vconsApp AllComputation.Cons.element AllComputation.Cons.number
        AllComputation.Cons.head AllComputation.Cons.tail)) :=
  cons_function_equal_at .forward AllComputation.Cons.element_typed AllComputation.Cons.predicate_typed
    AllComputation.Cons.number_typed AllComputation.Cons.head_typed AllComputation.Cons.tail_typed

#print axioms nil_application_equal
#print axioms forward_nil_control
#print axioms backward_nil_control
#print axioms nil_application_equal_at
#print axioms cons_function_equal_at
#print axioms forward_cons_function_control
#print axioms cons_prefix_beta_at
#print axioms cons_application_equal_at
#print axioms unknown_cons_control
#print axioms forward_unknown_cons_control

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllMapComputation
