import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllMapMethods

/-!
# Typed applications of the native All universe maps

Both universe directions use the original motives and methods in the same
joined Vector/identity signature. Typed beta equations expose the interfaces
of the applied motives. The original complete maps are typed at arbitrary
typed inputs, including neutral vectors, and transport inhabitation in both
directions. The native motive uses its explicit cumulative successor bound;
the two universe heads remain distinct. No normalization assumption about
that signature is used. Computation laws and inverse laws have separate
proof obligations.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation TypedEquality

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllTypedMaps
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeVectorIdentityComparison

inductive Direction where
  | forward
  | backward

def source : Direction → LevelExpr Nat
  | .forward => NativeVectorAll.Universes.resultLevel
  | .backward => NativeVectorAll.Universes.CumulativeElimination.upperLevel

def target : Direction → LevelExpr Nat
  | .forward => NativeVectorAll.Universes.CumulativeElimination.upperLevel
  | .backward => NativeVectorAll.Universes.resultLevel

theorem source_formed (direction : Direction) : Typed rules NativeVectorAllMapMethods.Motive.context
    (NativeVectorAllMapMethods.Motive.family (source direction))
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  cases direction
  · exact NativeVectorAllMapMethods.Motive.lower_typed
  · exact NativeVectorAllMapMethods.Motive.upper_typed

theorem target_formed (direction : Direction) : Typed rules NativeVectorAllMapMethods.Motive.context
    (NativeVectorAllMapMethods.Motive.family (target direction))
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  cases direction
  · exact NativeVectorAllMapMethods.Motive.upper_typed
  · exact NativeVectorAllMapMethods.Motive.lower_typed

theorem motive_typed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
      (source direction) (target direction) (.var 3) (.var 2)) NativeVectorAllMapMethods.Motive.type :=
  NativeVectorAllMapMethods.Motive.typed _ _ (source_formed direction) (target_formed direction)

theorem motive_beta (direction : Direction) : Equal rules NativeVectorAll.Universes.context
    (.app (.app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
      (source direction) (target direction) (.var 3) (.var 2)) (.var 1)) (.var 0))
    (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.functionType
      (source direction) (target direction) (.var 3) (.var 2) (.var 1) (.var 0))
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  NativeVectorAllMapMethods.Motive.beta _ _ (source_formed direction) (target_formed direction)

theorem motive_beta_at (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number vector : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (vectorTyped : Typed rules context vector (NativeNaturalVectorFamilies.vecApp element number)) :
    Equal rules context
      (.app (.app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
        (source direction) (target direction) element predicate) number) vector)
      (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.functionType
        (source direction) (target direction) element predicate number vector)
      (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  have linked := (motive_beta direction).substitute
    (all_inputs_typed elementTyped predicateTyped numberTyped vectorTyped)
  have atThree : NativeVectorAll.Universes.arguments element predicate number vector 3 = element := by
    change consSub vector (consSub number (consSub predicate (consSub element Fin.elim0)))
      (Fin.succ (Fin.succ (Fin.succ 0))) = element
    simp only [consSub_succ, consSub_zero]
  have atTwo : NativeVectorAll.Universes.arguments element predicate number vector 2 = predicate := by
    change consSub vector (consSub number (consSub predicate (consSub element Fin.elim0)))
      (Fin.succ (Fin.succ 0)) = predicate
    simp only [consSub_succ, consSub_zero]
  have atOne : NativeVectorAll.Universes.arguments element predicate number vector 1 = number := by
    change consSub vector (consSub number (consSub predicate (consSub element Fin.elim0))) (Fin.succ 0) = number
    simp only [consSub_succ, consSub_zero]
  have atZero : NativeVectorAll.Universes.arguments element predicate number vector 0 = vector :=
    consSub_zero _ _
  simpa only [NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.substitute_motive,
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.substitute_functionType,
    subst, sortTm, atThree, atTwo, atOne, atZero] using linked

def nilInterface (direction : Direction) : Tower.Tm 4 :=
  .app (.app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
    (source direction) (target direction) (.var 3) (.var 2)) NativeNaturalVectorFamilies.zeroTm)
    (NativeNaturalVectorFamilies.vnilApp (.var 3))

theorem nil_interface_equal (direction : Direction) : Equal rules NativeVectorAll.Universes.context
    (nilInterface direction) (NativeVectorAllMapMethods.nilMethodType (source direction) (target direction))
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  motive_beta_at direction AllComputation.Nil.element_typed AllComputation.Nil.predicate_typed
    (Congruence.NaturalControl.zero_typed _) AllComputation.Nil.nil_typed

theorem nil_method_typed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    (.lam (.var 0)) (nilInterface direction) := by
  have checked : Typed rules NativeVectorAll.Universes.context (.lam (.var 0))
      (NativeVectorAllMapMethods.nilMethodType (source direction) (target direction)) := by
    cases direction
    · exact NativeVectorAllMapMethods.forward_nil_method_typed
    · exact NativeVectorAllMapMethods.backward_nil_method_typed
  exact .conv checked (.symm (nil_interface_equal direction)) (.sort _)

def tailApplication (direction : Direction) : Tower.Tm 7 :=
  .app (.app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
    (source direction) (target direction) (.var 6) (.var 5)) (.var 2)) (.var 0)

def constructorApplication (direction : Direction) : Tower.Tm 7 :=
  .app (.app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
    (source direction) (target direction) (.var 6) (.var 5))
    (NativeNaturalVectorFamilies.succApp (.var 2)))
    (NativeNaturalVectorFamilies.vconsApp (.var 6) (.var 2) (.var 1) (.var 0))

def consInterface (direction : Direction) : Tower.Tm 4 :=
  .pi NativeNaturalVectorFamilies.natTm (.pi (.var 4)
    (.pi (NativeNaturalVectorFamilies.vecApp (.var 5) (.var 1))
      (.pi (tailApplication direction) (rename wk (constructorApplication direction)))))

def tailFunction (direction : Direction) : Tower.Tm 7 :=
  NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.functionType
    (source direction) (target direction) (.var 6) (.var 5) (.var 2) (.var 0)

def constructorFunction (direction : Direction) : Tower.Tm 7 :=
  NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.functionType
    (source direction) (target direction) (.var 6) (.var 5)
    (NativeNaturalVectorFamilies.succApp (.var 2))
    (NativeNaturalVectorFamilies.vconsApp (.var 6) (.var 2) (.var 1) (.var 0))

theorem constructor_interface_readback (direction : Direction) :
    NativeVectorAllMapMethods.constructorMethodType (source direction) (target direction) =
      .pi NativeNaturalVectorFamilies.natTm (.pi (.var 4)
        (.pi (NativeNaturalVectorFamilies.vecApp (.var 5) (.var 1))
          (.pi (tailFunction direction) (rename wk (constructorFunction direction))))) := rfl

theorem tail_beta (direction : Direction) : Equal rules NativeVectorAllMapMethods.context
    (tailApplication direction) (tailFunction direction)
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  motive_beta_at direction (element := .var 6) (predicate := .var 5)
    (number := .var 2) (vector := .var 0) (.var 6) (.var 5) (.var 2) (.var 0)

theorem successor_typed : Typed rules NativeVectorAllMapMethods.context
    (NativeNaturalVectorFamilies.succApp (.var 2)) NativeNaturalVectorFamilies.natTm :=
  .appElim (primitive_typed NativeVectorAllMapMethods.context 2) (.var 2)

theorem constructor_typed : Typed rules NativeVectorAllMapMethods.context
    (NativeNaturalVectorFamilies.vconsApp (.var 6) (.var 2) (.var 1) (.var 0))
    (NativeNaturalVectorFamilies.vecApp (.var 6) (NativeNaturalVectorFamilies.succApp (.var 2))) :=
  .appElim (.appElim (.appElim (.appElim (primitive_typed NativeVectorAllMapMethods.context 6)
    (.var 6)) (.var 2)) (.var 1)) (.var 0)

theorem constructor_beta (direction : Direction) : Equal rules NativeVectorAllMapMethods.context
    (constructorApplication direction) (constructorFunction direction)
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  motive_beta_at direction (element := .var 6) (predicate := .var 5)
    (.var 6) (.var 5) successor_typed constructor_typed

theorem cons_interface_equal (direction : Direction) : Equal rules NativeVectorAll.Universes.context
    (consInterface direction) (NativeVectorAllMapMethods.constructorMethodType (source direction) (target direction))
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  rw [constructor_interface_readback]
  exact NativeVectorAllMapMethods.pi_equal_upper (.refl NativeVectorAllMapMethods.length_domain_typed)
    (NativeVectorAllMapMethods.pi_equal_upper (.refl NativeVectorAllMapMethods.head_domain_typed)
      (NativeVectorAllMapMethods.pi_equal_upper (.refl NativeVectorAllMapMethods.vector_domain_typed)
        (NativeVectorAllMapMethods.pi_equal_upper (tail_beta direction) (constructor_beta direction).weaken)))

theorem cons_method_typed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.consCase (consInterface direction) := by
  have checked : Typed rules NativeVectorAll.Universes.context
      NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.consCase
      (NativeVectorAllMapMethods.constructorMethodType (source direction) (target direction)) := by
    cases direction
    · exact NativeVectorAllMapMethods.forward_constructor_method_typed
    · exact NativeVectorAllMapMethods.backward_constructor_method_typed
  exact .conv checked (.symm (cons_interface_equal direction)) (.sort _)

def resultInterface (direction : Direction) : Tower.Tm 4 :=
  .pi NativeNaturalVectorFamilies.natTm
    (.pi (NativeNaturalVectorFamilies.vecApp (.var 4) (.var 0))
      (.app (.app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
        (source direction) (target direction) (.var 5) (.var 4)) (.var 1)) (.var 0)))

def afterMotiveType (direction : Direction) : Tower.Tm 4 :=
  .pi (nilInterface direction)
    (rename wk (.pi (consInterface direction) (rename wk (resultInterface direction))))

def motiveTypeAt {n : Nat} (element : Tower.Tm n) : Tower.Tm n :=
  .pi NativeNaturalVectorFamilies.natTm
    (.pi (NativeNaturalVectorFamilies.vecApp (rename wk element) (.var 0))
      (sortTm (.succ NativeVectorAll.Universes.CumulativeElimination.upperLevel)))

def nativeMotiveLevel : LevelExpr Nat := .max NativeNaturalVectorFamilies.natLevel
  (.max NativeVectorAll.Universes.dataLevel
    (.succ (.succ NativeVectorAll.Universes.CumulativeElimination.upperLevel)))

theorem motive_type_formed {n : Nat} {context : Tower.Ctx n} {element : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel)) :
    Typed rules context (motiveTypeAt element) (sortTm nativeMotiveLevel) := by
  refine Derivable.piForm (Congruence.NaturalControl.natural_typed _) (.sort _) ?_ (.sort _) (.sorts _ _)
  refine Derivable.piForm ?_ (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)
  exact .appElim (.appElim (primitive_typed _ 4) elementTyped.weaken) (.var 0)

def nilTypeAt {n : Nat} (element motive : Tower.Tm n) : Tower.Tm n :=
  .app (.app motive NativeNaturalVectorFamilies.zeroTm) (NativeNaturalVectorFamilies.vnilApp element)

def consTypeAt {n : Nat} (element motive : Tower.Tm n) : Tower.Tm n :=
  .pi NativeNaturalVectorFamilies.natTm (.pi (rename wk element)
    (.pi (NativeNaturalVectorFamilies.vecApp (rename wk (rename wk element)) (.var (Fin.succ 0)))
      (.pi (.app (.app (rename wk (rename wk (rename wk motive))) (.var (Fin.succ (Fin.succ 0)))) (.var 0))
        (.app (.app (rename wk (rename wk (rename wk (rename wk motive))))
          (NativeNaturalVectorFamilies.succApp (.var (Fin.succ (Fin.succ (Fin.succ 0))))))
          (NativeNaturalVectorFamilies.vconsApp (rename wk (rename wk (rename wk (rename wk element))))
            (.var (Fin.succ (Fin.succ (Fin.succ 0)))) (.var (Fin.succ (Fin.succ 0))) (.var (Fin.succ 0)))))))

def resultTypeAt {n : Nat} (element motive : Tower.Tm n) : Tower.Tm n :=
  .pi NativeNaturalVectorFamilies.natTm
    (.pi (NativeNaturalVectorFamilies.vecApp (rename wk element) (.var 0))
      (.app (.app (rename wk (rename wk motive)) (.var (Fin.succ 0))) (.var 0)))

def afterMotiveTypeAt {n : Nat} (element motive : Tower.Tm n) : Tower.Tm n :=
  .pi (nilTypeAt element motive)
    (rename wk (.pi (consTypeAt element motive) (rename wk (resultTypeAt element motive))))

theorem result_apply {n : Nat} {context : Tower.Ctx n} {element motive function number vector : Tower.Tm n}
    (functionTyped : Typed rules context function (resultTypeAt element motive))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (vectorTyped : Typed rules context vector (NativeNaturalVectorFamilies.vecApp element number)) :
    Typed rules context (.app (.app function number) vector) (.app (.app motive number) vector) := by
  have openingWeakening {k : Nat} (value body : Tower.Tm k) :
      subst (subst0 value) (rename wk body) = body := inst0_rename_wk value body
  have atNumber := Derivable.appElim functionTyped numberTyped
  simp only [inst0, subst, openingWeakening, subst_liftSub_wk,
    liftSub_zero, liftSub_succ, subst0_zero, NativeNaturalVectorFamilies.subst_vecApp] at atNumber
  have atVector := Derivable.appElim atNumber vectorTyped
  simpa only [inst0, subst, openingWeakening, subst0_zero] using atVector

def eliminatorType : Tower.Tm 0 :=
  .pi (sortTm NativeVectorAll.Universes.dataLevel)
    (.pi (motiveTypeAt (.var 0))
      (.pi (nilTypeAt (.var 1) (.var 0))
        (.pi (consTypeAt (.var 2) (.var 1)) (resultTypeAt (.var 3) (.var 2)))))

theorem eliminator_type_readback : NativeVectorAll.Universes.ParameterInterpretation.types 7 = eliminatorType := rfl

theorem eliminator_name_readback : NativeVectorAll.Universes.ParameterInterpretation.names 7 =
    NativeNaturalVectorFamilies.vecEliminateName := by decide +kernel

def parameterContext : Tower.Ctx 2 :=
  .snoc (.snoc .nil (sortTm NativeVectorAll.Universes.dataLevel)) (motiveTypeAt (.var 0))

theorem parameter_context_formed : Normalization.CtxFormed rules parameterContext :=
  .snoc (.snoc .nil ⟨_, .sort _, .headType (.sort NativeVectorAll.Universes.dataLevel)⟩)
    ⟨_, .sort _, motive_type_formed (element := .var 0) (.var 0)⟩

def eliminatorBody : Tower.Tm 2 :=
  .pi (nilTypeAt (.var 1) (.var 0))
    (.pi (consTypeAt (.var 2) (.var 1)) (resultTypeAt (.var 3) (.var 2)))

def parameterResult : Tower.Tm 2 :=
  inst0 (.var 0) (subst (liftSub (subst0 (.var 1 : Tower.Tm 2)))
    (rename (liftRen (liftRen Fin.elim0)) eliminatorBody))

theorem parameter_result_readback : parameterResult = afterMotiveTypeAt (.var 1) (.var 0) := by
  decide +kernel

theorem parameter_application_typed : Typed rules parameterContext
    (.app (.app (.const NativeNaturalVectorFamilies.vecEliminateName) (.var 1)) (.var 0))
    (afterMotiveTypeAt (.var 1) (.var 0)) := by
  have operation : Typed rules parameterContext (.const NativeNaturalVectorFamilies.vecEliminateName)
      (liftClosed eliminatorType) := by
    simpa only [eliminator_type_readback, eliminator_name_readback] using primitive_typed parameterContext 7
  rw [← parameter_result_readback]
  exact .appElim (.appElim operation (.var 1)) (.var 0)

theorem substitute_afterMotiveTypeAt {n m : Nat} (sigma : Sub Tower.Head n m)
    (element motive : Tower.Tm n) :
    subst sigma (afterMotiveTypeAt element motive) = afterMotiveTypeAt (subst sigma element) (subst sigma motive) := by
  have variableRename {a b : Nat} (rho : Ren a b) (index : Fin a) :
      rename rho (.var index : Tower.Tm a) = .var (rho index) := rfl
  simp only [afterMotiveTypeAt, nilTypeAt, consTypeAt, resultTypeAt,
    NativeNaturalVectorFamilies.natTm, NativeNaturalVectorFamilies.vecApp,
    NativeNaturalVectorFamilies.vnilApp, NativeNaturalVectorFamilies.vconsApp,
    NativeNaturalVectorFamilies.zeroTm, NativeNaturalVectorFamilies.succApp,
    subst, subst_liftSub_wk, liftSub_zero, liftSub_succ]
  all_goals simp only [variableRename, wk]

theorem substitute_consTypeAt {n m : Nat} (sigma : Sub Tower.Head n m)
    (element motive : Tower.Tm n) :
    subst sigma (consTypeAt element motive) = consTypeAt (subst sigma element) (subst sigma motive) := by
  have combined := substitute_afterMotiveTypeAt sigma element motive
  change Tm.pi _ (subst (liftSub sigma)
      (rename wk (.pi (consTypeAt element motive) (rename wk (resultTypeAt element motive))))) =
    Tm.pi _ (rename wk (.pi (consTypeAt (subst sigma element) (subst sigma motive))
      (rename wk (resultTypeAt (subst sigma element) (subst sigma motive))))) at combined
  rw [subst_liftSub_wk] at combined
  have bodies := Normalization.rename_injective (ρ := wk) (Fin.succ_injective _) (Tm.pi.inj combined).2
  exact (Tm.pi.inj bodies).1

theorem after_motive_generic {n : Nat} {context : Tower.Ctx n} {element motive : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (motiveTyped : Typed rules context motive (motiveTypeAt element)) :
    Typed rules context (.app (.app (.const NativeNaturalVectorFamilies.vecEliminateName) element) motive)
      (afterMotiveTypeAt element motive) := by
  let sigma : Sub Tower.Head 2 n := consSub motive (consSub element Fin.elim0)
  have assignment : SubstMor rules parameterContext context sigma := by
    intro index
    fin_cases index
    · exact motiveTyped
    · exact elementTyped
  have linked := parameter_application_typed.substitute assignment
  rw [substitute_afterMotiveTypeAt] at linked
  have firstImage : sigma 1 = element := by
    change consSub motive (consSub element Fin.elim0) (Fin.succ 0) = element
    simp only [consSub_succ, consSub_zero]
  simpa only [subst, sigma, consSub_zero, firstImage] using linked

theorem rename_motive {n m : Nat} (renameMap : Ren n m)
    (source target : LevelExpr Nat) (element predicate : Tower.Tm n) :
    rename renameMap (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive source target element predicate) =
      NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive source target
        (rename renameMap element) (rename renameMap predicate) := by
  simpa only [subst_renSub] using
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.substitute_motive
      (renSub renameMap) source target element predicate

theorem after_motive_readback (direction : Direction) :
    afterMotiveTypeAt (.var 3) (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
      (source direction) (target direction) (.var 3) (.var 2)) = afterMotiveType direction := by
  norm_num [afterMotiveTypeAt, afterMotiveType, nilTypeAt, consTypeAt, resultTypeAt,
    nilInterface, consInterface, tailApplication, constructorApplication, resultInterface,
    NativeNaturalVectorFamilies.natTm, NativeNaturalVectorFamilies.vecApp,
    NativeNaturalVectorFamilies.vnilApp, NativeNaturalVectorFamilies.vconsApp,
    NativeNaturalVectorFamilies.succApp, rename_motive, rename, wk, liftRen,
    Fin.instOfNat, Fin.ofNat, Fin.succ, Fin.cases, Fin.induction, Fin.induction.go]

theorem cons_interface_readback (direction : Direction) :
    consTypeAt (.var 3) (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
      (source direction) (target direction) (.var 3) (.var 2)) = consInterface direction := by
  have combined := after_motive_readback direction
  change Tm.pi _ (rename wk (.pi _ _)) = Tm.pi _ (rename wk (.pi _ _)) at combined
  have bodies := Normalization.rename_injective (ρ := wk) (Fin.succ_injective _) (Tm.pi.inj combined).2
  exact (Tm.pi.inj bodies).1

theorem native_motive_typed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
      (source direction) (target direction) (.var 3) (.var 2)) (motiveTypeAt (.var 3)) := by
  have innerForm : Typed rules NativeVectorAllMapMethods.lengthContext
      (.pi (NativeNaturalVectorFamilies.vecApp (.var 4) (.var 0))
        (sortTm (.succ NativeVectorAll.Universes.CumulativeElimination.upperLevel)))
      (sortTm (.max NativeVectorAll.Universes.dataLevel
        (.succ (.succ NativeVectorAll.Universes.CumulativeElimination.upperLevel)))) :=
    .piForm NativeVectorAllMapMethods.Motive.vector_typed (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)
  have body : Typed rules NativeVectorAllMapMethods.Motive.context
      (NativeVectorAllMapMethods.Motive.body (source direction) (target direction))
      (sortTm (.succ NativeVectorAll.Universes.CumulativeElimination.upperLevel)) :=
    .sub (NativeVectorAllMapMethods.Motive.body_typed _ _ (source_formed direction) (target_formed direction))
      (.subUniv (by intro valuation; exact Nat.le_succ _))
  exact .lamIntro (motive_type_formed (element := .var 3) (.var 3))
    (.sort _) (.lamIntro innerForm (.sort _) body)

/-- A concrete native prefix before supplying either method. -/
theorem forward_after_motive : Typed rules NativeVectorAll.Universes.context
    (.app (.app (.const NativeNaturalVectorFamilies.vecEliminateName) (.var 3))
      (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
        NativeVectorAll.Universes.resultLevel NativeVectorAll.Universes.CumulativeElimination.upperLevel
        (.var 3) (.var 2)))
    (afterMotiveTypeAt (.var 3) (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
      NativeVectorAll.Universes.resultLevel NativeVectorAll.Universes.CumulativeElimination.upperLevel
      (.var 3) (.var 2))) :=
  after_motive_generic (element := .var 3) (.var 3) (native_motive_typed .forward)

theorem after_motive_typed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    (.app (.app (.const NativeNaturalVectorFamilies.vecEliminateName) (.var 3))
      (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
        (source direction) (target direction) (.var 3) (.var 2)))
    (afterMotiveType direction) := by
  rw [← after_motive_readback]
  exact after_motive_generic (.var 3) (native_motive_typed direction)

theorem after_nil_typed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    (.app (.app (.app (.const NativeNaturalVectorFamilies.vecEliminateName) (.var 3))
      (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
        (source direction) (target direction) (.var 3) (.var 2))) (.lam (.var 0)))
    (.pi (consInterface direction) (rename wk (resultInterface direction))) := by
  have applied := Derivable.appElim (after_motive_typed direction) (nil_method_typed direction)
  simpa only [afterMotiveType, inst0_rename_wk] using applied

theorem after_cons_typed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    (.app (.app (.app (.app (.const NativeNaturalVectorFamilies.vecEliminateName) (.var 3))
      (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
        (source direction) (target direction) (.var 3) (.var 2))) (.lam (.var 0)))
      NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.consCase)
    (resultInterface direction) := by
  have applied := Derivable.appElim (after_nil_typed direction) (cons_method_typed direction)
  simpa only [inst0_rename_wk] using applied

theorem applied_typed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map
      (source direction) (target direction) (.var 3) (.var 2) (.var 1) (.var 0))
    (.app (.app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
      (source direction) (target direction) (.var 3) (.var 2)) (.var 1)) (.var 0)) :=
  .appElim (.appElim (after_cons_typed direction) (.var 1)) (.var 0)

theorem map_typed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map
      (source direction) (target direction) (.var 3) (.var 2) (.var 1) (.var 0))
    (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.functionType
      (source direction) (target direction) (.var 3) (.var 2) (.var 1) (.var 0)) :=
  .conv (applied_typed direction) (motive_beta direction) (.sort _)

theorem forward_typed : Typed rules NativeVectorAll.Universes.context
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.forward
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.forwardType :=
  map_typed .forward

theorem backward_typed : Typed rules NativeVectorAll.Universes.context
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.backward
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.backwardType :=
  map_typed .backward

theorem map_typed_at (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number vector : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (vectorTyped : Typed rules context vector (NativeNaturalVectorFamilies.vecApp element number)) :
    Typed rules context
      (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map
        (source direction) (target direction) element predicate number vector)
      (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.functionType
        (source direction) (target direction) element predicate number vector) := by
  let sigma := NativeVectorAll.Universes.arguments element predicate number vector
  have linked := (map_typed direction).substitute
    (all_inputs_typed elementTyped predicateTyped numberTyped vectorTyped)
  have programReadback : subst sigma
      (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map
        (source direction) (target direction) (.var 3) (.var 2) (.var 1) (.var 0)) =
      NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map
        (source direction) (target direction) element predicate number vector := by
    rw [NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.substitute_map]
    rfl
  have typeReadback : subst sigma
      (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.functionType
        (source direction) (target direction) (.var 3) (.var 2) (.var 1) (.var 0)) =
      NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.functionType
        (source direction) (target direction) element predicate number vector := by
    rw [NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.substitute_functionType]
    rfl
  rw [programReadback, typeReadback] at linked
  exact linked

theorem forward_at_original : Typed rules NativeVectorAll.Universes.context
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.forward
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.forwardType :=
  map_typed_at .forward (element := .var 3) (predicate := .var 2) (number := .var 1) (vector := .var 0)
    (.var 3) (.var 2) (.var 1) (.var 0)

theorem cons_method_at (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number vector : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (vectorTyped : Typed rules context vector (NativeNaturalVectorFamilies.vecApp element number)) :
    Typed rules context NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.consCase
      (consTypeAt element (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
        (source direction) (target direction) element predicate)) := by
  let sigma := NativeVectorAll.Universes.arguments element predicate number vector
  have linked := (cons_method_typed direction).substitute
    (all_inputs_typed elementTyped predicateTyped numberTyped vectorTyped)
  have typeReadback : subst sigma (consInterface direction) =
      consTypeAt element (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.motive
        (source direction) (target direction) element predicate) := by
    rw [← cons_interface_readback, substitute_consTypeAt,
      NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.substitute_motive]
    rfl
  rw [typeReadback, NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.substitute_consCase] at linked
  exact linked

theorem cons_method_apply {n : Nat} {context : Tower.Ctx n}
    {element motive number head tail recursive : Tower.Tm n}
    (methodTyped : Typed rules context NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.consCase
      (consTypeAt element motive))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (headTyped : Typed rules context head element)
    (tailTyped : Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number))
    (recursiveTyped : Typed rules context recursive (.app (.app motive number) tail)) :
    Typed rules context
      (.app (.app (.app (.app NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.consCase number) head) tail) recursive)
      (.app (.app motive (NativeNaturalVectorFamilies.succApp number))
        (NativeNaturalVectorFamilies.vconsApp element number head tail)) := by
  have openingWeakening {k : Nat} (value body : Tower.Tm k) :
      subst (subst0 value) (rename wk body) = body := inst0_rename_wk value body
  have afterNumber := Derivable.appElim methodTyped numberTyped
  simp only [inst0, subst, openingWeakening, subst_liftSub_wk,
    liftSub_zero, liftSub_succ, subst0_zero,
    NativeNaturalVectorFamilies.subst_vecApp, NativeNaturalVectorFamilies.subst_succApp,
    NativeNaturalVectorFamilies.vconsApp] at afterNumber
  have afterHead := Derivable.appElim afterNumber headTyped
  simp only [inst0, subst, openingWeakening, subst_liftSub_wk,
    liftSub_zero, subst0_zero, NativeNaturalVectorFamilies.subst_vecApp, NativeNaturalVectorFamilies.subst_succApp] at afterHead
  have afterTail := Derivable.appElim afterHead tailTyped
  simp only [inst0, subst, openingWeakening, subst_liftSub_wk,
    subst0_zero, NativeNaturalVectorFamilies.subst_succApp] at afterTail
  have afterRecursive := Derivable.appElim afterTail recursiveTyped
  simpa only [inst0, subst, openingWeakening, subst_liftSub_wk,
    liftSub_zero, liftSub_succ, subst0_zero,
    NativeNaturalVectorFamilies.vconsApp, NativeNaturalVectorFamilies.succApp] using afterRecursive

theorem inhabited_iff {n : Nat} {context : Tower.Ctx n}
    {element predicate number vector : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (vectorTyped : Typed rules context vector (NativeNaturalVectorFamilies.vecApp element number)) :
    (∃ evidence, Typed rules context evidence
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse NativeVectorAll.Universes.resultLevel
        element predicate number vector)) ↔
    (∃ evidence, Typed rules context evidence
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse NativeVectorAll.Universes.CumulativeElimination.upperLevel
        element predicate number vector)) := by
  constructor
  · rintro ⟨evidence, checked⟩
    have applied := Derivable.appElim (map_typed_at .forward elementTyped predicateTyped numberTyped vectorTyped) checked
    exact ⟨_, by simpa only [NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.functionType,
      inst0_rename_wk, source, target] using applied⟩
  · rintro ⟨evidence, checked⟩
    have applied := Derivable.appElim (map_typed_at .backward elementTyped predicateTyped numberTyped vectorTyped) checked
    exact ⟨_, by simpa only [NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.functionType,
      inst0_rename_wk, source, target] using applied⟩

theorem inhabited_at_original :
    (∃ evidence, Typed rules NativeVectorAll.Universes.context evidence
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse NativeVectorAll.Universes.resultLevel
        (.var 3) (.var 2) (.var 1) (.var 0))) ↔
    (∃ evidence, Typed rules NativeVectorAll.Universes.context evidence
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse NativeVectorAll.Universes.CumulativeElimination.upperLevel
        (.var 3) (.var 2) (.var 1) (.var 0))) :=
  inhabited_iff (element := .var 3) (predicate := .var 2) (number := .var 1) (vector := .var 0)
    (.var 3) (.var 2) (.var 1) (.var 0)

/-- Cumulative use at the native bound does not identify the two universe heads. -/
theorem native_bound_not_head_equal :
    ¬ rules.headEq (.sort NativeVectorAll.Universes.CumulativeElimination.upperLevel)
      (.sort (.succ NativeVectorAll.Universes.CumulativeElimination.upperLevel)) := by
  intro same
  have atZero := same (fun _ => (0 : Nat))
  change (0 : Nat) = 1 at atZero
  cases atZero

theorem motive_type_syntax_distinct : NativeVectorAllMapMethods.Motive.type ≠ motiveTypeAt (.var 3) := by
  decide +kernel

#print axioms motive_beta_at
#print axioms nil_method_typed
#print axioms cons_method_typed
#print axioms forward_typed
#print axioms backward_typed
#print axioms map_typed_at
#print axioms inhabited_iff
#print axioms native_bound_not_head_equal

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllTypedMaps
