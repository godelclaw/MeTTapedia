import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorAnnotatedPrograms
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LaterArguments

/-!
# Typed indexed-vector operations over the original declaration library

The constructor and eliminator applications consume independently typed
arguments along their original dependent telescopes. The natural index
computation is the existing annotated addition used by the M1 program.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
namespace Programs.Annotated.Append

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Annotated
open Functions (natural zero successor motiveSort)

variable (enabled : ComputationProfiles.Selection) {n : Nat} {Γ : CCtx Tower.Head n}

def elementSort : CTm Tower.Head n := .head (.sort (.param 0))
def vector (element length : CTm Tower.Head n) : CTm Tower.Head n :=
  .app (.app (.const vecName) element) length
def nil (element : CTm Tower.Head n) : CTm Tower.Head n := .app (.const vnilName) element
def cons (element length head tail : CTm Tower.Head n) : CTm Tower.Head n :=
  .app (.app (.app (.app (.const vconsName) element) length) head) tail

theorem elementSort_typed : CTyped (church enabled) Γ elementSort
    (.head (.sort (.succ (.param 0)))) := .headType (.sort _)

theorem in_motive_universe {type : CTm Tower.Head n}
    (typed : CTyped (church enabled) Γ type elementSort) :
    CTyped (church enabled) Γ type motiveSort := by
  refine .cumul typed ?_
  change ∀ valuation : Nat → Nat, valuation 0 ≤ max (valuation 0) (valuation 1)
  exact fun valuation => Nat.le_max_left _ _

theorem vector_constant_typed : CTyped (church enabled) Γ (.const vecName)
    (.pi elementSort (.pi natural elementSort)) :=
  .const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel)
    (Evidence.declaration_4 enabled) (.sort _)

theorem vector_typed {element length : CTm Tower.Head n}
    (elementTyped : CTyped (church enabled) Γ element elementSort)
    (lengthTyped : CTyped (church enabled) Γ length natural) :
    CTyped (church enabled) Γ (vector element length) elementSort :=
  .appElim (.appElim (vector_constant_typed enabled) elementTyped) lengthTyped

theorem vector_index_equal {element first second : CTm Tower.Head n}
    (elementTyped : CTyped (church enabled) Γ element elementSort)
    (equal : CEqual (church enabled) Γ first second natural) :
    CEqual (church enabled) Γ (vector element first) (vector element second) elementSort :=
  .appCong (.refl (.appElim (vector_constant_typed enabled) elementTyped)) equal

theorem nil_constant_typed : CTyped (church enabled) Γ (.const vnilName)
    (.pi elementSort (vector (.var 0) zero)) :=
  .const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel)
    (Evidence.declaration_5 enabled) (.sort _)

theorem nil_typed {element : CTm Tower.Head n}
    (typed : CTyped (church enabled) Γ element elementSort) :
    CTyped (church enabled) Γ (nil element) (vector element zero) :=
  .appElim (nil_constant_typed enabled) typed

def consEntry : (scope : Nat) → Tower.Tm scope
  | 0 => .head (.sort (.param 0))
  | 1 => natTm
  | 2 => .var 1
  | 3 => vecApp (.var 2) (.var 1)
  | _ + 4 => natTm

def consContext : Tower.Ctx 4 := Normalization.ofEntries consEntry 4
def consResult : Tower.Tm 4 := vecApp (.var 3) (succApp (.var 2))

theorem cons_constant_typed : CTyped (church enabled) Γ (.const vconsName)
    (liftTm (TelescopeAbstraction.closeType consContext consResult)).liftClosed :=
  .const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel)
    (Evidence.declaration_6 enabled) (.sort _)

def consArguments (element length head tail : CTm Tower.Head n) : CSub Tower.Head 4 n :=
  Fin.cases tail (Fin.cases head (Fin.cases length (fun _ => element)))

theorem cons_typed {element length head tail : CTm Tower.Head n}
    (elementTyped : CTyped (church enabled) Γ element elementSort)
    (lengthTyped : CTyped (church enabled) Γ length natural)
    (headTyped : CTyped (church enabled) Γ head element)
    (tailTyped : CTyped (church enabled) Γ tail (vector element length)) :
    CTyped (church enabled) Γ (cons element length head tail) (vector element (successor length)) := by
  have arguments : CSubstMor (church enabled) (liftCtx consContext) Γ
      (consArguments element length head tail) := by
    intro index
    exact Fin.cases tailTyped (Fin.cases headTyped (Fin.cases lengthTyped
      (Fin.cases elementTyped (fun impossible => Fin.elim0 impossible)))) index
  exact applyAlong_typed (Q := church enabled) consEntry 4 consResult
    (consArguments element length head tail) arguments (cons_constant_typed enabled)

def result (element first second : CTm Tower.Head n) : CTm Tower.Head n :=
  vector element (Functions.add first second)

theorem result_typed {element first second : CTm Tower.Head n}
    (elementTyped : CTyped (church enabled) Γ element elementSort)
    (firstTyped : CTyped (church enabled) Γ first natural)
    (secondTyped : CTyped (church enabled) Γ second natural) :
    CTyped (church enabled) Γ (result element first second) elementSort :=
  vector_typed enabled elementTyped (Functions.add_typed enabled firstTyped secondTyped)

theorem result_substitute {scope : Nat} (σ : CSub Tower.Head n scope)
    (element first second : CTm Tower.Head n) :
    (result element first second).subst σ =
      result (element.subst σ) (first.subst σ) (second.subst σ) := rfl

def innerType (element first : CTm Tower.Head n) : CTm Tower.Head n :=
  .pi (vector element first) motiveSort

def familyType (element : CTm Tower.Head n) : CTm Tower.Head n :=
  .pi natural (innerType (element.rename wk) (.var 0))

theorem innerType_open (element number : CTm Tower.Head n) :
    CTm.inst0 number (innerType (element.rename wk) (.var 0)) = innerType element number := by
  change CTm.pi (vector (CTm.inst0 number (element.rename wk)) number) motiveSort = _
  rw [CTm.inst0_rename_wk]
  rfl

theorem family_applied {element family length value : CTm Tower.Head n}
    (familyTyped : CTyped (church enabled) Γ family (familyType element))
    (lengthTyped : CTyped (church enabled) Γ length natural)
    (valueTyped : CTyped (church enabled) Γ value (vector element length)) :
    CTyped (church enabled) Γ (.app (.app family length) value) motiveSort := by
  have function := CDerivable.appElim familyTyped lengthTyped
  change CTyped (church enabled) Γ (.app family length)
    (CTm.inst0 length (innerType (element.rename wk) (.var 0))) at function
  rw [innerType_open] at function
  exact .appElim function valueTyped

def recursorEntry : (scope : Nat) → Tower.Tm scope
  | 0 => .head (.sort (.param 0))
  | 1 => RussellTarski.substLevelsTm levels vecMotiveType
  | 2 => vecNilCaseType
  | 3 => vecConsCaseType
  | 4 => natTm
  | 5 => vecApp (.var 4) (.var 0)
  | _ + 6 => natTm

def recursorContext : Tower.Ctx 6 := Normalization.ofEntries recursorEntry 6
def recursorResult : Tower.Tm 6 := .app (.app (.var 4) (.var 1)) (.var 0)

theorem recursor_constant_typed : CTyped (church enabled) Γ (.const vecEliminateName)
    (liftTm (TelescopeAbstraction.closeType recursorContext recursorResult)).liftClosed :=
  .const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel)
    (Evidence.declaration_7 enabled) (.sort _)

def methodType (element family : CTm Tower.Head n) : CTm Tower.Head n :=
  .pi natural (.pi (element.rename wk)
    (.pi (vector ((element.rename wk).rename wk) (.var 1))
      (.pi (.app (.app (((family.rename wk).rename wk).rename wk) (.var 2)) (.var 0))
        (.app (.app ((((family.rename wk).rename wk).rename wk).rename wk) (successor (.var 3)))
          (cons ((((element.rename wk).rename wk).rename wk).rename wk)
            (.var 3) (.var 2) (.var 1))))))

def arguments (element family base method length value : CTm Tower.Head n) : CSub Tower.Head 6 n :=
  Fin.cases value (Fin.cases length (Fin.cases method
    (Fin.cases base (Fin.cases family (fun _ => element)))))

theorem arguments_typed {element family base method length value : CTm Tower.Head n}
    (elementTyped : CTyped (church enabled) Γ element elementSort)
    (familyTyped : CTyped (church enabled) Γ family (familyType element))
    (baseTyped : CTyped (church enabled) Γ base (.app (.app family zero) (nil element)))
    (methodTyped : CTyped (church enabled) Γ method (methodType element family))
    (lengthTyped : CTyped (church enabled) Γ length natural)
    (valueTyped : CTyped (church enabled) Γ value (vector element length)) :
    CSubstMor (church enabled) (liftCtx recursorContext) Γ
      (arguments element family base method length value) := by
  intro index
  exact Fin.cases valueTyped (Fin.cases lengthTyped (Fin.cases methodTyped
    (Fin.cases baseTyped (Fin.cases familyTyped
      (Fin.cases elementTyped (fun impossible => Fin.elim0 impossible)))))) index

def eliminate (element family base method length value : CTm Tower.Head n) : CTm Tower.Head n :=
  .app (.app (.app (.app (.app (.app (.const vecEliminateName) element) family) base) method) length) value

theorem eliminate_typed {element family base method length value : CTm Tower.Head n}
    (elementTyped : CTyped (church enabled) Γ element elementSort)
    (familyTyped : CTyped (church enabled) Γ family (familyType element))
    (baseTyped : CTyped (church enabled) Γ base (.app (.app family zero) (nil element)))
    (methodTyped : CTyped (church enabled) Γ method (methodType element family))
    (lengthTyped : CTyped (church enabled) Γ length natural)
    (valueTyped : CTyped (church enabled) Γ value (vector element length)) :
    CTyped (church enabled) Γ (eliminate element family base method length value)
      (.app (.app family length) value) :=
  applyAlong_typed (Q := church enabled) recursorEntry 6 recursorResult
    (arguments element family base method length value)
    (arguments_typed enabled elementTyped familyTyped baseTyped methodTyped lengthTyped valueTyped)
    (recursor_constant_typed enabled)

def motiveInner (element first second : CTm Tower.Head n) : CTm Tower.Head n :=
  .lam (vector element first)
    (result (element.rename wk) (first.rename wk) (second.rename wk))

def motive (element second : CTm Tower.Head n) : CTm Tower.Head n :=
  .lam natural (motiveInner (element.rename wk) (.var 0) (second.rename wk))

theorem innerType_typed {element first : CTm Tower.Head n}
    (elementTyped : CTyped (church enabled) Γ element elementSort)
    (firstTyped : CTyped (church enabled) Γ first natural) :
    CTyped (church enabled) Γ (innerType element first)
      (.head (.sort (.max (.param 0) (.succ (.max (.param 0) (.param 1)))))) :=
  .piForm (vector_typed enabled elementTyped firstTyped) (.sort _)
    (Functions.universe_typed enabled) (.sort _) (.sorts _ _)

theorem familyType_typed {element : CTm Tower.Head n}
    (typed : CTyped (church enabled) Γ element elementSort) :
    CTyped (church enabled) Γ (familyType element)
      (.head (.sort (.max (.const 0) (.max (.param 0) (.succ (.max (.param 0) (.param 1))))))) :=
  .piForm (Functions.natural_typed enabled) (.sort _)
    (innerType_typed enabled typed.weaken (.var 0)) (.sort _) (.sorts _ _)

theorem motiveInner_typed {element first second : CTm Tower.Head n}
    (elementTyped : CTyped (church enabled) Γ element elementSort)
    (firstTyped : CTyped (church enabled) Γ first natural)
    (secondTyped : CTyped (church enabled) Γ second natural) :
    CTyped (church enabled) Γ (motiveInner element first second) (innerType element first) :=
  .lamIntro (vector_typed enabled elementTyped firstTyped) (.sort _)
    (innerType_typed enabled elementTyped firstTyped) (.sort _)
    (in_motive_universe enabled (result_typed enabled elementTyped.weaken firstTyped.weaken secondTyped.weaken))

theorem motive_typed {element second : CTm Tower.Head n}
    (elementTyped : CTyped (church enabled) Γ element elementSort)
    (secondTyped : CTyped (church enabled) Γ second natural) :
    CTyped (church enabled) Γ (motive element second) (familyType element) :=
  .lamIntro (Functions.natural_typed enabled) (.sort _) (familyType_typed enabled elementTyped) (.sort _)
    (motiveInner_typed enabled elementTyped.weaken (.var 0) secondTyped.weaken)

theorem motiveInner_substitute {scope : Nat} (σ : CSub Tower.Head n scope)
    (element first second : CTm Tower.Head n) :
    (motiveInner element first second).subst σ =
      motiveInner (element.subst σ) (first.subst σ) (second.subst σ) := by
  simp only [motiveInner, vector, CTm.subst, result_substitute, CTm.subst_liftSub_wk]

theorem motiveInner_rename {scope : Nat} (ρ : Ren n scope)
    (element first second : CTm Tower.Head n) :
    (motiveInner element first second).rename ρ =
      motiveInner (element.rename ρ) (first.rename ρ) (second.rename ρ) := by
  simp only [motiveInner, vector, result, CTm.rename, Functions.add_rename, CTm.rename_liftRen_wk]

theorem motive_rename {scope : Nat} (ρ : Ren n scope) (element second : CTm Tower.Head n) :
    (motive element second).rename ρ = motive (element.rename ρ) (second.rename ρ) := by
  simp only [motive, CTm.rename, motiveInner_rename, CTm.rename_liftRen_wk]
  rfl

theorem motive_beta {element first second value : CTm Tower.Head n}
    (elementTyped : CTyped (church enabled) Γ element elementSort)
    (firstTyped : CTyped (church enabled) Γ first natural)
    (secondTyped : CTyped (church enabled) Γ second natural)
    (valueTyped : CTyped (church enabled) Γ value (vector element first)) :
    CEqual (church enabled) Γ (.app (.app (motive element second) first) value)
      (result element first second) motiveSort := by
  have betaFirst := CDerivable.betaPi (familyType_typed enabled elementTyped) (.sort _)
    (motiveInner_typed enabled elementTyped.weaken (.var 0) secondTyped.weaken) firstTyped
  change CEqual (church enabled) Γ (.app (motive element second) first)
    (CTm.inst0 first (motiveInner (element.rename wk) (.var 0) (second.rename wk)))
    (CTm.inst0 first (innerType (element.rename wk) (.var 0))) at betaFirst
  have openedValue : CTm.inst0 first
      (motiveInner (element.rename wk) (.var 0) (second.rename wk)) =
      motiveInner element first second := by
    rw [CTm.inst0, motiveInner_substitute]
    change motiveInner (CTm.inst0 first (element.rename wk)) first
      (CTm.inst0 first (second.rename wk)) = _
    rw [CTm.inst0_rename_wk, CTm.inst0_rename_wk]
  have openedType := innerType_open element first
  rw [openedValue, openedType] at betaFirst
  have applied := CDerivable.appCong betaFirst (.refl valueTyped)
  have body : CTyped (church enabled) (.snoc Γ (vector element first))
      (result (element.rename wk) (first.rename wk) (second.rename wk)) motiveSort :=
    in_motive_universe enabled
    (result_typed enabled elementTyped.weaken firstTyped.weaken secondTyped.weaken)
  have betaSecond := CDerivable.betaPi (innerType_typed enabled elementTyped firstTyped) (.sort _) body valueTyped
  change CEqual (church enabled) Γ (.app (motiveInner element first second) value)
    (CTm.inst0 value (result (element.rename wk) (first.rename wk) (second.rename wk))) motiveSort at betaSecond
  have openedResult : CTm.inst0 value
      (result (element.rename wk) (first.rename wk) (second.rename wk)) = result element first second := by
    rw [CTm.inst0, result_substitute]
    change result (CTm.inst0 value (element.rename wk)) (CTm.inst0 value (first.rename wk))
      (CTm.inst0 value (second.rename wk)) = _
    rw [CTm.inst0_rename_wk, CTm.inst0_rename_wk, CTm.inst0_rename_wk]
  rw [openedResult] at betaSecond
  exact .trans applied betaSecond

def lengthContext (context : CCtx Tower.Head n) : CCtx Tower.Head (n + 1) :=
  .snoc context natural

def headContext (context : CCtx Tower.Head n) (element : CTm Tower.Head n) :
    CCtx Tower.Head (n + 2) :=
  .snoc (lengthContext context) (element.rename wk)

def tailDomain (element : CTm Tower.Head n) : CTm Tower.Head (n + 2) :=
  vector ((element.rename wk).rename wk) (.var 1)

def tailContext (context : CCtx Tower.Head n) (element : CTm Tower.Head n) :
    CCtx Tower.Head (n + 3) :=
  .snoc (headContext context element) (tailDomain element)

def recursiveDomain (element second : CTm Tower.Head n) : CTm Tower.Head (n + 3) :=
  .app (.app ((((motive element second).rename wk).rename wk).rename wk) (.var 2)) (.var 0)

def methodContext (context : CCtx Tower.Head n) (element second : CTm Tower.Head n) :
    CCtx Tower.Head (n + 4) :=
  .snoc (tailContext context element) (recursiveDomain element second)

def methodResult (element second : CTm Tower.Head n) : CTm Tower.Head (n + 4) :=
  .app (.app (((((motive element second).rename wk).rename wk).rename wk).rename wk)
      (successor (.var 3)))
    (cons ((((element.rename wk).rename wk).rename wk).rename wk) (.var 3) (.var 2) (.var 1))

def methodBody (element second : CTm Tower.Head n) : CTm Tower.Head (n + 4) :=
  cons ((((element.rename wk).rename wk).rename wk).rename wk)
    (Functions.add (.var 3) ((((second.rename wk).rename wk).rename wk).rename wk)) (.var 2) (.var 0)

def method (element second : CTm Tower.Head n) : CTm Tower.Head n :=
  .lam natural (.lam (element.rename wk)
    (.lam (tailDomain element) (.lam (recursiveDomain element second) (methodBody element second))))

theorem method_body_typed {element second : CTm Tower.Head n}
    (permitted : enabled Functions.successorRow = true)
    (elementTyped : CTyped (church enabled) Γ element elementSort)
    (secondTyped : CTyped (church enabled) Γ second natural) :
    CTyped (church enabled) (methodContext Γ element second)
      (methodBody element second) (methodResult element second) := by
  let context := methodContext Γ element second
  let element4 := (((element.rename wk).rename wk).rename wk).rename wk
  let second4 := (((second.rename wk).rename wk).rename wk).rename wk
  have elementAt : CTyped (church enabled) context element4 elementSort :=
    elementTyped.weaken.weaken.weaken.weaken
  have secondAt : CTyped (church enabled) context second4 natural :=
    secondTyped.weaken.weaken.weaken.weaken
  have lengthAt : CTyped (church enabled) context (.var 3) natural := .var 3
  have headAt : CTyped (church enabled) context (.var 2) element4 := .var 2
  have tailAt : CTyped (church enabled) context (.var 1) (vector element4 (.var 3)) := .var 1
  have recursive : CTyped (church enabled) context (.var 0)
      (.app (.app (((((motive element second).rename wk).rename wk).rename wk).rename wk)
        (.var 3)) (.var 1)) := .var 0
  simp only [motive_rename] at recursive
  have recursiveResult : CTyped (church enabled) context (.var 0) (result element4 (.var 3) second4) :=
    .conv recursive (motive_beta enabled elementAt lengthAt secondAt tailAt) (.sort _)
  have produced := cons_typed enabled elementAt (Functions.add_typed enabled lengthAt secondAt)
    headAt recursiveResult
  have indexEquality := vector_index_equal enabled elementAt
    (Functions.add_successor enabled permitted lengthAt secondAt)
  have adjusted : CTyped (church enabled) context (methodBody element second)
      (result element4 (successor (.var 3)) second4) :=
    .conv produced (.symm indexEquality) (.sort _)
  have sourceCons := cons_typed enabled elementAt lengthAt headAt tailAt
  have finished := CDerivable.conv adjusted
    (.symm (motive_beta enabled elementAt (Functions.successor_typed enabled lengthAt) secondAt sourceCons))
    (.sort _)
  simpa only [methodResult, motive_rename] using finished

theorem method_typed {element second : CTm Tower.Head n}
    (permitted : enabled Functions.successorRow = true)
    (elementTyped : CTyped (church enabled) Γ element elementSort)
    (secondTyped : CTyped (church enabled) Γ second natural) :
    CTyped (church enabled) Γ (method element second)
      (methodType element (motive element second)) := by
  have lengthForm : CIsType (church enabled) Γ natural :=
    ⟨_, .sort _, Functions.natural_typed enabled⟩
  have headForm : CIsType (church enabled) (lengthContext Γ) (element.rename wk) :=
    ⟨_, .sort _, elementTyped.weaken⟩
  have tailForm : CIsType (church enabled) (headContext Γ element) (tailDomain element) :=
    ⟨_, .sort _, vector_typed enabled elementTyped.weaken.weaken (.var 1)⟩
  have recursiveForm : CIsType (church enabled) (tailContext Γ element)
      (recursiveDomain element second) := by
    refine ⟨.sort (.max (.param 0) (.param 1)), .sort _, ?_⟩
    change CTyped (church enabled) (tailContext Γ element)
      (.app (.app ((((motive element second).rename wk).rename wk).rename wk) (.var 2)) (.var 0))
      motiveSort
    simp only [motive_rename]
    exact family_applied enabled
        (motive_typed enabled elementTyped.weaken.weaken.weaken secondTyped.weaken.weaken.weaken)
        (.var 2) (.var 0)
  have resultForm : CIsType (church enabled) (methodContext Γ element second)
      (methodResult element second) := by
    refine ⟨.sort (.max (.param 0) (.param 1)), .sort _, ?_⟩
    change CTyped (church enabled) (methodContext Γ element second)
      (methodResult element second) motiveSort
    simp only [methodResult, motive_rename]
    exact family_applied enabled
        (motive_typed enabled elementTyped.weaken.weaken.weaken.weaken
          secondTyped.weaken.weaken.weaken.weaken)
        (Functions.successor_typed enabled (.var 3))
        (cons_typed enabled elementTyped.weaken.weaken.weaken.weaken
          (.var 3) (.var 2) (.var 1))
  exact CTyped.abstractTerm (levelModel enabled) lengthForm
    (CIsType.pi (levelModel enabled) headForm
      (CIsType.pi (levelModel enabled) tailForm
        (CIsType.pi (levelModel enabled) recursiveForm resultForm)))
    (CTyped.abstractTerm (levelModel enabled) headForm
      (CIsType.pi (levelModel enabled) tailForm
        (CIsType.pi (levelModel enabled) recursiveForm resultForm))
      (CTyped.abstractTerm (levelModel enabled) tailForm
        (CIsType.pi (levelModel enabled) recursiveForm resultForm)
        (CTyped.abstractTerm (levelModel enabled) recursiveForm resultForm
          (method_body_typed enabled permitted elementTyped secondTyped))))

theorem nil_branch_typed {element second right : CTm Tower.Head n}
    (permitted : enabled Functions.zeroRow = true)
    (elementTyped : CTyped (church enabled) Γ element elementSort)
    (secondTyped : CTyped (church enabled) Γ second natural)
    (rightTyped : CTyped (church enabled) Γ right (vector element second)) :
    CTyped (church enabled) Γ right (.app (.app (motive element second) zero) (nil element)) := by
  have indexEquality := vector_index_equal enabled elementTyped
    (Functions.add_zero enabled permitted secondTyped)
  have typedResult : CTyped (church enabled) Γ right (result element zero second) :=
    .conv rightTyped (.symm indexEquality) (.sort _)
  exact .conv typedResult
    (.symm (motive_beta enabled elementTyped (Functions.zero_typed enabled) secondTyped
      (nil_typed enabled elementTyped))) (.sort _)

def append (element first second left right : CTm Tower.Head n) : CTm Tower.Head n :=
  eliminate element (motive element second) right (method element second) first left

theorem append_typed {element first second left right : CTm Tower.Head n}
    (zeroPermitted : enabled Functions.zeroRow = true)
    (successorPermitted : enabled Functions.successorRow = true)
    (elementTyped : CTyped (church enabled) Γ element elementSort)
    (firstTyped : CTyped (church enabled) Γ first natural)
    (secondTyped : CTyped (church enabled) Γ second natural)
    (leftTyped : CTyped (church enabled) Γ left (vector element first))
    (rightTyped : CTyped (church enabled) Γ right (vector element second)) :
    CTyped (church enabled) Γ (append element first second left right) (result element first second) :=
  .conv (eliminate_typed enabled elementTyped (motive_typed enabled elementTyped secondTyped)
    (nil_branch_typed enabled zeroPermitted elementTyped secondTyped rightTyped)
    (method_typed enabled successorPermitted elementTyped secondTyped) firstTyped leftTyped)
    (motive_beta enabled elementTyped firstTyped secondTyped leftTyped) (.sort _)

def functionContext : CCtx Tower.Head 5 := liftCtx Programs.appendContext
def functionBody : CTm Tower.Head 5 := append (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)
def functionResult : CTm Tower.Head 5 := result (.var 4) (.var 3) (.var 2)
def appendFunction : CTm Tower.Head 0 := Impredicative.Domain.lamsCtx functionContext functionBody
def appendFunctionType : CTm Tower.Head 0 := Impredicative.Domain.pisCtx functionContext functionResult

theorem functionContext_formed : CCtxFormed (church enabled) functionContext := by
  refine .snoc (.snoc (.snoc (.snoc (.snoc .nil ?_) ?_) ?_) ?_) ?_
  · exact ⟨_, .sort _, elementSort_typed enabled⟩
  · exact ⟨_, .sort _, Functions.natural_typed enabled⟩
  · exact ⟨_, .sort _, Functions.natural_typed enabled⟩
  · exact ⟨_, .sort _, vector_typed enabled (.var 2) (.var 1)⟩
  · exact ⟨_, .sort _, vector_typed enabled (.var 3) (.var 1)⟩

theorem functionBody_typed
    (zeroPermitted : enabled Functions.zeroRow = true)
    (successorPermitted : enabled Functions.successorRow = true) :
    CTyped (church enabled) functionContext functionBody functionResult :=
  append_typed enabled zeroPermitted successorPermitted (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

theorem functionResult_typed : CTyped (church enabled) functionContext functionResult elementSort :=
  result_typed enabled (.var 4) (.var 3) (.var 2)

theorem appendFunction_typed
    (zeroPermitted : enabled Functions.zeroRow = true)
    (successorPermitted : enabled Functions.successorRow = true) :
    CTyped (church enabled) .nil appendFunction appendFunctionType :=
  lamsCtx_typed (levelModel enabled) (functionContext_formed enabled)
    ⟨_, .sort _, functionResult_typed enabled⟩
    (functionBody_typed enabled zeroPermitted successorPermitted)

theorem motive_erases (element second : CTm Tower.Head n) :
    (motive element second).erase = Programs.appendMotive element.erase second.erase := by
  simp only [motive, motiveInner, result, vector, CTm.erase, Functions.add_erases,
    CTm.erase_rename, Programs.appendMotive, rename_comp]
  rfl

theorem method_erases (element second : CTm Tower.Head n) :
    (method element second).erase = Programs.appendCons element.erase second.erase := by
  simp only [method, methodBody, cons, CTm.erase, Functions.add_erases, CTm.erase_rename,
    Programs.appendCons, rename_comp]
  rfl

theorem append_erases (element first second left right : CTm Tower.Head n) :
    (append element first second left right).erase =
      Programs.append element.erase first.erase second.erase left.erase right.erase := by
  simp only [append, eliminate, CTm.erase, motive_erases, method_erases]
  rfl

theorem appendFunction_erases : appendFunction.erase = Programs.appendTerm := by
  change Tm.lam (.lam (.lam (.lam (.lam functionBody.erase)))) = _
  rw [functionBody, append_erases]
  rfl

theorem appendFunctionType_erases : appendFunctionType.erase = Programs.appendType := rfl

/-- The existing annotator receives the original raw program and the
independently formed dependent function type. Its result grants no authority
until the typing derivation below checks that concrete output. -/
def producedAppendFunction (selection : ComputationProfiles.Selection) : CTm Tower.Head 0 :=
  (elaborate (church selection).constantType Knowledge.empty (some appendFunctionType) none
    Programs.appendTerm).1

theorem producedAppendFunction_exact : producedAppendFunction enabled = appendFunction := by
  dsimp only [producedAppendFunction]
  rw [constantType_eq enabled]
  clear! enabled
  decide +kernel

theorem producedAppendFunction_typed
    (zeroPermitted : enabled Functions.zeroRow = true)
    (successorPermitted : enabled Functions.successorRow = true) :
    CTyped (church enabled) .nil (producedAppendFunction enabled) appendFunctionType := by
  rw [producedAppendFunction_exact]
  exact appendFunction_typed enabled zeroPermitted successorPermitted

theorem naturalOnly_typed :
    CTyped (church ComputationProfiles.naturalOnly) .nil appendFunction appendFunctionType :=
  appendFunction_typed _ (by decide +kernel) (by decide +kernel)

def unconstrainedAppendFunction (selection : ComputationProfiles.Selection) : CTm Tower.Head 0 :=
  (elaborate (church selection).constantType Knowledge.empty none none Programs.appendTerm).1

/-- Erasure still recovers the source when the expected type is omitted;
the resulting placeholder domains differ from the independently typed program. -/
theorem unconstrained_erasure_distinction :
    (unconstrainedAppendFunction enabled).erase = Programs.appendTerm ∧
      unconstrainedAppendFunction enabled ≠ appendFunction := by
  refine ⟨erase_elab _ _ _ _ _, ?_⟩
  dsimp only [unconstrainedAppendFunction]
  rw [constantType_eq enabled]
  clear! enabled
  decide +kernel

def verdicts : List (String × Bool) :=
  [("annotated append erases to the original M1 program",
      decide (appendFunction.erase = Programs.appendTerm)),
   ("annotated append type erases to the original dependent function type",
      decide (appendFunctionType.erase = Programs.appendType)),
   ("the existing annotator reconstructs the independently typed append",
      decide (producedAppendFunction ComputationProfiles.naturalOnly = appendFunction)),
   ("erasure alone does not identify append's recovered domains",
      decide ((unconstrainedAppendFunction ComputationProfiles.naturalOnly).erase = Programs.appendTerm) &&
        decide (unconstrainedAppendFunction ComputationProfiles.naturalOnly ≠ appendFunction))]

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

def methodTelescope (element second : CTm Tower.Head n) : CTele Tower.Head n (n + 4) :=
  .cons natural (.cons (element.rename wk)
    (.cons (tailDomain element) (.cons (recursiveDomain element second) .nil)))

theorem methodContext_formed {element second : CTm Tower.Head n}
    (formed : CCtxFormed (church enabled) Γ)
    (elementTyped : CTyped (church enabled) Γ element elementSort)
    (secondTyped : CTyped (church enabled) Γ second natural) :
    CCtxFormed (church enabled) (methodContext Γ element second) := by
  refine .snoc (.snoc (.snoc (.snoc formed ?_) ?_) ?_) ?_
  · exact ⟨_, .sort _, Functions.natural_typed enabled⟩
  · exact ⟨_, .sort _, elementTyped.weaken⟩
  · exact ⟨_, .sort _, vector_typed enabled elementTyped.weaken.weaken (.var 1)⟩
  · refine ⟨.sort (.max (.param 0) (.param 1)), .sort _, ?_⟩
    change CTyped (church enabled) (tailContext Γ element) (recursiveDomain element second) motiveSort
    simp only [recursiveDomain, motive_rename]
    exact family_applied enabled
      (motive_typed enabled elementTyped.weaken.weaken.weaken secondTyped.weaken.weaken.weaken)
      (.var 2) (.var 0)

theorem methodResult_typed {element second : CTm Tower.Head n}
    (elementTyped : CTyped (church enabled) Γ element elementSort)
    (secondTyped : CTyped (church enabled) Γ second natural) :
    CTyped (church enabled) (methodContext Γ element second) (methodResult element second) motiveSort := by
  simp only [methodResult, motive_rename]
  exact family_applied enabled
    (motive_typed enabled elementTyped.weaken.weaken.weaken.weaken
      secondTyped.weaken.weaken.weaken.weaken)
    (Functions.successor_typed enabled (.var 3))
    (cons_typed enabled elementTyped.weaken.weaken.weaken.weaken (.var 3) (.var 2) (.var 1))

theorem method_apply_equal {element second length head tail recursive : CTm Tower.Head n}
    (formed : CCtxFormed (church enabled) Γ)
    (permitted : enabled Functions.successorRow = true)
    (elementTyped : CTyped (church enabled) Γ element elementSort)
    (secondTyped : CTyped (church enabled) Γ second natural)
    (lengthTyped : CTyped (church enabled) Γ length natural)
    (headTyped : CTyped (church enabled) Γ head element)
    (tailTyped : CTyped (church enabled) Γ tail (vector element length))
    (recursiveTyped : CTyped (church enabled) Γ recursive
      (.app (.app (motive element second) length) tail)) :
    CEqual (church enabled) Γ
      (.app (.app (.app (.app (method element second) length) head) tail) recursive)
      (cons element (Functions.add length second) head recursive)
      (.app (.app (motive element second) (successor length)) (cons element length head tail)) := by
  let assignment : CSub Tower.Head (n + 4) n :=
    CTm.consSub recursive (CTm.consSub tail (CTm.consSub head (CTm.consSub length CTm.ids)))
  let raiseFour (term : CTm Tower.Head n) : CTm Tower.Head (n + 4) :=
    (((term.rename wk).rename wk).rename wk).rename wk
  have raised (term : CTm Tower.Head n) : (raiseFour term).subst assignment = term := by
    dsimp only [raiseFour]
    simp only [CTm.subst_rename]
    exact CTm.subst_ids term
  have typed : CSubstMor (church enabled) (methodContext Γ element second) Γ assignment := by
    intro index
    refine Fin.cases ?_ (fun index => ?_) index
    · change CTyped (church enabled) Γ recursive
        (.app (.app ((raiseFour (motive element second)).subst assignment) length) tail)
      rw [raised]
      exact recursiveTyped
    · refine Fin.cases ?_ (fun index => ?_) index
      · change CTyped (church enabled) Γ tail
          (vector ((raiseFour element).subst assignment) length)
        rw [raised]
        exact tailTyped
      · refine Fin.cases ?_ (fun index => ?_) index
        · change CTyped (church enabled) Γ head
            ((raiseFour element).subst assignment)
          rw [raised]
          exact headTyped
        · refine Fin.cases ?_ (fun index => ?_) index
          · exact lengthTyped
          · change CTyped (church enabled) Γ (.var index)
              ((raiseFour (Γ.lookup index)).subst assignment)
            rw [raised]
            exact .var index
  have applied := CTele.lams_apply (levelModel enabled) (methodTelescope element second) assignment
    (methodContext_formed enabled formed elementTyped secondTyped)
    ⟨_, .sort _, methodResult_typed enabled elementTyped secondTyped⟩
    (method_body_typed enabled permitted elementTyped secondTyped) typed
  have atFirst : assignment (3 : Fin (n + 4)) = length := by
    change assignment (((0 : Fin (n + 1)).succ).succ).succ = length
    rfl
  have atHead : assignment (2 : Fin (n + 4)) = head := by
    change assignment ((0 : Fin (n + 2)).succ).succ = head
    rfl
  have atTail : assignment (1 : Fin (n + 4)) = tail := by
    change assignment (0 : Fin (n + 3)).succ = tail
    rfl
  have atRecursive : assignment (0 : Fin (n + 4)) = recursive := rfl
  change CEqual (church enabled) Γ
    (.app (.app (.app (.app ((method element second).subst CTm.ids) length) head) tail) recursive)
    ((methodBody element second).subst assignment) ((methodResult element second).subst assignment) at applied
  rw [CTm.subst_ids] at applied
  dsimp only [raiseFour] at raised
  simpa only [methodBody, methodResult, cons, successor, CTm.subst, Functions.add_substitute, raised,
    atFirst, atHead, atTail, atRecursive] using applied

def nilRow : Row := ⟨2, by decide +kernel⟩
def consRow : Row := ⟨3, by decide +kernel⟩

theorem append_nil {element second right : CTm Tower.Head n}
    (zeroPermitted : enabled Functions.zeroRow = true)
    (successorPermitted : enabled Functions.successorRow = true)
    (nilPermitted : enabled nilRow = true)
    (elementTyped : CTyped (church enabled) Γ element elementSort)
    (secondTyped : CTyped (church enabled) Γ second natural)
    (rightTyped : CTyped (church enabled) Γ right (vector element second)) :
    CEqual (church enabled) Γ (append element zero second (nil element) right) right
      (vector element second) := by
  have family := motive_typed enabled elementTyped secondTyped
  have base := nil_branch_typed enabled zeroPermitted elementTyped secondTyped rightTyped
  have step := method_typed enabled successorPermitted elementTyped secondTyped
  have allArguments := arguments_typed enabled elementTyped family base step
    (Functions.zero_typed enabled) (nil_typed enabled elementTyped)
  let assignment : CSub Tower.Head 4 n :=
    Fin.cases (method element second) (Fin.cases right (Fin.cases (motive element second) (fun _ => element)))
  have selected : CSubstMor (church enabled) (context nilRow) Γ assignment := by
    intro index
    fin_cases index
    · exact allArguments (2 : Fin 6)
    · exact allArguments (3 : Fin 6)
    · exact allArguments (4 : Fin 6)
    · exact allArguments (5 : Fin 6)
  have equation := instantiated_equal enabled nilRow nilPermitted selected
  change CEqual (church enabled) Γ (append element zero second (nil element) right) right
    (.app (.app (motive element second) zero) (nil element)) at equation
  have atResult := CDerivable.convEq equation
    (motive_beta enabled elementTyped (Functions.zero_typed enabled) secondTyped
      (nil_typed enabled elementTyped)) (.sort _)
  exact .convEq atResult (vector_index_equal enabled elementTyped
    (Functions.add_zero enabled zeroPermitted secondTyped)) (.sort _)

theorem append_cons {element first second head tail right : CTm Tower.Head n}
    (formed : CCtxFormed (church enabled) Γ)
    (zeroPermitted : enabled Functions.zeroRow = true)
    (successorPermitted : enabled Functions.successorRow = true)
    (consPermitted : enabled consRow = true)
    (elementTyped : CTyped (church enabled) Γ element elementSort)
    (firstTyped : CTyped (church enabled) Γ first natural)
    (secondTyped : CTyped (church enabled) Γ second natural)
    (headTyped : CTyped (church enabled) Γ head element)
    (tailTyped : CTyped (church enabled) Γ tail (vector element first))
    (rightTyped : CTyped (church enabled) Γ right (vector element second)) :
    CEqual (church enabled) Γ (append element (successor first) second
      (cons element first head tail) right)
      (cons element (Functions.add first second) head (append element first second tail right))
      (result element (successor first) second) := by
  have family := motive_typed enabled elementTyped secondTyped
  have base := nil_branch_typed enabled zeroPermitted elementTyped secondTyped rightTyped
  have step := method_typed enabled successorPermitted elementTyped secondTyped
  have allArguments := arguments_typed enabled elementTyped family base step firstTyped tailTyped
  let assignment : CSub Tower.Head 7 n := Fin.cases tail (Fin.cases head (Fin.cases first
    (Fin.cases (method element second) (Fin.cases right (Fin.cases (motive element second)
      (fun _ => element))))))
  have selected : CSubstMor (church enabled) (context consRow) Γ assignment := by
    intro index
    fin_cases index
    · exact tailTyped
    · exact headTyped
    · exact firstTyped
    · exact allArguments (2 : Fin 6)
    · exact allArguments (3 : Fin 6)
    · exact allArguments (4 : Fin 6)
    · exact allArguments (5 : Fin 6)
  have equation := instantiated_equal enabled consRow consPermitted selected
  change CEqual (church enabled) Γ (append element (successor first) second
    (cons element first head tail) right)
    (.app (.app (.app (.app (method element second) first) head) tail)
      (append element first second tail right))
    (.app (.app (motive element second) (successor first)) (cons element first head tail)) at equation
  have recursive := eliminate_typed enabled elementTyped family base step firstTyped tailTyped
  have computed := method_apply_equal enabled formed successorPermitted elementTyped secondTyped
    firstTyped headTyped tailTyped recursive
  exact .convEq (.trans equation computed)
    (motive_beta enabled elementTyped (Functions.successor_typed enabled firstTyped) secondTyped
      (cons_typed enabled elementTyped firstTyped headTyped tailTyped)) (.sort _)

theorem natural_as_element : CTyped (church enabled) Γ natural elementSort := by
  refine .cumul (Functions.natural_typed enabled) ?_
  exact fun _ => Nat.zero_le _

theorem closed_nil : CEqual (church (fun _ => true)) .nil
    (append natural zero zero (nil natural) (nil natural)) (nil natural) (vector natural zero) :=
  append_nil _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (natural_as_element _) (Functions.zero_typed _) (nil_typed _ (natural_as_element _))

def closedConsSource : CTm Tower.Head 0 :=
  append natural (successor zero) zero (cons natural zero zero (nil natural)) (nil natural)

def closedConsTarget : CTm Tower.Head 0 :=
  cons natural (Functions.add zero zero) zero (append natural zero zero (nil natural) (nil natural))

theorem closed_cons : CEqual (church (fun _ => true)) .nil closedConsSource closedConsTarget
    (result natural (successor zero) zero) :=
  append_cons _ .nil (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (natural_as_element _) (Functions.zero_typed _) (Functions.zero_typed _)
    (Functions.zero_typed _) (nil_typed _ (natural_as_element _)) (nil_typed _ (natural_as_element _))

/-- Typed equation erasure retains the independent original program and its
recursive cons target. The raw typed-equality judgment remains distinct from
formation-sensitive structural conversion. -/
theorem closed_cons_erased : Equal (ComputationProfiles.rules (fun _ => true)) .nil
    (Programs.append natTm (succApp zeroTm) zeroTm (vconsApp natTm zeroTm zeroTm (vnilApp natTm))
      (vnilApp natTm))
    (vconsApp natTm (Programs.add zeroTm zeroTm) zeroTm
      (Programs.append natTm zeroTm zeroTm (vnilApp natTm) (vnilApp natTm)))
    (vecApp natTm (Programs.add (succApp zeroTm) zeroTm)) := by
  simpa only [CStatement.erase, closedConsSource, closedConsTarget, append_erases,
    cons, nil, result, vector, CTm.erase, CCtx.erase, Functions.add_erases, natural, zero, successor,
    natTm, zeroTm, succApp, vecApp, vconsApp, vnilApp]
    using closed_cons.erase

theorem typed_with_vector_rows_disabled :
    CTyped (church ComputationProfiles.naturalOnly) .nil appendFunction appendFunctionType ∧
      ComputationProfiles.naturalOnly nilRow = false ∧
      ComputationProfiles.naturalOnly consRow = false :=
  ⟨naturalOnly_typed, by decide +kernel, by decide +kernel⟩

def nilCertificate (selection : ComputationProfiles.Selection) : (ComputationProfiles.decoder selection).Code 0 :=
  .declared ⟨2, [(method natural zero).erase, (nil natural).erase,
    (motive natural zero).erase, (natural : CTm Tower.Head 0).erase]⟩

def consCertificate (selection : ComputationProfiles.Selection) : (ComputationProfiles.decoder selection).Code 0 :=
  .declared ⟨3, [(nil natural).erase, (zero : CTm Tower.Head 0).erase, (zero : CTm Tower.Head 0).erase,
    (method natural zero).erase, (nil natural).erase, (motive natural zero).erase,
    (natural : CTm Tower.Head 0).erase]⟩

def computationVerdicts : List (String × Bool) :=
  [("the original full policy accepts actual append nil computation evidence",
      ((ComputationProfiles.decoder (fun _ => true)).decode (nilCertificate _)).isSome),
   ("the original full policy accepts actual append cons computation evidence",
      ((ComputationProfiles.decoder (fun _ => true)).decode (consCertificate _)).isSome),
   ("append's smaller typing policy refuses its nil computation citation",
      ((ComputationProfiles.decoder ComputationProfiles.naturalOnly).decode (nilCertificate _)).isNone),
   ("append's smaller typing policy refuses its cons computation citation",
      ((ComputationProfiles.decoder ComputationProfiles.naturalOnly).decode (consCertificate _)).isNone)]

theorem all_computationVerdicts : computationVerdicts.all Prod.snd = true := by decide +kernel

/-- An intermediate computation policy: natural recursion and vector nil,
with vector cons still disabled. The declarations and universe rules agree. -/
def naturalAndNil : ComputationProfiles.Selection := fun index => decide (index.val < 3)

theorem naturalOnly_included : ∀ index,
    ComputationProfiles.naturalOnly index = true → naturalAndNil index = true := by
  intro index permitted
  simp only [ComputationProfiles.naturalOnly, naturalAndNil, decide_eq_true_eq] at *
  omega

/-- Two genuine policy extensions transport the independently typed
function through the common composed package morphism. -/
theorem function_after_two_extensions :
    CTyped (church (fun _ => true)) .nil appendFunction appendFunctionType := by
  have first := permissions_morphism naturalOnly_included
  have second : (church naturalAndNil).Morphism (church (fun _ => true)) (fun head => head) :=
    permissions_morphism (fun _ _ => rfl)
  simpa only [Function.comp_def, CStatement.mapHead_id] using
    naturalOnly_typed.mapHead (second.comp first)

theorem nil_before_cons : CEqual (church naturalAndNil) .nil
    (append natural zero zero (nil natural) (nil natural)) (nil natural) (vector natural zero) :=
  append_nil _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (natural_as_element _) (Functions.zero_typed _) (nil_typed _ (natural_as_element _))

/-- The new cons permission changes this actual certificate's acceptance.
This is strictness of submitted computation support, not a general failure
of theorem reflection or an untypability claim. -/
theorem cons_certificate_strict :
    ((ComputationProfiles.decoder naturalAndNil).decode (consCertificate _)).isNone = true ∧
      ((ComputationProfiles.decoder (fun _ => true)).decode (consCertificate _)).isSome = true := by
  decide +kernel

def profileVerdicts : List (String × Bool) :=
  [("the intermediate policy accepts actual append nil computation",
      ((ComputationProfiles.decoder naturalAndNil).decode (nilCertificate _)).isSome),
   ("the intermediate policy still refuses actual append cons computation",
      ((ComputationProfiles.decoder naturalAndNil).decode (consCertificate _)).isNone)]

theorem all_profileVerdicts : profileVerdicts.all Prod.snd = true := by decide +kernel

end Programs.Annotated.Append
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
