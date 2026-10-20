import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorAnnotatedChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.TelescopeAbstractions

/-!
# Explicit domains for the natural computation used by dependent append

The motive, constructor method and complete addition function carry actual
Church domains. Typing uses the already checked declaration library and finite
typed beta conversions. The existing bidirectional annotator reconstructs the
independently typed function. Its zero/successor equations retain their exact
root permissions. No former-injectivity or uniform annotated-admission premise
is assumed; full dependent append annotation remains separate.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
namespace Programs.Annotated.Functions

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel

variable (enabled : ComputationProfiles.Selection) {n : Nat} {Γ : CCtx Tower.Head n}

def natural : CTm Tower.Head n := .const natName
def zero : CTm Tower.Head n := .const zeroName
def successor (number : CTm Tower.Head n) : CTm Tower.Head n := .app (.const succName) number
def motiveSort : CTm Tower.Head n := .head (.sort (.max (.param 0) (.param 1)))
def motive : CTm Tower.Head n := .lam natural natural

theorem natural_typed : CTyped (church enabled) Γ natural (.head (.sort (.const 0))) := by
  exact .const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel)
    (Evidence.declaration_0 enabled) (.sort _)

theorem zero_typed : CTyped (church enabled) Γ zero natural := by
  exact .const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel)
    (Evidence.declaration_1 enabled) (.sort _)

theorem successor_constant_typed :
    CTyped (church enabled) Γ (.const succName) (.pi natural natural) :=
  .const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel)
    (Evidence.declaration_2 enabled) (.sort _)

theorem successor_typed {number : CTm Tower.Head n}
    (typed : CTyped (church enabled) Γ number natural) :
    CTyped (church enabled) Γ (successor number) natural :=
  .appElim (successor_constant_typed enabled) typed

theorem successor_equal {first second : CTm Tower.Head n}
    (equal : CEqual (church enabled) Γ first second natural) :
    CEqual (church enabled) Γ (successor first) (successor second) natural :=
  .appCong (.refl (successor_constant_typed enabled)) equal

theorem natural_in_universe : CTyped (church enabled) Γ natural motiveSort := by
  refine .cumul (natural_typed enabled) ?_
  change ∀ valuation : Nat → Nat, 0 ≤ max (valuation 0) (valuation 1)
  intro valuation
  exact Nat.zero_le _

theorem universe_typed : CTyped (church enabled) Γ motiveSort
    (.head (.sort (.succ (.max (.param 0) (.param 1))))) := .headType (.sort _)

theorem motive_type : CTyped (church enabled) Γ (.pi natural motiveSort)
    (.head (.sort (.max (.const 0) (.succ (.max (.param 0) (.param 1)))))) :=
  .piForm (natural_typed enabled) (.sort _) (universe_typed enabled) (.sort _) (.sorts _ _)

theorem motive_typed : CTyped (church enabled) Γ motive (.pi natural motiveSort) :=
  .lamIntro (natural_typed enabled) (.sort _) (motive_type enabled) (.sort _)
    (natural_in_universe enabled)

theorem motive_applied {number : CTm Tower.Head n}
    (typed : CTyped (church enabled) Γ number natural) :
    CTyped (church enabled) Γ (.app motive number) motiveSort :=
  .appElim (motive_typed enabled) typed

theorem motive_beta {number : CTm Tower.Head n}
    (typed : CTyped (church enabled) Γ number natural) :
    CEqual (church enabled) Γ (.app motive number) natural motiveSort :=
  .betaPi (motive_type enabled) (.sort _) (natural_in_universe enabled) typed

def stepType : CTm Tower.Head n :=
  .pi natural (.pi (.app motive (.var 0)) (.app motive (successor (.var 1))))

def step : CTm Tower.Head n :=
  .lam natural (.lam (.app motive (.var 0)) (successor (.var 0)))

theorem step_inner_type : CTyped (church enabled) (.snoc Γ natural)
    (.pi (.app motive (.var 0)) (.app motive (successor (.var 1))))
    (.head (.sort (.max (.max (.param 0) (.param 1)) (.max (.param 0) (.param 1))))) := by
  apply CDerivable.piForm (motive_applied enabled (.var 0)) (.sort _)
    (motive_applied enabled (successor_typed enabled (.var 1))) (.sort _) (.sorts _ _)

theorem step_type : CTyped (church enabled) Γ stepType
    (.head (.sort (.max (.const 0)
      (.max (.max (.param 0) (.param 1)) (.max (.param 0) (.param 1)))))) :=
  .piForm (natural_typed enabled) (.sort _) (step_inner_type enabled) (.sort _) (.sorts _ _)

theorem method_body_typed {number : CTm Tower.Head n}
    (typed : CTyped (church enabled) Γ number natural) :
    CTyped (church enabled) (.snoc Γ (.app motive number)) (successor (.var 0))
      (.app motive (successor (number.rename wk))) := by
  have previous : CTyped (church enabled) (.snoc Γ (.app motive number))
      (number.rename wk) natural := typed.weaken
  have argument : CTyped (church enabled) (.snoc Γ (.app motive number)) (.var 0) natural :=
    .conv (.var 0) (motive_beta enabled previous) (.sort _)
  exact .conv (successor_typed enabled argument)
    (.symm (motive_beta enabled (successor_typed enabled previous))) (.sort _)

theorem step_inner_typed : CTyped (church enabled) (.snoc Γ natural)
    (.lam (.app motive (.var 0)) (successor (.var 0)))
    (.pi (.app motive (.var 0)) (.app motive (successor (.var 1)))) := by
  apply CDerivable.lamIntro (motive_applied enabled (.var 0)) (.sort _)
    (step_inner_type enabled) (.sort _)
  exact method_body_typed enabled (.var 0)

theorem step_typed : CTyped (church enabled) Γ step stepType :=
  .lamIntro (natural_typed enabled) (.sort _) (step_type enabled) (.sort _) (step_inner_typed enabled)

theorem step_apply_equal {number value : CTm Tower.Head n}
    (numberTyped : CTyped (church enabled) Γ number natural)
    (valueTyped : CTyped (church enabled) Γ value (.app motive number)) :
    CEqual (church enabled) Γ (.app (.app step number) value) (successor value)
      (.app motive (successor number)) := by
  have first := CDerivable.betaPi (step_type enabled) (.sort _)
    (step_inner_typed enabled) numberTyped
  change CEqual (church enabled) Γ (.app step number)
    (.lam (.app motive number) (successor (.var 0)))
    (.pi (.app motive number) (.app motive (successor (number.rename wk)))) at first
  have applied := CDerivable.appCong first (.refl valueTyped)
  have opened : CTm.inst0 value (.app motive (successor (number.rename wk))) =
      .app motive (successor number) := by
    change CTm.app motive (successor (CTm.inst0 value (number.rename wk))) = _
    rw [CTm.inst0_rename_wk]
  rw [opened] at applied
  have formed := (step_inner_type enabled (Γ := Γ)).instantiate numberTyped
  have second := CDerivable.betaPi formed (.sort _) (method_body_typed enabled numberTyped) valueTyped
  change CEqual (church enabled) Γ
    (.app (.lam (.app motive number) (successor (.var 0))) value) (successor value)
      (CTm.inst0 value (.app motive (successor (number.rename wk)))) at second
  rw [opened] at second
  exact .trans applied second

def recursorEntry : (scope : Nat) → Tower.Tm scope
  | 0 => .pi natTm (.head (.sort (.max (.param 0) (.param 1))))
  | 1 => natZeroCaseType
  | 2 => natSuccCaseType
  | _ + 3 => natTm

def recursorContext : Tower.Ctx 4 := Normalization.ofEntries recursorEntry 4
def recursorResult : Tower.Tm 4 := .app (.var 3) (.var 0)

theorem recursor_typed : CTyped (church enabled) Γ (.const natEliminateName)
    (liftTm (TelescopeAbstraction.closeType recursorContext recursorResult)).liftClosed := by
  exact .const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel)
    (Evidence.declaration_3 enabled) (.sort _)

def methodType (family : CTm Tower.Head n) : CTm Tower.Head n :=
  .pi natural (.pi (.app (family.rename wk) (.var 0))
    (.app ((family.rename wk).rename wk) (successor (.var 1))))

def arguments (family base method number : CTm Tower.Head n) : CSub Tower.Head 4 n :=
  Fin.cases number (Fin.cases method (Fin.cases base (fun _ => family)))

theorem arguments_typed {family base method number : CTm Tower.Head n}
    (familyTyped : CTyped (church enabled) Γ family (.pi natural motiveSort))
    (baseTyped : CTyped (church enabled) Γ base (.app family zero))
    (methodTyped : CTyped (church enabled) Γ method (methodType family))
    (numberTyped : CTyped (church enabled) Γ number natural) :
    CSubstMor (church enabled) (liftCtx recursorContext) Γ
      (arguments family base method number) := by
  intro index
  fin_cases index
  · exact numberTyped
  · exact methodTyped
  · exact baseTyped
  · exact familyTyped

def eliminate (family base method number : CTm Tower.Head n) : CTm Tower.Head n :=
  .app (.app (.app (.app (.const natEliminateName) family) base) method) number

theorem eliminate_typed {family base method number : CTm Tower.Head n}
    (familyTyped : CTyped (church enabled) Γ family (.pi natural motiveSort))
    (baseTyped : CTyped (church enabled) Γ base (.app family zero))
    (methodTyped : CTyped (church enabled) Γ method (methodType family))
    (numberTyped : CTyped (church enabled) Γ number natural) :
    CTyped (church enabled) Γ (eliminate family base method number) (.app family number) := by
  have applied := applyAlong_typed (Q := church enabled) recursorEntry 4 recursorResult
    (arguments family base method number)
    (arguments_typed enabled familyTyped baseTyped methodTyped numberTyped) (recursor_typed enabled)
  exact applied

def add (first second : CTm Tower.Head n) : CTm Tower.Head n :=
  eliminate motive second step first

theorem add_substitute {scope : Nat} (σ : CSub Tower.Head n scope) (first second : CTm Tower.Head n) :
    (add first second).subst σ = add (first.subst σ) (second.subst σ) := rfl

theorem add_rename {scope : Nat} (ρ : Ren n scope) (first second : CTm Tower.Head n) :
    (add first second).rename ρ = add (first.rename ρ) (second.rename ρ) := rfl

theorem add_typed {first second : CTm Tower.Head n}
    (firstTyped : CTyped (church enabled) Γ first natural)
    (secondTyped : CTyped (church enabled) Γ second natural) :
    CTyped (church enabled) Γ (add first second) natural := by
  have base : CTyped (church enabled) Γ second (.app motive zero) :=
    .conv secondTyped (.symm (motive_beta enabled (zero_typed enabled))) (.sort _)
  have recursive := eliminate_typed enabled (motive_typed enabled) base
    (step_typed enabled) firstTyped
  exact .conv recursive (motive_beta enabled firstTyped) (.sort _)

theorem add_erases (first second : CTm Tower.Head n) :
    (add first second).erase = Programs.add first.erase second.erase := rfl

def addFunction : CTm Tower.Head 0 := .lam natural (.lam natural (add (.var 1) (.var 0)))
def addFunctionType : CTm Tower.Head 0 := .pi natural (.pi natural natural)

theorem addFunction_typed : CTyped (church enabled) .nil addFunction addFunctionType := by
  have innerType {scope : Nat} {context : CCtx Tower.Head scope} :
      CTyped (church enabled) context (.pi natural natural)
        (.head (.sort (.max (.const 0) (.const 0)))) :=
    .piForm (natural_typed enabled) (.sort _) (natural_typed enabled) (.sort _) (.sorts _ _)
  have outerType : CTyped (church enabled) .nil addFunctionType
      (.head (.sort (.max (.const 0) (.max (.const 0) (.const 0))))) :=
    .piForm (natural_typed enabled) (.sort _) innerType (.sort _) (.sorts _ _)
  exact .lamIntro (natural_typed enabled) (.sort _) outerType (.sort _)
    (.lamIntro (natural_typed enabled) (.sort _) innerType (.sort _)
      (add_typed enabled (.var 1) (.var 0)))

theorem addFunction_erases : addFunction.erase =
    TelescopeAbstraction.closeTerm (.snoc (.snoc .nil natTm) natTm)
      (Programs.add (.var 1) (.var 0)) := rfl

/-- The maintained bidirectional annotator receives the actual unannotated
function and its independently specified dependent-function type. -/
def producedAddFunction (selection : ComputationProfiles.Selection) : CTm Tower.Head 0 :=
  (elaborate (church selection).constantType Knowledge.empty (some addFunctionType) none
    (TelescopeAbstraction.closeTerm (.snoc (.snoc .nil natTm) natTm)
      (Programs.add (.var 1) (.var 0)))).1

theorem producedAddFunction_exact : producedAddFunction enabled = addFunction := by
  dsimp only [producedAddFunction]
  rw [constantType_eq enabled]
  clear! enabled
  decide +kernel

/-- Output shape alone grants no type; this consumes the independent derivation. -/
theorem producedAddFunction_typed :
    CTyped (church enabled) .nil (producedAddFunction enabled) addFunctionType := by
  rw [producedAddFunction_exact]
  exact addFunction_typed enabled

def zeroRow : Row := ⟨0, by decide +kernel⟩
def successorRow : Row := ⟨1, by decide +kernel⟩

theorem add_zero {second : CTm Tower.Head n} (permitted : enabled zeroRow = true)
    (typed : CTyped (church enabled) Γ second natural) :
    CEqual (church enabled) Γ (add zero second) second natural := by
  have base : CTyped (church enabled) Γ second (.app motive zero) :=
    .conv typed (.symm (motive_beta enabled (zero_typed enabled))) (.sort _)
  have allArguments := arguments_typed enabled (motive_typed enabled) base
    (step_typed enabled) (zero_typed enabled)
  let assignment : CSub Tower.Head 3 n := fun index => arguments motive second step zero index.succ
  have selected : CSubstMor (church enabled) (context zeroRow) Γ assignment := by
    intro index
    fin_cases index
    · exact allArguments (1 : Fin 4)
    · exact allArguments (2 : Fin 4)
    · exact allArguments (3 : Fin 4)
  have equation := instantiated_equal enabled zeroRow permitted selected
  change CEqual (church enabled) Γ (add zero second) second (.app motive zero) at equation
  exact .convEq equation (motive_beta enabled (zero_typed enabled)) (.sort _)

theorem add_successor {first second : CTm Tower.Head n} (permitted : enabled successorRow = true)
    (firstTyped : CTyped (church enabled) Γ first natural)
    (secondTyped : CTyped (church enabled) Γ second natural) :
    CEqual (church enabled) Γ (add (successor first) second) (successor (add first second)) natural := by
  have base : CTyped (church enabled) Γ second (.app motive zero) :=
    .conv secondTyped (.symm (motive_beta enabled (zero_typed enabled))) (.sort _)
  have allArguments := arguments_typed enabled (motive_typed enabled) base
    (step_typed enabled) firstTyped
  have equation := instantiated_equal enabled successorRow permitted allArguments
  change CEqual (church enabled) Γ (add (successor first) second)
    (.app (.app step first) (add first second)) (.app motive (successor first)) at equation
  have recursive := eliminate_typed enabled (motive_typed enabled) base
    (step_typed enabled) firstTyped
  exact .convEq (.trans equation (step_apply_equal enabled firstTyped recursive))
    (motive_beta enabled (successor_typed enabled firstTyped)) (.sort _)

theorem inactive_no_root {left right : CTm Tower.Head n} :
    ¬ (church (fun _ => false)).computation.step left right := by
  intro root
  exact inactive_raw_no_root (erase_root (fun _ => false) root)

/-- A typed closed function does not authorize any of the disabled iota roots. -/
theorem typed_without_iota :
    CTyped (church (fun _ => false)) .nil addFunction addFunctionType ∧
      ∀ {scope : Nat} {left right : CTm Tower.Head scope},
        ¬ (church (fun _ => false)).computation.step left right :=
  ⟨addFunction_typed _, inactive_no_root⟩

/-- Former separation applies to the actual typed function's dependent
product type, even though every declared iota citation is disabled. -/
theorem inactive_function_type_not_universe (level : Tower.Head) :
    ¬ CTypeEq (church (fun _ => false)) .nil addFunctionType (.head level) :=
  inactive_pi_not_head .nil

theorem inactive_function_beta : CEqual (church (fun _ => false)) .nil
    (.app addFunction zero) (.lam natural (add zero (.var 0))) (.pi natural natural) :=
  inactive_reduction_equal .nil (Relation.ReflTransGen.single (.betaPi _ _ _))
    (.appElim (addFunction_typed _) (zero_typed _))

def inactiveZeroCitation : (ComputationProfiles.decoder (fun _ => false)).Code 0 :=
  .declared ⟨0, [step.erase, zero.erase, motive.erase]⟩

theorem inactive_zero_citation_refused :
    ((ComputationProfiles.decoder (fun _ => false)).decode inactiveZeroCitation).isNone = true := by
  decide +kernel

theorem full_zero_citation_accepted :
    (ComputationProfiles.decoder (fun _ => true)).decode inactiveZeroCitation =
      some ((add zero zero).erase, zero.erase) := by decide +kernel

def otherMotive : CTm Tower.Head n := .lam motiveSort natural

theorem otherMotive_typed : CTyped (church enabled) Γ otherMotive (.pi motiveSort motiveSort) :=
  .lamIntro (universe_typed enabled) (.sort _)
    (.piForm (universe_typed enabled) (.sort _) (universe_typed enabled) (.sort _) (.sorts _ _))
    (.sort _) (natural_in_universe enabled)

/-- Both annotations have real typings, but erasure forgets their different domains. -/
theorem domain_erasure_distinction :
    (motive : CTm Tower.Head n).erase = otherMotive.erase ∧
      (motive : CTm Tower.Head n) ≠ otherMotive ∧
      (CTm.pi natural motiveSort : CTm Tower.Head n) ≠ .pi motiveSort motiveSort := by
  refine ⟨rfl, ?_, ?_⟩ <;> intro impossible <;> cases impossible

theorem one_plus_zero : CEqual (church ComputationProfiles.naturalOnly) .nil
    (add (successor zero) zero) (successor zero) natural :=
  .trans (add_successor _ (by decide +kernel) (zero_typed _) (zero_typed _))
    (successor_equal _ (add_zero _ (by decide +kernel) (zero_typed _)))

def verdicts : List (String × Bool) :=
  [("annotated addition erases to the actual closed M1 function",
      decide (addFunction.erase = TelescopeAbstraction.closeTerm (.snoc (.snoc .nil natTm) natTm)
        (Programs.add (.var 1) (.var 0)))),
   ("the bidirectional annotator reconstructs the independently typed addition",
      decide (producedAddFunction ComputationProfiles.naturalOnly = addFunction)),
   ("erasing a motive loses its actual domain",
      decide ((motive : CTm Tower.Head 0).erase = otherMotive.erase) &&
        decide ((motive : CTm Tower.Head 0) ≠ otherMotive)),
   ("opaque declaration baseline reconstructs the actual annotated function",
      decide (producedAddFunction (fun _ => false) = addFunction)),
   ("opaque declaration baseline refuses the actual natural zero root",
      ((ComputationProfiles.decoder (fun _ => false)).decode inactiveZeroCitation).isNone),
   ("enabling roots accepts the same natural zero citation",
      (ComputationProfiles.decoder (fun _ => true)).decode inactiveZeroCitation ==
        some ((add zero zero).erase, zero.erase))]

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

end Programs.Annotated.Functions
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
