import Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Codes

open Mettapedia.OSLF.Framework

/-!
# Source-law preservation for actual generated code classifiers

Original constructor-code substitutions commute with the display encoding.
Native code law instances and native one-hole constructor contexts therefore
inherit the checked classifier preservation theorem. The selected equation
and directed systems retain separate certificates and separate relations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Source

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.UniversalAlgebra
open ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Generation

variable {language : LanguageDef}

def Code.substitute (substitution : Nat → Code language) : Code language → Code language
  | .variableCode index => substitution index
  | .constructor index arguments => .constructor index (fun position => (arguments position).substitute substitution)

theorem code_display_substitute (substitution : Nat → Code language) (code : Code language) :
    (code.substitute substitution).display = code.display.subst (fun index => (substitution index).display) := by
  induction code with
  | variableCode index => rfl
  | constructor index arguments ih =>
      change Term.op (operation language index) (fun position => ((arguments position).substitute substitution).display) =
        Term.op (operation language index) (fun position => (arguments position).display.subst
          (fun variableIndex => (substitution variableIndex).display))
      congr 1
      funext position
      exact ih position

theorem Kinded.substitute {profile : Profile language} {source target : Nat → HSort}
    {code : Code language} {sort : HSort} (formed : Kinded profile source code sort)
    (substitution : Nat → Code language)
    (typed : ∀ index, Kinded profile target (substitution index) (source index)) :
    Kinded profile target (code.substitute substitution) sort := by
  induction formed with
  | variableCode index => exact typed index
  | constructor index arguments children ih => exact .constructor index _ ih

theorem Carries.substitute {source target : Nat → TypeExpr}
    {code : Code language} {carrier : TypeExpr} (formed : Carries source code carrier)
    (substitution : Nat → Code language)
    (typed : ∀ index, Carries target (substitution index) (source index)) :
    Carries target (code.substitute substitution) carrier := by
  induction formed with
  | variableCode index => exact typed index
  | constructor index arguments children ih => exact .constructor index _ ih

inductive NativeLawStep (profile : Profile language)
    (system : EquationSystem (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.signature language))
    (valuation : Nat → HSort) : Code language → Code language → Prop where
  | law (left right : Code language) (member : (left.display, right.display) ∈ system)
      (source : Nat → HSort) (substitution : Nat → Code language)
      (typed : ∀ index, Kinded profile valuation (substitution index) (source index)) :
      NativeLawStep profile system valuation (left.substitute substitution) (right.substitute substitution)
  | context (index : Fin language.terms.length)
      (arguments : Fin (declaration language index).params.length → Code language)
      (position : Fin (declaration language index).params.length) {first second : Code language}
      (step : NativeLawStep profile system valuation first second) :
      NativeLawStep profile system valuation
        (.constructor index (Function.update arguments position first))
        (.constructor index (Function.update arguments position second))

theorem native_law_step_display {profile : Profile language}
    {system : EquationSystem (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.signature language)}
    {valuation : Nat → HSort} {first second : Code language}
    (step : NativeLawStep profile system valuation first second) :
    Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.TypedDisplayStep profile system valuation first.display second.display := by
  induction step with
  | law left right member source substitution typed =>
      rw [code_display_substitute, code_display_substitute]
      exact .equation _ member source (fun index => (substitution index).display)
        (fun index => (kinded_display_exact _ _ _ _).mp (typed index))
  | context index arguments position step ih =>
      have component : ∀ replacement : Code language,
          (Code.constructor index (Function.update arguments position replacement)).display =
            .op (operation language index)
              (Function.update (fun other => (arguments other).display) position replacement.display) := by
        intro replacement
        change Term.op (operation language index) _ = Term.op (operation language index) _
        congr 1
        funext other
        change (Function.update arguments position replacement other).display =
          Function.update (fun argument : Fin (declaration language index).params.length =>
            (arguments argument).display) position replacement.display other
        exact Function.apply_update (fun (_ : Fin (declaration language index).params.length)
          (value : Code language) => value.display) arguments position replacement other
      rw [component, component]
      exact Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.TypedDisplayStep.context (operation language index)
        (fun other => (arguments other).display) position ih

theorem native_law_step_universe {profile : Profile language}
    {system : EquationSystem (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.signature language)}
    (stable : Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Stable system profile) {valuation : Nat → HSort}
    {first second : Code language} (step : NativeLawStep profile system valuation first second) (sort : HSort) :
    first ∈ Universe profile valuation sort ↔ second ∈ Universe profile valuation sort := by
  change Kinded _ _ _ _ ↔ Kinded _ _ _ _
  rw [kinded_display_exact, kinded_display_exact]
  exact Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.typed_display_step_formation stable (native_law_step_display step) sort

def selectedEquations (generated : Generated) :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.compileLaws generated.snapshot.language
    (selectedEquationLaws generated.snapshot.language generated.languageFragment.operational)

def selectedDirectedLaws (generated : Generated) :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.compileLaws generated.snapshot.language
    (selectedRewriteLaws generated.snapshot.language generated.languageFragment.operational)

theorem generated_joint_admission_stable (snapshot : Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.Snapshot)
    (fragment : LanguageFragment) (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex (selectedSnapshot snapshot fragment).language)
    (accepted : jointAdmission (generate snapshot fragment logic vertex) = some true) :
    Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Stable (selectedEquations (generate snapshot fragment logic vertex)).system vertex.2 ∧
      Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Stable (selectedDirectedLaws (generate snapshot fragment logic vertex)).system vertex.2 := by
  have certified := (joint_admission_exact _).mp accepted
  constructor
  · have equationCheck : Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled?
        (selectedEquations (generate snapshot fragment logic vertex)) vertex.2 = some true := certified.1
    have result := (Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled?_some_iff _ _ _).mp equationCheck
    exact (Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStable_iff _ _).mp result.2
  · have directedCheck : Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled?
        (selectedDirectedLaws (generate snapshot fragment logic vertex)) vertex.2 = some true := certified.2
    have result := (Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled?_some_iff _ _ _).mp directedCheck
    exact (Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStable_iff _ _).mp result.2

theorem generated_native_equation_universe
    (snapshot : Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.Snapshot)
    (fragment : LanguageFragment) (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex (selectedSnapshot snapshot fragment).language)
    (accepted : jointAdmission (generate snapshot fragment logic vertex) = some true)
    (valuation : Nat → HSort) (first second : Code (selectedSnapshot snapshot fragment).language)
    (equivalent : Convertibility vertex.2 valuation
      (selectedEquations (generate snapshot fragment logic vertex)).system first second) (sort : HSort) :
    first ∈ Universe vertex.2 valuation sort ↔ second ∈ Universe vertex.2 valuation sort :=
  universe_equation_invariant (generated_joint_admission_stable _ _ _ _ accepted).1 _ _ equivalent sort

/-- A selected directed law preserves the classifier on its genuinely typed
instances and constructor contexts; it is not an operational equation. -/
theorem generated_native_directed_universe
    (snapshot : Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.Snapshot)
    (fragment : LanguageFragment) (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex (selectedSnapshot snapshot fragment).language)
    (accepted : jointAdmission (generate snapshot fragment logic vertex) = some true)
    (valuation : Nat → HSort) (first second : Code (selectedSnapshot snapshot fragment).language)
    (step : NativeLawStep vertex.2
      (selectedDirectedLaws (generate snapshot fragment logic vertex)).system valuation first second) (sort : HSort) :
    first ∈ Universe vertex.2 valuation sort ↔ second ∈ Universe vertex.2 valuation sort :=
  native_law_step_universe (generated_joint_admission_stable _ _ _ _ accepted).2 step sort

end Mettapedia.OSLF.NativeTypes.SortProfiles.Source
