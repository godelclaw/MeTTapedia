import Mettapedia.OSLF.NativeTypes.SortProfiles.Derived

open Mettapedia.OSLF.Framework

/-!
# The universal fixed-output profile diagnostic rejects original QuoteDrop

This is a boundary theorem for the old universal formation diagnostic.  A fixed
result slot cannot both equal every possible sort of an external variable and
remain fixed.  It does not refute the finite displayed-occurrence consistency
construction, whose constraints and equation-conversion role are separate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.ProfileBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.UniversalAlgebra
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler Mettapedia.OSLF.NativeTypes.SortProfiles.Derived

def opposite : HSort → HSort
  | .star => .box
  | .box => .star

theorem opposite_ne (sort : HSort) : opposite sort ≠ sort := by
  cases sort <;> decide

theorem fixed_head_variable_never_stable {S : Signature.{0}}
    (profile : Profile S) (operation : S.Operation)
    (arguments : Fin (S.arity operation) → Term S) (index : Nat) :
    ¬ StableEquation profile (.op operation arguments, .var index) := by
  intro stable
  have variableFormed : Formed profile
      (fun _ => opposite (output profile operation)) (.var index)
      (opposite (output profile operation)) := .variableTerm index
  have headFormed := (stable.2 _ _).mpr variableFormed
  have uniqueOutput {sort : HSort}
      (formed : Formed profile (fun _ => opposite (output profile operation))
        (.op operation arguments) sort) : sort = output profile operation := by
    cases formed
    rfl
  exact opposite_ne (output profile operation) (uniqueOutput headFormed)

def quoteDropLaw : Law := equationLaw rhoCalc.equations[0] 0

theorem encode_application_head {language : LanguageDef} {names : List String}
    {label : String} {arguments : List Pattern} {term : Term (signature language)}
    (encoded : encode language names (.apply label arguments) = some term) :
    ∃ operation children, term = .op operation children := by
  change (encodeList language names arguments).bind
    (assemble? language (.constructor label arguments.length)) = some term at encoded
  obtain ⟨children, _, assembled⟩ := Option.bind_eq_some_iff.mp encoded
  unfold assemble? at assembled
  obtain ⟨operation, _, assembled⟩ := Option.bind_eq_some_iff.mp assembled
  split at assembled
  · exact ⟨operation, _, (Option.some.inj assembled).symm⟩
  · contradiction

theorem original_quoteDrop_never_universally_stable
    (profile : Profile (signature rhoCalc)) :
    ¬ SourceEquationStable rhoCalc quoteDropLaw profile := by
  intro stable
  obtain ⟨valuation, sort, left, right, leftEncoded, rightEncoded, leftFormed, rightFormed⟩ := stable.1
  have rightShape : right = .var 0 := by
    have rightRead : encode rhoCalc (quoteDropLaw.context.map Prod.fst) quoteDropLaw.right =
        some (.var 0) := by cbv
    exact Option.some.inj (rightEncoded.symm.trans rightRead)
  obtain ⟨operation, children, leftShape⟩ := encode_application_head leftEncoded
  apply fixed_head_variable_never_stable profile operation children 0
  rw [← leftShape, ← rightShape]
  exact ⟨⟨valuation, sort, leftFormed, rightFormed⟩,
    stable.2 left right leftEncoded rightEncoded⟩

theorem original_equation_diagnostic_never_accepts
    (profile : Profile (signature rhoCalc)) :
    checkStableLanguage? rhoCalc profile ≠ some true := by
  intro checked
  have stable := (original_stable_equation_check_exact rhoCalc profile).mp checked
  exact original_quoteDrop_never_universally_stable profile (stable.2 rhoCalc.equations[0] 0
    (by simp [rhoCalc]))

theorem original_universal_center_empty : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.center rhoCalc = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro vertex member
  exact original_equation_diagnostic_never_accepts vertex.2
    (Finset.mem_filter.mp member).2

#print axioms fixed_head_variable_never_stable
#print axioms original_equation_diagnostic_never_accepts
#print axioms original_universal_center_empty

end Mettapedia.OSLF.NativeTypes.Instances.Rho.ProfileBoundary
