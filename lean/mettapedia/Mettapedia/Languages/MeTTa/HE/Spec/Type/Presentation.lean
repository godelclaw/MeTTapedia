import Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement

/-!
# Presentation-preserving spec type substitutions

Solution theory is sufficient for positive type evidence, but it cannot
determine the syntax emitted by application-result inference.  In particular,
an unconstrained return variable remains that variable; it is not replaced by
an arbitrary model value.  This module therefore gives the runtime-refinement
lane an executable-independent finite substitution presentation.

The relations below are type-specific and declarative.  They mention neither
the LeaTTa matcher nor the HE executable matcher.  `%Undefined%` is a wildcard
recursively, while `Atom` is a wildcard only at the outer type-match boundary.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type

/-! ## Finite substitutions -/

/-- A finite, ordered type-variable substitution.  The first entry for a key
is authoritative. -/
abbrev TypeSubst := List (String × Atom)

namespace TypeSubst

mutual

/-- Type variables occurring in an atom, with multiplicity. -/
def typeVars : Atom → List String
  | .var name => [name]
  | .expression atoms => typeVarsList atoms
  | _ => []

/-- List companion of `typeVars`. -/
def typeVarsList : List Atom → List String
  | [] => []
  | atom :: atoms => typeVars atom ++ typeVarsList atoms

end

/-- First-hit lookup in a finite type substitution. -/
def lookup : TypeSubst → String → Option Atom
  | [], _ => none
  | (key, value) :: rest, name =>
      if name = key then some value else lookup rest name

/-- Variables assigned by a finite substitution. -/
def keys (substitution : TypeSubst) : List String :=
  substitution.map Prod.fst

/-- Homomorphic, one-pass application.  Normal substitutions contain no
assigned variable in a stored value, so one pass is their total application. -/
def apply (substitution : TypeSubst) : Atom → Atom
  | .symbol name => .symbol name
  | .var name => (substitution.lookup name).getD (.var name)
  | .grounded value => .grounded value
  | .expression atoms => .expression (atoms.map (apply substitution))

/-- Remove every entry for one key. -/
def erase (substitution : TypeSubst) (name : String) : TypeSubst :=
  substitution.filter (fun entry => entry.1 != name)

/-- Apply one new assignment to the values of an older substitution. -/
def applyAssignment (name : String) (value : Atom) : Atom → Atom :=
  TypeSubst.apply [(name, value)]

/-- Extend a substitution and compose the new assignment through all older
values.  This preserves the syntactic spelling of every still-unassigned
variable. -/
def bind (substitution : TypeSubst) (name : String) (value : Atom) :
    TypeSubst :=
  let resolvedValue := substitution.apply value
  (name, resolvedValue) ::
    (substitution.erase name).map fun entry =>
      (entry.1, applyAssignment name resolvedValue entry.2)

/-- Idempotent finite-substitution presentation: keys are unique and no
stored value contains a variable assigned by the same substitution. -/
def Normal (substitution : TypeSubst) : Prop :=
  substitution.keys.Nodup ∧
    ∀ name value, (name, value) ∈ substitution →
      ∀ candidate ∈ typeVars value, candidate ∉ substitution.keys

@[simp] theorem lookup_empty (name : String) :
    lookup [] name = none := rfl

mutual

@[simp] theorem apply_empty (atom : Atom) :
    apply [] atom = atom := by
  cases atom with
  | symbol | var | grounded => simp [apply, lookup, Option.getD]
  | expression atoms =>
      simp only [apply]
      exact congrArg Atom.expression (apply_empty_list atoms)
termination_by 2 * sizeOf atom

@[simp] theorem apply_empty_list (atoms : List Atom) :
    atoms.map (apply []) = atoms := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      exact congrArg₂ List.cons (apply_empty atom) (apply_empty_list atoms)
termination_by 2 * sizeOf atoms + 1
decreasing_by
  all_goals simp_wf
  all_goals omega

end

theorem normal_empty : Normal [] := by
  simp [Normal, keys]

end TypeSubst

/-! ## Presentation-preserving reduced-type matching -/

mutual

/-- Ordinary matching after the incoming substitution has already been
applied.  This layer has no wildcard constructor: a `%Undefined%` produced
by substitution is an ordinary symbol at every depth.  Distinct variables
orient left-to-right and compounds recurse in source order. -/
inductive AppliedReducedTypeMatchRel :
    TypeSubst → Atom → Atom → TypeSubst → Prop where
  | identical (substitution : TypeSubst) (atom : Atom) :
      AppliedReducedTypeMatchRel substitution atom atom substitution
  | bindLeft {substitution : TypeSubst} {name : String} {right : Atom} :
      name ∉ TypeSubst.typeVars right →
      AppliedReducedTypeMatchRel substitution (.var name) right
        (substitution.bind name right)
  | bindRight {substitution : TypeSubst} {left : Atom} {name : String} :
      (∀ other, left ≠ .var other) →
      name ∉ TypeSubst.typeVars left →
      AppliedReducedTypeMatchRel substitution left (.var name)
        (substitution.bind name left)
  | expression {substitution output : TypeSubst}
      {left right : List Atom} :
      AppliedReducedTypeListMatchRel substitution left right output →
      AppliedReducedTypeMatchRel substitution
        (.expression left) (.expression right) output

/-- Resolve one ordinary (non-wildcard) child through the substitution
accumulated by earlier siblings, then take one applied unification step. -/
inductive AppliedTypePresentationMatchRel :
    TypeSubst → Atom → Atom → TypeSubst → Prop where
  | ordinary {substitution output : TypeSubst}
      {left right resolvedLeft resolvedRight : Atom} :
      substitution.apply left = resolvedLeft →
      substitution.apply right = resolvedRight →
      AppliedReducedTypeMatchRel substitution resolvedLeft resolvedRight output →
      AppliedTypePresentationMatchRel substitution left right output

/-- Pointwise companion for already-applied ordinary atoms.  In particular,
this relation deliberately has no recursive `%Undefined%` wildcard. -/
inductive AppliedReducedTypeListMatchRel :
    TypeSubst → List Atom → List Atom → TypeSubst → Prop where
  | nil (substitution : TypeSubst) :
      AppliedReducedTypeListMatchRel substitution [] [] substitution
  | cons {substitution next output : TypeSubst}
      {left right : Atom} {lefts rights : List Atom} :
      AppliedTypePresentationMatchRel substitution left right next →
      AppliedReducedTypeListMatchRel next lefts rights output →
      AppliedReducedTypeListMatchRel substitution
        (left :: lefts) (right :: rights) output

end

/-- The ordinary leaf lane applies only when the two raw atoms are not both
expressions.  Raw expression pairs must recurse before substitution so that
literal wildcard provenance is preserved child by child. -/
def ReducedTypeLeafShape : Atom → Atom → Prop
  | .expression _, .expression _ => False
  | _, _ => True

mutual

/-- Literal recursive `%Undefined%` is a wildcard before substitution.
Raw expression pairs recurse before substitution.  Every other shape resolves
through the current presentation and takes one ordinary declarative unifier
step.  Consequently a variable presented as `%Undefined%` by earlier
constraints never becomes a wildcard, including below an expression. -/
inductive ReducedTypePresentationMatchRel :
    TypeSubst → Atom → Atom → TypeSubst → Prop where
  | undefinedLeft (substitution : TypeSubst) (right : Atom) :
      ReducedTypePresentationMatchRel substitution
        Atom.undefinedType right substitution
  | undefinedRight (substitution : TypeSubst) (left : Atom) :
      ReducedTypePresentationMatchRel substitution
        left Atom.undefinedType substitution
  | expression {substitution output : TypeSubst}
      {left right : List Atom} :
      ReducedTypePresentationListMatchRel substitution left right output →
      ReducedTypePresentationMatchRel substitution
        (.expression left) (.expression right) output
  | ordinary {substitution output : TypeSubst}
      {left right resolvedLeft resolvedRight : Atom} :
      left ≠ Atom.undefinedType →
      right ≠ Atom.undefinedType →
      ReducedTypeLeafShape left right →
      substitution.apply left = resolvedLeft →
      substitution.apply right = resolvedRight →
      AppliedReducedTypeMatchRel substitution resolvedLeft resolvedRight output →
      ReducedTypePresentationMatchRel substitution left right output

/-- Left-to-right list companion, threading the finite substitution. -/
inductive ReducedTypePresentationListMatchRel :
    TypeSubst → List Atom → List Atom → TypeSubst → Prop where
  | nil (substitution : TypeSubst) :
      ReducedTypePresentationListMatchRel substitution [] [] substitution
  | cons {substitution next output : TypeSubst}
      {left right : Atom} {lefts rights : List Atom} :
      ReducedTypePresentationMatchRel substitution left right next →
      ReducedTypePresentationListMatchRel next lefts rights output →
      ReducedTypePresentationListMatchRel substitution
        (left :: lefts) (right :: rights) output

end

/-- Away from literal recursive wildcards, a reduced presentation derivation
exposes its ordinary post-substitution matching step. -/
theorem ReducedTypePresentationMatchRel.ordinary_of_nonUndefined
    {substitution output : TypeSubst} {left right : Atom}
    (leftNotUndefined : left ≠ Atom.undefinedType)
    (rightNotUndefined : right ≠ Atom.undefinedType)
    (leafShape : ReducedTypeLeafShape left right)
    (derivation : ReducedTypePresentationMatchRel
      substitution left right output) :
    ∃ resolvedLeft resolvedRight,
      substitution.apply left = resolvedLeft ∧
        substitution.apply right = resolvedRight ∧
        AppliedReducedTypeMatchRel
          substitution resolvedLeft resolvedRight output := by
  cases derivation with
  | undefinedLeft => exact (leftNotUndefined rfl).elim
  | undefinedRight => exact (rightNotUndefined rfl).elim
  | expression children => exact leafShape.elim
  | ordinary _ _ _ leftApply rightApply applied =>
      exact ⟨_, _, leftApply, rightApply, applied⟩

/-- Published top-level gradual wildcards plus the presentation-preserving R2
reduced matcher. -/
inductive CorePlusR2TypePresentationMatchRel :
    TypeSubst → Atom → Atom → TypeSubst → Prop where
  | undefinedLeft (substitution : TypeSubst) (right : Atom) :
      CorePlusR2TypePresentationMatchRel substitution
        Atom.undefinedType right substitution
  | undefinedRight (substitution : TypeSubst) (left : Atom) :
      CorePlusR2TypePresentationMatchRel substitution
        left Atom.undefinedType substitution
  | atomLeft (substitution : TypeSubst) (right : Atom) :
      CorePlusR2TypePresentationMatchRel substitution
        Atom.atomType right substitution
  | atomRight (substitution : TypeSubst) (left : Atom) :
      CorePlusR2TypePresentationMatchRel substitution
        left Atom.atomType substitution
  | reduced {substitution output : TypeSubst} {left right : Atom} :
      left ≠ Atom.undefinedType →
      right ≠ Atom.undefinedType →
      left ≠ Atom.atomType →
      right ≠ Atom.atomType →
      ReducedTypePresentationMatchRel substitution left right output →
      CorePlusR2TypePresentationMatchRel substitution left right output

/-- Away from the four published top-level wildcards, a type-presentation
match is exactly one reduced-type presentation match. -/
theorem CorePlusR2TypePresentationMatchRel.reduced_of_nonWildcard
    {substitution output : TypeSubst} {left right : Atom}
    (hLeftUndefined : left ≠ Atom.undefinedType)
    (hRightUndefined : right ≠ Atom.undefinedType)
    (hLeftAtom : left ≠ Atom.atomType)
    (hRightAtom : right ≠ Atom.atomType)
    (hmatch : CorePlusR2TypePresentationMatchRel
      substitution left right output) :
    ReducedTypePresentationMatchRel substitution left right output := by
  cases hmatch with
  | undefinedLeft => exact (hLeftUndefined rfl).elim
  | undefinedRight => exact (hRightUndefined rfl).elim
  | atomLeft => exact (hLeftAtom rfl).elim
  | atomRight => exact (hRightAtom rfl).elim
  | reduced _ _ _ _ hreduced => exact hreduced

/-- Two distinct ordinary symbols have no applied reduced-type match. -/
theorem AppliedReducedTypeMatchRel.no_distinct_symbols
    {substitution output : TypeSubst} {left right : String}
    (hDistinct : left ≠ right) :
    ¬AppliedReducedTypeMatchRel substitution
      (.symbol left) (.symbol right) output := by
  intro hmatch
  cases hmatch with
  | identical => exact hDistinct rfl

/-! ## Lawful presented candidates -/

/-- One exact runtime candidate: `rawTerm` records the declared provenance,
`substitution` records the type fold, and `observed` is its definite syntactic
presentation. -/
structure RuntimeTypePackage where
  observed : Atom
  rawTerm : Atom
  substitution : TypeSubst
  presentation : observed = substitution.apply rawTerm

/-- A published candidate has an empty private substitution. -/
def RuntimeTypePackage.published (type : Atom) : RuntimeTypePackage :=
  ⟨type, type, [], (TypeSubst.apply_empty type).symm⟩

/-- Later consumers match only the definite observed presentation.  The
package-local substitution is provenance and cannot capture the outer fold. -/
def PackagedTypePresentationMatchRel
    (incoming : TypeSubst) (expected : Atom)
    (actual : RuntimeTypePackage) (output : TypeSubst) : Prop :=
  CorePlusR2TypePresentationMatchRel incoming expected actual.observed output

/-! ## Positive and negative boundary examples -/

private def tToA : TypeSubst := [("t", .symbol "A")]
private def tToB : TypeSubst := [("t", .symbol "B")]

/-- Positive: matching `$t` against `A` records the definite substitution. -/
theorem variable_matches_symbol_presentation :
    CorePlusR2TypePresentationMatchRel [] (.var "t") (.symbol "A")
      tToA := by
  apply CorePlusR2TypePresentationMatchRel.reduced
  · simp [Atom.undefinedType]
  · simp [Atom.undefinedType]
  · simp [Atom.atomType]
  · simp [Atom.atomType]
  apply ReducedTypePresentationMatchRel.ordinary
      (resolvedLeft := .var "t") (resolvedRight := .symbol "A")
  · simp [Atom.undefinedType]
  · simp [Atom.undefinedType]
  · simp [ReducedTypeLeafShape]
  · exact TypeSubst.apply_empty (.var "t")
  · exact TypeSubst.apply_empty (.symbol "A")
  simpa [tToA, TypeSubst.bind, TypeSubst.apply, TypeSubst.erase,
    TypeSubst.lookup] using
    (AppliedReducedTypeMatchRel.bindLeft
      (substitution := []) (name := "t") (right := .symbol "A")
      (by simp [TypeSubst.typeVars]))

/-- Negative: after `$t` is fixed to `B`, `A` cannot match the same spelling. -/
theorem fixed_variable_rejects_distinct_symbol :
    ¬∃ output,
      CorePlusR2TypePresentationMatchRel tToB
        (.symbol "A") (.var "t") output := by
  rintro ⟨output, hmatch⟩
  have hreduced := hmatch.reduced_of_nonWildcard
    (by simp [Atom.undefinedType]) (by simp [Atom.undefinedType])
    (by simp [Atom.atomType]) (by simp [Atom.atomType])
  obtain ⟨resolvedLeft, resolvedRight, hleft, hright, happlied⟩ :=
    hreduced.ordinary_of_nonUndefined
      (by simp [Atom.undefinedType]) (by simp [Atom.undefinedType])
      (by simp [ReducedTypeLeafShape])
  simp [tToB, TypeSubst.apply, TypeSubst.lookup,
    Option.getD] at hleft hright
  rw [← hleft, ← hright] at happlied
  exact AppliedReducedTypeMatchRel.no_distinct_symbols
    (by decide) happlied

/-- An unconstrained raw return variable has exactly its syntactic variable
presentation under the empty substitution. -/
theorem unresolved_variable_presentation_is_rigid :
    (RuntimeTypePackage.published (.var "t")).observed = .var "t" := rfl

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation

/-! ## Shared substitution and determined template readout -/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra
open RuntimeRefinement

/-- The type presentation uses the shared atom variable-occurrence algebra. -/
theorem TypeSubst.typeVars_eq_vars (atom : Atom) :
    TypeSubst.typeVars atom = vars atom := by
  induction atom using Atom.rec
      (motive_2 := fun atoms => TypeSubst.typeVarsList atoms = vars.varsList atoms) with
  | symbol name => rfl
  | var name => rfl
  | grounded value => rfl
  | expression atoms ih => exact ih
  | nil => rfl
  | cons atom atoms head tail =>
    simp only [TypeSubst.typeVarsList, vars.varsList, head, tail]

/-- A total source valuation is the shared simultaneous substitution with all
variable entries supplied. -/
theorem applyTypeValuation_eq_subst (valuation : String → Atom) (atom : Atom) :
    applyTypeValuation valuation atom = subst (some ∘ valuation) atom := by
  induction atom using Atom.rec
      (motive_2 := fun atoms => atoms.map (applyTypeValuation valuation) =
        subst.substList (some ∘ valuation) atoms) with
  | symbol name => simp only [applyTypeValuation, subst]
  | var name => simp only [applyTypeValuation, subst, Function.comp_apply, Option.getD_some]
  | grounded value => simp only [applyTypeValuation, subst]
  | expression atoms ih => simpa only [applyTypeValuation, subst] using congrArg Atom.expression ih
  | nil => rfl
  | cons atom atoms head tail =>
    simp only [List.map_cons, subst.substList, head, tail]

/-- An observed first-order pattern determines precisely its variable values. -/
theorem applyTypeValuation_eq_iff_on_typeVars (left right : String → Atom) (atom : Atom) :
    applyTypeValuation left atom = applyTypeValuation right atom ↔
      ∀ name ∈ TypeSubst.typeVars atom, left name = right name := by
  simp only [applyTypeValuation_eq_subst, TypeSubst.typeVars_eq_vars,
    subst_eq_iff_on_vars, subst, Function.comp_apply, Option.getD_some]

/-- Equal solutions of a pattern give equal readouts for every template whose
variables are covered by that pattern. -/
theorem applyTypeValuation_template_eq_of_pattern_eq
    (left right : String → Atom) (pattern template : Atom)
    (covered : ∀ name ∈ TypeSubst.typeVars template, name ∈ TypeSubst.typeVars pattern)
    (same : applyTypeValuation left pattern = applyTypeValuation right pattern) :
    applyTypeValuation left template = applyTypeValuation right template := by
  apply (applyTypeValuation_eq_iff_on_typeVars left right template).mpr
  intro name member
  exact (applyTypeValuation_eq_iff_on_typeVars left right pattern).mp same name
    (covered name member)


end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ScopeObservation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement

/-! ## Structural renaming helpers -/

mutual

/-- Whole-type renaming depends only on the names occurring in the atom. -/
theorem renameTypeVars_congr_on_typeVars
    {left right : String → String} (atom : Atom)
    (agrees : ∀ name, name ∈ TypeSubst.typeVars atom →
      left name = right name) :
    renameTypeVars left atom = renameTypeVars right atom := by
  cases atom with
  | symbol name => simp [renameTypeVars]
  | var name =>
      simp only [renameTypeVars, Atom.var.injEq]
      exact agrees name (by simp [TypeSubst.typeVars])
  | grounded value => simp [renameTypeVars]
  | expression atoms =>
      simp only [renameTypeVars, Atom.expression.injEq]
      apply renameTypeVarsList_congr_on_typeVars
      intro name member
      exact agrees name (by simpa [TypeSubst.typeVars] using member)

/-- List companion of `renameTypeVars_congr_on_typeVars`. -/
theorem renameTypeVarsList_congr_on_typeVars
    {left right : String → String} (atoms : List Atom)
    (agrees : ∀ name, name ∈ TypeSubst.typeVarsList atoms →
      left name = right name) :
    atoms.map (renameTypeVars left) =
      atoms.map (renameTypeVars right) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · apply renameTypeVars_congr_on_typeVars atom
        intro name member
        exact agrees name (by
          simp only [TypeSubst.typeVarsList, List.mem_append]
          exact Or.inl member)
      · apply renameTypeVarsList_congr_on_typeVars atoms
        intro name member
        exact agrees name (by
          simp only [TypeSubst.typeVarsList, List.mem_append]
          exact Or.inr member)

end

mutual

/-- Successive whole-type renamings compose. -/
theorem renameTypeVars_comp
    (outer inner : String → String) (atom : Atom) :
    renameTypeVars outer (renameTypeVars inner atom) =
      renameTypeVars (outer ∘ inner) atom := by
  cases atom with
  | symbol name => simp [renameTypeVars]
  | var name => simp [renameTypeVars, Function.comp_apply]
  | grounded value => simp [renameTypeVars]
  | expression atoms =>
      simp only [renameTypeVars, Atom.expression.injEq]
      exact renameTypeVarsList_comp outer inner atoms

/-- List companion of `renameTypeVars_comp`. -/
theorem renameTypeVarsList_comp
    (outer inner : String → String) (atoms : List Atom) :
    (atoms.map (renameTypeVars inner)).map
        (renameTypeVars outer) =
      atoms.map (renameTypeVars (outer ∘ inner)) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨renameTypeVars_comp outer inner atom,
        renameTypeVarsList_comp outer inner atoms⟩

end

/-- Renaming every type variable by the identity function is inert. -/
theorem renameTypeVars_id (atom : Atom) :
    renameTypeVars id atom = atom := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
    atoms.map (renameTypeVars id) = atoms) with
  | symbol name => simp [renameTypeVars]
  | var name => simp [renameTypeVars]
  | grounded value => simp [renameTypeVars]
  | expression atoms ih => simp [renameTypeVars, ih]
  | nil => rfl
  | cons atom atoms ihAtom ihAtoms => simp [ihAtom, ihAtoms]

mutual

/-- If a structural type renaming leaves an atom literally unchanged, it
fixes every variable name occurring in that atom. -/
theorem renameTypeVars_eq_self_fixed_on_typeVars
    (rename : String → String) (atom : Atom)
    (equation : renameTypeVars rename atom = atom) :
    ∀ name, name ∈ TypeSubst.typeVars atom → rename name = name := by
  cases atom with
  | symbol symbol => simp [TypeSubst.typeVars]
  | var variableName =>
      intro name member
      have nameEquation : name = variableName := by
        simpa [TypeSubst.typeVars] using member
      subst name
      simpa [renameTypeVars] using equation
  | grounded value => simp [TypeSubst.typeVars]
  | expression atoms =>
      have listEquation :
          atoms.map (renameTypeVars rename) = atoms := by
        simpa [renameTypeVars] using equation
      exact renameTypeVarsList_eq_self_fixed_on_typeVars
        rename atoms listEquation

/-- List companion of
`renameTypeVars_eq_self_fixed_on_typeVars`. -/
theorem renameTypeVarsList_eq_self_fixed_on_typeVars
    (rename : String → String) (atoms : List Atom)
    (equation : atoms.map (renameTypeVars rename) = atoms) :
    ∀ name,
      name ∈ TypeSubst.typeVarsList atoms → rename name = name := by
  cases atoms with
  | nil => simp [TypeSubst.typeVarsList]
  | cons atom atoms =>
      have parts := List.cons.inj equation
      intro name member
      rw [TypeSubst.typeVarsList, List.mem_append] at member
      rcases member with headMember | tailMember
      · exact renameTypeVars_eq_self_fixed_on_typeVars
          rename atom parts.1 name headMember
      · exact renameTypeVarsList_eq_self_fixed_on_typeVars
          rename atoms parts.2 name tailMember

end

mutual

/-- Whole-type renaming maps the finite variable support pointwise. -/
theorem typeVars_renameTypeVars
    (rename : String → String) (atom : Atom) :
    TypeSubst.typeVars (renameTypeVars rename atom) =
      (TypeSubst.typeVars atom).map rename := by
  cases atom with
  | symbol name => simp [renameTypeVars, TypeSubst.typeVars]
  | var name => simp [renameTypeVars, TypeSubst.typeVars]
  | grounded value => simp [renameTypeVars, TypeSubst.typeVars]
  | expression atoms =>
      simpa [renameTypeVars, TypeSubst.typeVars] using
        typeVarsList_renameTypeVars rename atoms

/-- List companion of `typeVars_renameTypeVars`. -/
theorem typeVarsList_renameTypeVars
    (rename : String → String) (atoms : List Atom) :
    TypeSubst.typeVarsList
        (atoms.map (renameTypeVars rename)) =
      (TypeSubst.typeVarsList atoms).map rename := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, TypeSubst.typeVarsList,
        List.map_append]
      exact congrArg₂ List.append
        (typeVars_renameTypeVars rename atom)
        (typeVarsList_renameTypeVars rename atoms)

end


end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ScopeObservation

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement

mutual

/-- Valuation after whole-type renaming is valuation conjugation on variable
names. -/
theorem applyTypeValuation_renameTypeVars
    (valuation : String → Atom) (rename : String → String) (atom : Atom) :
    applyTypeValuation valuation (renameTypeVars rename atom) =
      applyTypeValuation (valuation ∘ rename) atom := by
  cases atom with
  | symbol name => simp [renameTypeVars, applyTypeValuation]
  | var name => simp [renameTypeVars, applyTypeValuation]
  | grounded value => simp [renameTypeVars, applyTypeValuation]
  | expression atoms =>
      simp only [renameTypeVars, applyTypeValuation,
        Atom.expression.injEq]
      exact applyTypeValuationList_renameTypeVars
        valuation rename atoms

/-- List companion of `applyTypeValuation_renameTypeVars`. -/
theorem applyTypeValuationList_renameTypeVars
    (valuation : String → Atom) (rename : String → String)
    (atoms : List Atom) :
    (atoms.map (renameTypeVars rename)).map
        (applyTypeValuation valuation) =
      atoms.map (applyTypeValuation (valuation ∘ rename)) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨applyTypeValuation_renameTypeVars
          valuation rename atom,
        applyTypeValuationList_renameTypeVars
          valuation rename atoms⟩

end

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance

namespace Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement Spec.Type.Presentation.ScopeObservation

@[simp] theorem renameTypeVars_perm_inverse (permutation : Equiv.Perm String)
    (atom : Atom) :
    renameTypeVars permutation.symm (renameTypeVars permutation atom) = atom := by
  rw [renameTypeVars_comp]
  have inverse : (permutation.symm : String → String) ∘ permutation = id := by
    funext name
    simp
  rw [inverse, renameTypeVars_id]

theorem renameTypeVars_perm_injective (permutation : Equiv.Perm String) :
    Function.Injective (renameTypeVars permutation) := by
  intro left right same
  simpa only [renameTypeVars_perm_inverse] using
    congrArg (renameTypeVars permutation.symm) same


end Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open ScopeObservation Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation

namespace TypeSubst

/-- Simultaneously rename the keys and values of an ordered presentation. -/
def renameVars (rename : String → String) (substitution : TypeSubst) : TypeSubst :=
  substitution.map (fun entry => (rename entry.1, renameTypeVars rename entry.2))

@[simp] theorem renameVars_nil (rename : String → String) :
    renameVars rename [] = [] := rfl

@[simp] theorem renameVars_cons (rename : String → String) (key : String)
    (value : Atom) (rest : TypeSubst) :
    renameVars rename ((key, value) :: rest) =
      (rename key, renameTypeVars rename value) :: renameVars rename rest := rfl

theorem renameVars_comp (outer inner : String → String) (substitution : TypeSubst) :
    renameVars outer (renameVars inner substitution) =
      renameVars (outer ∘ inner) substitution := by
  simp [renameVars, List.map_map, Function.comp_def, renameTypeVars_comp]

@[simp] theorem renameVars_id (substitution : TypeSubst) :
    renameVars id substitution = substitution := by
  simp [renameVars, renameTypeVars_id]

@[simp] theorem renameVars_inverse (permutation : Equiv.Perm String)
    (substitution : TypeSubst) :
    renameVars permutation.symm (renameVars permutation substitution) = substitution := by
  rw [renameVars_comp]
  have inverse : (permutation.symm : String → String) ∘ permutation = id := by
    funext name
    simp
  rw [inverse, renameVars_id]

@[simp] theorem lookup_renameVars (permutation : Equiv.Perm String)
    (substitution : TypeSubst) (name : String) :
    (renameVars permutation substitution).lookup (permutation name) =
      (substitution.lookup name).map (renameTypeVars permutation) := by
  induction substitution with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨key, value⟩ := entry
      by_cases same : name = key <;>
        simp [renameVars_cons, lookup, permutation.injective.eq_iff, ih, same]

mutual

/-- Ordered substitution application commutes with one simultaneous variable
permutation. No choice of representative is changed independently. -/
theorem apply_renameVars (permutation : Equiv.Perm String)
    (substitution : TypeSubst) (atom : Atom) :
    (renameVars permutation substitution).apply (renameTypeVars permutation atom) =
      renameTypeVars permutation (substitution.apply atom) := by
  cases atom with
  | symbol name => simp [renameTypeVars, apply]
  | grounded value => simp [renameTypeVars, apply]
  | var name =>
      simp only [renameTypeVars, apply, lookup_renameVars]
      cases substitution.lookup name <;> simp [renameTypeVars]
  | expression atoms =>
      simp only [renameTypeVars, apply, Atom.expression.injEq]
      exact applyList_renameVars permutation substitution atoms

/-- List companion of `apply_renameVars`. -/
theorem applyList_renameVars (permutation : Equiv.Perm String)
    (substitution : TypeSubst) (atoms : List Atom) :
    (atoms.map (renameTypeVars permutation)).map
        (apply (renameVars permutation substitution)) =
      (atoms.map (apply substitution)).map (renameTypeVars permutation) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨apply_renameVars permutation substitution atom,
        applyList_renameVars permutation substitution atoms⟩

end

theorem erase_renameVars (permutation : Equiv.Perm String)
    (substitution : TypeSubst) (name : String) :
    (renameVars permutation substitution).erase (permutation name) =
      renameVars permutation (substitution.erase name) := by
  induction substitution with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨key, value⟩ := entry
      by_cases same : key = name
      · subst key
        simpa [erase, renameVars, List.filter_cons] using ih
      · simpa [erase, renameVars, List.filter_cons, same,
          permutation.injective.eq_iff] using congrArg
            (List.cons (permutation key, renameTypeVars permutation value)) ih

theorem applyAssignment_renameVars (permutation : Equiv.Perm String)
    (name : String) (value atom : Atom) :
    applyAssignment (permutation name) (renameTypeVars permutation value)
        (renameTypeVars permutation atom) =
      renameTypeVars permutation (applyAssignment name value atom) :=
  apply_renameVars permutation [(name, value)] atom

theorem bind_renameVars (permutation : Equiv.Perm String)
    (substitution : TypeSubst) (name : String) (value : Atom) :
    (renameVars permutation substitution).bind
        (permutation name) (renameTypeVars permutation value) =
      renameVars permutation (substitution.bind name value) := by
  simp only [bind, apply_renameVars, erase_renameVars, renameVars_cons]
  apply congrArg (List.cons _)
  simp only [renameVars, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro entry _
  exact congrArg (Prod.mk (permutation entry.1))
    (applyAssignment_renameVars permutation name (substitution.apply value) entry.2)

theorem keys_renameVars (rename : String → String) (substitution : TypeSubst) :
    (renameVars rename substitution).keys = substitution.keys.map rename := by
  simp [renameVars, keys, List.map_map, Function.comp_def]

/-- One bijective coordinate change preserves unique keys and the absence
of assigned variables from stored values. -/
theorem Normal.rename (permutation : Equiv.Perm String) {substitution : TypeSubst}
    (normal : substitution.Normal) : (substitution.renameVars permutation).Normal := by
  refine ⟨?_, ?_⟩
  · rw [keys_renameVars]
    exact normal.1.map permutation.injective
  · intro name value member candidate occurs assigned
    obtain ⟨⟨oldName, oldValue⟩, stored, pair⟩ := List.mem_map.mp member
    cases pair
    rw [typeVars_renameTypeVars] at occurs
    obtain ⟨oldCandidate, candidateOccurs, rfl⟩ := List.mem_map.mp occurs
    rw [keys_renameVars] at assigned
    obtain ⟨oldKey, keyMember, same⟩ := List.mem_map.mp assigned
    have sameKey := permutation.injective same
    subst oldKey
    exact normal.2 oldName oldValue stored oldCandidate candidateOccurs keyMember

end TypeSubst

/-- Every ordinary applied match transports its actual ordered output. -/
theorem AppliedReducedTypeMatchRel.rename
    (permutation : Equiv.Perm String) {incoming output : TypeSubst}
    {left right : Atom}
    (derivation : AppliedReducedTypeMatchRel incoming left right output) :
    AppliedReducedTypeMatchRel (incoming.renameVars permutation)
      (renameTypeVars permutation left) (renameTypeVars permutation right)
      (output.renameVars permutation) := by
  induction derivation using AppliedReducedTypeMatchRel.rec
      (motive_2 := fun incoming left right output _ =>
        AppliedTypePresentationMatchRel (incoming.renameVars permutation)
          (renameTypeVars permutation left) (renameTypeVars permutation right)
          (output.renameVars permutation))
      (motive_3 := fun incoming left right output _ =>
        AppliedReducedTypeListMatchRel (incoming.renameVars permutation)
          (left.map (renameTypeVars permutation))
          (right.map (renameTypeVars permutation)) (output.renameVars permutation)) with
  | identical substitution atom => exact .identical _ _
  | bindLeft absent =>
      rw [← TypeSubst.bind_renameVars]
      simp only [renameTypeVars]
      apply AppliedReducedTypeMatchRel.bindLeft
      simpa only [typeVars_renameTypeVars, List.mem_map,
        permutation.injective.eq_iff, exists_eq_right] using absent
  | bindRight nonvariable absent =>
      rw [← TypeSubst.bind_renameVars]
      simp only [renameTypeVars]
      apply AppliedReducedTypeMatchRel.bindRight
      · intro other same
        have original := congrArg (renameTypeVars permutation.symm) same
        simp only [renameTypeVars_perm_inverse, renameTypeVars] at original
        exact nonvariable _ original
      · simpa only [typeVars_renameTypeVars, List.mem_map,
          permutation.injective.eq_iff, exists_eq_right] using absent
  | expression _children ih =>
      simpa only [renameTypeVars] using AppliedReducedTypeMatchRel.expression ih
  | ordinary leftApply rightApply _applied ih =>
      exact .ordinary
        ((TypeSubst.apply_renameVars permutation _ _).trans
          (congrArg (renameTypeVars permutation) leftApply))
        ((TypeSubst.apply_renameVars permutation _ _).trans
          (congrArg (renameTypeVars permutation) rightApply)) ih
  | nil substitution => exact .nil _
  | cons _head _tail headIH tailIH => exact .cons headIH tailIH

/-- The ordinary post-substitution boundary is equivariant. -/
theorem AppliedTypePresentationMatchRel.rename
    (permutation : Equiv.Perm String) {incoming output : TypeSubst}
    {left right : Atom}
    (derivation : AppliedTypePresentationMatchRel incoming left right output) :
    AppliedTypePresentationMatchRel (incoming.renameVars permutation)
      (renameTypeVars permutation left) (renameTypeVars permutation right)
      (output.renameVars permutation) := by
  cases derivation with
  | ordinary leftApply rightApply applied =>
      exact .ordinary
        ((TypeSubst.apply_renameVars permutation _ _).trans
          (congrArg (renameTypeVars permutation) leftApply))
        ((TypeSubst.apply_renameVars permutation _ _).trans
          (congrArg (renameTypeVars permutation) rightApply))
        (AppliedReducedTypeMatchRel.rename permutation applied)


end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## Literal functionality of the ordinary ordered presentation -/

private theorem reflexive_family :
    (∀ {s o : TypeSubst} {l r : Atom}, AppliedReducedTypeMatchRel s l r o → l = r → o = s) ∧
    (∀ {s o : TypeSubst} {l r : Atom}, AppliedTypePresentationMatchRel s l r o → l = r → o = s) ∧
    (∀ {s o : TypeSubst} {l r : List Atom}, AppliedReducedTypeListMatchRel s l r o → l = r → o = s) := by
  let reduced := fun (s : TypeSubst) (l r : Atom) (o : TypeSubst)
    (_ : AppliedReducedTypeMatchRel s l r o) => l = r → o = s
  let applied := fun (s : TypeSubst) (l r : Atom) (o : TypeSubst)
    (_ : AppliedTypePresentationMatchRel s l r o) => l = r → o = s
  let list := fun (s : TypeSubst) (l r : List Atom) (o : TypeSubst)
    (_ : AppliedReducedTypeListMatchRel s l r o) => l = r → o = s
  have identical (s : TypeSubst) (a : Atom) : reduced s a a s (.identical s a) := by
    intro _
    rfl
  have bindLeft {s : TypeSubst} {name : String} {r : Atom}
      (absent : name ∉ TypeSubst.typeVars r) :
      reduced s (.var name) r (s.bind name r) (.bindLeft absent) := by
    intro same
    cases same
    exact (absent (by simp [TypeSubst.typeVars])).elim
  have bindRight {s : TypeSubst} {l : Atom} {name : String}
      (nonvariable : ∀ other, l ≠ .var other) (absent : name ∉ TypeSubst.typeVars l) :
      reduced s l (.var name) (s.bind name l) (.bindRight nonvariable absent) := by
    intro same
    exact (nonvariable name same).elim
  have expression {s o : TypeSubst} {l r : List Atom}
      (h : AppliedReducedTypeListMatchRel s l r o) (ih : list s l r o h) :
      reduced s (.expression l) (.expression r) o (.expression h) := by
    intro same
    exact ih (Atom.expression.inj same)
  have ordinary {s o : TypeSubst} {l r rl rr : Atom}
      (hl : s.apply l = rl) (hr : s.apply r = rr)
      (h : AppliedReducedTypeMatchRel s rl rr o) (ih : reduced s rl rr o h) :
      applied s l r o (.ordinary hl hr h) := by
    intro same
    exact ih (hl.symm.trans ((congrArg s.apply same).trans hr))
  have nil (s : TypeSubst) : list s [] [] s (.nil s) := by intro _; rfl
  have cons {s n o : TypeSubst} {l r : Atom} {ls rs : List Atom}
      (h : AppliedTypePresentationMatchRel s l r n)
      (t : AppliedReducedTypeListMatchRel n ls rs o)
      (ih : applied s l r n h) (it : list n ls rs o t) :
      list s (l :: ls) (r :: rs) o (.cons h t) := by
    intro same
    have eqs := List.cons.inj same
    have middle := ih eqs.1
    exact (it eqs.2).trans middle
  exact ⟨fun h => AppliedReducedTypeMatchRel.rec
      (motive_1 := reduced) (motive_2 := applied) (motive_3 := list)
      identical bindLeft bindRight expression ordinary nil cons h,
    fun h => AppliedTypePresentationMatchRel.rec
      (motive_1 := reduced) (motive_2 := applied) (motive_3 := list)
      identical bindLeft bindRight expression ordinary nil cons h,
    fun h => AppliedReducedTypeListMatchRel.rec
      (motive_1 := reduced) (motive_2 := applied) (motive_3 := list)
      identical bindLeft bindRight expression ordinary nil cons h⟩

/-- Matching an atom with itself does not change its incoming presentation. -/
theorem AppliedReducedTypeMatchRel.reflexive_output
    {incoming output : TypeSubst} {left right : Atom}
    (derivation : AppliedReducedTypeMatchRel incoming left right output)
    (same : left = right) : output = incoming := reflexive_family.1 derivation same

/-- Applying the same operand twice leaves the presentation unchanged. -/
theorem AppliedTypePresentationMatchRel.reflexive_output
    {incoming output : TypeSubst} {left right : Atom}
    (derivation : AppliedTypePresentationMatchRel incoming left right output)
    (same : left = right) : output = incoming := reflexive_family.2.1 derivation same

/-- A pointwise self-match leaves the complete ordered presentation unchanged. -/
theorem AppliedReducedTypeListMatchRel.reflexive_output
    {incoming output : TypeSubst} {left right : List Atom}
    (derivation : AppliedReducedTypeListMatchRel incoming left right output)
    (same : left = right) : output = incoming := reflexive_family.2.2 derivation same

private theorem functional_family :
    (∀ {s o : TypeSubst} {l r : Atom}, AppliedReducedTypeMatchRel s l r o →
      ∀ {other}, AppliedReducedTypeMatchRel s l r other → o = other) ∧
    (∀ {s o : TypeSubst} {l r : Atom}, AppliedTypePresentationMatchRel s l r o →
      ∀ {other}, AppliedTypePresentationMatchRel s l r other → o = other) ∧
    (∀ {s o : TypeSubst} {l r : List Atom}, AppliedReducedTypeListMatchRel s l r o →
      ∀ {other}, AppliedReducedTypeListMatchRel s l r other → o = other) := by
  let reduced := fun (s : TypeSubst) (l r : Atom) (o : TypeSubst)
    (_ : AppliedReducedTypeMatchRel s l r o) =>
      ∀ {other}, AppliedReducedTypeMatchRel s l r other → o = other
  let applied := fun (s : TypeSubst) (l r : Atom) (o : TypeSubst)
    (_ : AppliedTypePresentationMatchRel s l r o) =>
      ∀ {other}, AppliedTypePresentationMatchRel s l r other → o = other
  let list := fun (s : TypeSubst) (l r : List Atom) (o : TypeSubst)
    (_ : AppliedReducedTypeListMatchRel s l r o) =>
      ∀ {other}, AppliedReducedTypeListMatchRel s l r other → o = other
  have identical (s : TypeSubst) (a : Atom) : reduced s a a s (.identical s a) := by
    intro other two
    exact (two.reflexive_output rfl).symm
  have bindLeft {s : TypeSubst} {name : String} {r : Atom}
      (absent : name ∉ TypeSubst.typeVars r) :
      reduced s (.var name) r (s.bind name r) (.bindLeft absent) := by
    intro other two
    cases two with
    | identical => exact (absent (by simp [TypeSubst.typeVars])).elim
    | bindLeft => rfl
    | bindRight nonvariable _ => exact (nonvariable _ rfl).elim
  have bindRight {s : TypeSubst} {l : Atom} {name : String}
      (nonvariable : ∀ other, l ≠ .var other) (absent : name ∉ TypeSubst.typeVars l) :
      reduced s l (.var name) (s.bind name l) (.bindRight nonvariable absent) := by
    intro other two
    cases two with
    | identical => exact (nonvariable _ rfl).elim
    | bindLeft => exact (nonvariable _ rfl).elim
    | bindRight => rfl
  have expression {s o : TypeSubst} {l r : List Atom}
      (h : AppliedReducedTypeListMatchRel s l r o) (ih : list s l r o h) :
      reduced s (.expression l) (.expression r) o (.expression h) := by
    intro other two
    cases two with
    | identical => exact h.reflexive_output rfl
    | expression otherChildren => exact ih otherChildren
  have ordinary {s o : TypeSubst} {l r rl rr : Atom}
      (hl : s.apply l = rl) (hr : s.apply r = rr)
      (h : AppliedReducedTypeMatchRel s rl rr o) (ih : reduced s rl rr o h) :
      applied s l r o (.ordinary hl hr h) := by
    intro other two
    cases two with
    | ordinary otherLeft otherRight secondMatch =>
        have alignedLeft := hl.symm.trans otherLeft
        have alignedRight := hr.symm.trans otherRight
        cases alignedLeft
        cases alignedRight
        exact ih secondMatch
  have nil (s : TypeSubst) : list s [] [] s (.nil s) := by
    intro other two
    cases two
    rfl
  have cons {s n o : TypeSubst} {l r : Atom} {ls rs : List Atom}
      (h : AppliedTypePresentationMatchRel s l r n)
      (t : AppliedReducedTypeListMatchRel n ls rs o)
      (ih : applied s l r n h) (it : list n ls rs o t) :
      list s (l :: ls) (r :: rs) o (.cons h t) := by
    intro other two
    cases two with
    | cons otherHead otherTail =>
        have middle := ih otherHead
        cases middle
        exact it otherTail
  exact ⟨fun h => AppliedReducedTypeMatchRel.rec
      (motive_1 := reduced) (motive_2 := applied) (motive_3 := list)
      identical bindLeft bindRight expression ordinary nil cons h,
    fun h => AppliedTypePresentationMatchRel.rec
      (motive_1 := reduced) (motive_2 := applied) (motive_3 := list)
      identical bindLeft bindRight expression ordinary nil cons h,
    fun h => AppliedReducedTypeListMatchRel.rec
      (motive_1 := reduced) (motive_2 := applied) (motive_3 := list)
      identical bindLeft bindRight expression ordinary nil cons h⟩

/-- One ordinary reduced match has one literal output presentation. -/
theorem AppliedReducedTypeMatchRel.output_eq
    {incoming first second : TypeSubst} {left right : Atom}
    (one : AppliedReducedTypeMatchRel incoming left right first)
    (two : AppliedReducedTypeMatchRel incoming left right second) : first = second :=
  functional_family.1 one two

/-- One applied ordinary match has one literal output presentation. -/
theorem AppliedTypePresentationMatchRel.output_eq
    {incoming first second : TypeSubst} {left right : Atom}
    (one : AppliedTypePresentationMatchRel incoming left right first)
    (two : AppliedTypePresentationMatchRel incoming left right second) : first = second :=
  functional_family.2.1 one two

/-- A fixed ordered match list has one literal output presentation. -/
theorem AppliedReducedTypeListMatchRel.output_eq
    {incoming first second : TypeSubst} {left right : List Atom}
    (one : AppliedReducedTypeListMatchRel incoming left right first)
    (two : AppliedReducedTypeListMatchRel incoming left right second) : first = second :=
  functional_family.2.2 one two

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
