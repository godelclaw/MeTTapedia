import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance
import MettaHyperonFull.Proofs.TypeInferenceFreshening
import MettaHyperonFull.Proofs.CaptureAvoidingFreshening
import Mettapedia.Languages.MeTTa.HE.EquationScope
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.BindingComposition
open Mettapedia.Languages.MeTTa.HE.MatchSizeTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-!
# Exact type-presentation conformance

The exact spec type boundary describes fresh inference scopes relationally.
This file connects the repaired runtime's deterministic finite freshener to
that relation.  The correspondence is structural: translation commutes with
whole-type renaming, and the runtime's growing avoid list is exactly the spec
type-variable list at every fold step.

The recursive `getTypes` characterization is built above these lemmas; no
negative consumer should use the exact relation before both directions of
that characterization are available.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationExactConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance

/-! ## Structural translation laws -/

mutual

/-- Translation commutes with whole-type variable renaming. -/
theorem encodeModelAtom_renameTypeVars
    (rename : String → String) (atom : Atom) :
    encodeModelAtom (renameTypeVars rename atom) =
      Metta.Minimal.renameAllVars rename (encodeModelAtom atom) := by
  cases atom with
  | symbol name =>
      simp [renameTypeVars, encodeModelAtom,
        Metta.Minimal.renameAllVars]
  | var name =>
      simp [renameTypeVars, encodeModelAtom,
        Metta.Minimal.renameAllVars]
  | grounded value =>
      simp [renameTypeVars, encodeModelAtom,
        Metta.Minimal.renameAllVars]
  | expression atoms =>
      simp only [renameTypeVars, encodeModelAtom,
        Metta.Minimal.renameAllVars]
      exact congrArg Metta.Atom.expr
        (encodeModelAtoms_renameTypeVars rename atoms)
termination_by 2 * sizeOf atom

/-- List companion of `encodeModelAtom_renameTypeVars`. -/
theorem encodeModelAtoms_renameTypeVars
    (rename : String → String) (atoms : List Atom) :
    encodeModelAtoms (atoms.map (renameTypeVars rename)) =
      (encodeModelAtoms atoms).map
        (Metta.Minimal.renameAllVars rename) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      exact congrArg₂ List.cons
        (encodeModelAtom_renameTypeVars rename atom)
        (encodeModelAtoms_renameTypeVars rename atoms)
termination_by 2 * sizeOf atoms + 1
decreasing_by
  all_goals simp_wf
  all_goals omega

end

/-! ## Runtime freshening realizes the relational alpha scopes -/

/-- One deterministic repaired-runtime candidate is a lawful spec
alpha-variant satisfying the same finite avoidance contract. -/
theorem freshenTypeCandidate_alphaVariant
    (avoid : List String) (position : Nat) (source : Atom) :
    TypeCandidateAlphaVariantRel avoid source
      (decodeModelAtom
        (Metta.Minimal.freshenTypeCandidate avoid position
          (encodeModelAtom source))) := by
  refine ⟨Metta.Minimal.captureAvoidingName avoid position,
    Metta.Minimal.captureAvoidingName_injective avoid position, ?_, ?_⟩
  · simp only [Metta.Minimal.freshenTypeCandidate]
    rw [← encodeModelAtom_renameTypeVars,
      decodeModelAtom_encodeModelAtom]
  · intro name _
    exact Metta.Minimal.captureAvoidingName_not_mem avoid position name

/-- The deterministic argument freshening fold realizes the spec growing
avoid-set relation at every starting position. -/
theorem freshenArgumentTypes_alphaVariants
    (avoid : List String) (position : Nat) : ∀ sources : List Atom,
    ArgumentAlphaVariantsRel avoid sources
      (decodeModelAtoms
        (Metta.Minimal.freshenArgumentTypes avoid position
          (encodeModelAtoms sources))) := by
  intro sources
  induction sources generalizing avoid position with
  | nil => exact ArgumentAlphaVariantsRel.nil avoid
  | cons source sources ih =>
      let freshLea := Metta.Minimal.freshenTypeCandidate avoid position
        (encodeModelAtom source)
      let target := decodeModelAtom freshLea
      have hvariant : TypeCandidateAlphaVariantRel avoid source target := by
        simpa [freshLea, target] using
          freshenTypeCandidate_alphaVariant avoid position source
      have htarget : target = renameTypeVars
          (Metta.Minimal.captureAvoidingName avoid position) source := by
        dsimp [target, freshLea]
        simp only [Metta.Minimal.freshenTypeCandidate]
        rw [← encodeModelAtom_renameTypeVars,
          decodeModelAtom_encodeModelAtom]
      have hfreshImage : freshLea = encodeModelAtom target := by
        rw [htarget]
        simpa [freshLea, Metta.Minimal.freshenTypeCandidate] using
          (encodeModelAtom_renameTypeVars
            (Metta.Minimal.captureAvoidingName avoid position) source).symm
      have hvars : freshLea.vars = TypeSubst.typeVars target := by
        rw [hfreshImage, encodeModelAtom_vars_eq_typeVars]
      rw [Metta.Minimal.freshenArgumentTypes.eq_def]
      simp only [encodeModelAtoms, decodeModelAtoms]
      apply ArgumentAlphaVariantsRel.cons hvariant
      simpa [freshLea, target, hvars] using
        ih (avoid ++ TypeSubst.typeVars target) (position + 1)

/-- Pointwise deterministic operator freshening realizes the spec operator
candidate relation. -/
theorem freshenOperatorTypes_alphaVariants
    (avoid : List String) (position : Nat) : ∀ sources : List Atom,
    OperatorAlphaVariantsRel avoid sources
      (decodeModelAtoms
        ((encodeModelAtoms sources).map
          (Metta.Minimal.freshenTypeCandidate avoid position))) := by
  intro sources
  induction sources with
  | nil => exact OperatorAlphaVariantsRel.nil
  | cons source sources ih =>
      simp only [encodeModelAtoms, List.map_cons, decodeModelAtoms]
      exact OperatorAlphaVariantsRel.cons
        (freshenTypeCandidate_alphaVariant avoid position source) ih

/-! ## Fresh-scope separation -/

mutual

/-- Whole-type renaming maps the native variable-occurrence list
pointwise. -/
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

/-- Function candidates freshened against the complete argument-variable
set are structurally disjoint from those arguments.  This is the exact scope
premise consumed by application-candidate completeness. -/
theorem OperatorAlphaVariantsRel.disjoint_from_arguments
    {avoid : List String} {rawOperators freshOperators actualTypes : List Atom}
    (variants : OperatorAlphaVariantsRel
      (avoid ++ TypeSubst.typeVarsList actualTypes)
      rawOperators freshOperators) :
    ∀ operatorType ∈ freshOperators,
      VarsDisjoint operatorType (.expression actualTypes) := by
  induction variants with
  | nil => simp
  | @cons source target sources targets headVariant tailVariants ih =>
      intro operatorType member
      rcases List.mem_cons.mp member with rfl | tailMember
      · intro name operatorMember argumentMember
        rw [encodeModelAtom_vars_eq_typeVars] at operatorMember
        rw [encodeModelAtom_vars_eq_typeVars] at argumentMember
        exact TypeCandidateAlphaVariantRel.target_vars_fresh
          headVariant name operatorMember
          (List.mem_append_right avoid argumentMember)
      · exact ih operatorType tailMember

end Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationExactConformance


/-! ## Optional equation-freshener realization

The following adapter concerns LeaTTa's particular allocation algorithm.
Independent HE equation semantics and its retained freshener do not depend on
this realization.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationExactConformance.EquationFreshening

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge LeaTTaTypeConformance
open Spec.Type.Presentation Spec.Type.Presentation.Exact
open Spec.Type.RuntimeRefinement
open Spec.Eval.Steps

private theorem mapped_lookup (names : List String) (rename : String → String)
    (name : String) (member : name ∈ names) :
    Metta.Subst.lookup (names.map fun candidate =>
      (candidate, Metta.Atom.var (rename candidate))) name =
        some (.var (rename name)) := by
  induction names with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · simp [Metta.Subst.lookup]
    · by_cases equal : name = head
      · subst name
        simp [Metta.Subst.lookup]
      · simpa [Metta.Subst.lookup, equal] using ih member

private theorem mapped_apply (names : List String) (rename : String → String)
    (atom : Metta.Atom) (covers : ∀ name ∈ atom.vars, name ∈ names) :
    Metta.Subst.apply (names.map fun name => (name, Metta.Atom.var (rename name))) atom =
      Metta.Minimal.renameAllVars rename atom := by
  cases atom with
  | sym name => simp [Metta.Subst.apply, Metta.Minimal.renameAllVars]
  | gnd value => simp [Metta.Subst.apply, Metta.Minimal.renameAllVars]
  | var name =>
      have member : name ∈ names := covers name (by simp [Metta.Atom.vars])
      simp [Metta.Subst.apply, Metta.Minimal.renameAllVars,
        mapped_lookup names rename name member]
  | expr atoms =>
      simp only [Metta.Subst.apply, Metta.Minimal.renameAllVars]
      congr 1
      apply List.map_congr_left
      intro atom member
      apply mapped_apply names rename atom
      intro name occurrence
      apply covers name
      simp only [Metta.Atom.vars, List.mem_flatten]
      exact ⟨atom.vars, List.mem_map.mpr ⟨atom, member, rfl⟩, occurrence⟩
termination_by atom.size
decreasing_by
  subst_vars
  have bound : atom.size ≤ (atoms.map Metta.Atom.size).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨atom, member, rfl⟩)
  simp only [Metta.Atom.size]
  omega

/-- The ordinary counter freshener is one total simultaneous renaming. -/
theorem legacy_is_total_renaming (counter : Nat) (lhs rhs : Metta.Atom) :
    Metta.Minimal.freshenRule counter lhs rhs =
      (Metta.Minimal.renameAllVars (fun name => name ++ "#" ++ toString counter) lhs,
        Metta.Minimal.renameAllVars (fun name => name ++ "#" ++ toString counter) rhs) := by
  have left := mapped_apply (lhs.vars ++ rhs.vars)
    (fun name => name ++ "#" ++ toString counter) lhs
    (fun name member => List.mem_append_left _ member)
  have right := mapped_apply (lhs.vars ++ rhs.vars)
    (fun name => name ++ "#" ++ toString counter) rhs
    (fun name member => List.mem_append_right _ member)
  unfold Metta.Minimal.freshenRule
  split
  · rename_i empty
    simp only [empty, List.map_nil, Metta.Subst.apply_nil] at left right
    exact congrArg₂ Prod.mk left right
  · exact congrArg₂ Prod.mk left right

/-- The name function selected by the runtime's collision test. -/
def ruleRename (avoid : List String) (counter : Nat) (lhs rhs : Metta.Atom) : String → String :=
  if ∃ name ∈ (Metta.Minimal.freshenRule counter lhs rhs).1.vars ++
      (Metta.Minimal.freshenRule counter lhs rhs).2.vars, name ∈ avoid
  then Metta.Minimal.captureAvoidingName avoid counter
  else fun name => name ++ "#" ++ toString counter

theorem ruleRename_injective (avoid : List String) (counter : Nat) (lhs rhs : Metta.Atom) :
    Function.Injective (ruleRename avoid counter lhs rhs) := by
  unfold ruleRename
  split
  · exact Metta.Minimal.captureAvoidingName_injective avoid counter
  · intro left right equal
    have suffixEqual : left ++ ("#" ++ toString counter) =
        right ++ ("#" ++ toString counter) := by
      simpa [String.append_assoc] using equal
    exact (String.append_left_inj ("#" ++ toString counter)).mp suffixEqual

/-- The actual freshener, including its counter, realizes the selected map. -/
theorem runtime_freshening (avoid : List String) (counter : Nat) (lhs rhs : Metta.Atom) :
    Metta.Minimal.freshenRuleAvoiding counter avoid lhs rhs =
      ((Metta.Minimal.renameAllVars (ruleRename avoid counter lhs rhs) lhs,
        Metta.Minimal.renameAllVars (ruleRename avoid counter lhs rhs) rhs), counter + 1) := by
  unfold Metta.Minimal.freshenRuleAvoiding ruleRename
  dsimp only
  split
  · rfl
  · rw [legacy_is_total_renaming]



/-- Read the actual runtime's freshened HE equation back into HE syntax. -/
def freshRule (avoid : List String) (counter : Nat) (lhs rhs : Atom) : Atom × Atom :=
  let native := (Metta.Minimal.freshenRuleAvoiding counter avoid
    (encodeModelAtom lhs) (encodeModelAtom rhs)).1
  (decodeModelAtom native.1, decodeModelAtom native.2)

theorem freshRule_eq_renamed (avoid : List String) (counter : Nat) (lhs rhs : Atom) :
    freshRule avoid counter lhs rhs =
      (renameTypeVars (ruleRename avoid counter (encodeModelAtom lhs) (encodeModelAtom rhs)) lhs,
        renameTypeVars (ruleRename avoid counter (encodeModelAtom lhs) (encodeModelAtom rhs)) rhs) := by
  simp only [freshRule, runtime_freshening]
  rw [← encodeModelAtom_renameTypeVars, ← encodeModelAtom_renameTypeVars,
    decodeModelAtom_encodeModelAtom, decodeModelAtom_encodeModelAtom]

/-- Readback preserves the actual native freshened rule exactly. -/
theorem freshRule_translation (avoid : List String) (counter : Nat) (lhs rhs : Atom) :
    (encodeModelAtom (freshRule avoid counter lhs rhs).1,
      encodeModelAtom (freshRule avoid counter lhs rhs).2) =
      (Metta.Minimal.freshenRuleAvoiding counter avoid (encodeModelAtom lhs) (encodeModelAtom rhs)).1 := by
  rw [freshRule_eq_renamed, runtime_freshening]
  simp only [encodeModelAtom_renameTypeVars]

/-- Neither side of the returned equation contains an avoided variable. -/
theorem freshRule_variables_avoid (avoid : List String) (counter : Nat) (lhs rhs : Atom) :
    ∀ name ∈ (encodeModelAtom (freshRule avoid counter lhs rhs).1).vars ++
        (encodeModelAtom (freshRule avoid counter lhs rhs).2).vars,
      name ∉ avoid := by
  have nativeFresh := Metta.Minimal.freshenRuleAvoiding_vars_fresh counter avoid
    (encodeModelAtom lhs) (encodeModelAtom rhs)
  have translation := freshRule_translation avoid counter lhs rhs
  have left := congrArg Prod.fst translation
  have right := congrArg Prod.snd translation
  simp only at left right
  intro name member
  rw [left, right] at member
  exact nativeFresh name member

/-- Any finite avoidance list containing the complete caller scope suffices.
Additional native or retained names do not weaken hygiene. -/
theorem freshRule_alphaVariant_of_covers (live : List Atom) (query lhs rhs : Atom)
    (incoming : Bindings) (counter : Nat) (avoid : List String)
    (covers : ∀ name, QueryVisibleName live query incoming name → name ∈ avoid) :
    AlphaVariantRel live query incoming lhs rhs
      (freshRule avoid counter lhs rhs).1
      (freshRule avoid counter lhs rhs).2 := by
  let rename := ruleRename avoid counter (encodeModelAtom lhs) (encodeModelAtom rhs)
  rw [freshRule_eq_renamed]
  refine ⟨rename, ruleRename_injective _ _ _ _,
    Mettapedia.Languages.MeTTa.HE.EquationFreshening.rename_alpha _ _,
    Mettapedia.Languages.MeTTa.HE.EquationFreshening.rename_alpha _ _, ?_⟩
  intro name occurs visible
  have renamedOccurs : rename name ∈
      (encodeModelAtom (renameTypeVars rename lhs)).vars ++
        (encodeModelAtom (renameTypeVars rename rhs)).vars := by
    rw [encodeModelAtom_vars_eq_typeVars, encodeModelAtom_vars_eq_typeVars,
      Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars,
      Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars]
    rcases occurs with left | right
    · apply List.mem_append_left
      apply List.mem_map_of_mem
      rw [← encodeModelAtom_vars_eq_typeVars]
      exact Spec.Match.ModelTheory.atomOccurs_iff_mem_translated_vars.mp left
    · apply List.mem_append_right
      apply List.mem_map_of_mem
      rw [← encodeModelAtom_vars_eq_typeVars]
      exact Spec.Match.ModelTheory.atomOccurs_iff_mem_translated_vars.mp right
  have fresh := Metta.Minimal.freshenRuleAvoiding_vars_fresh counter avoid
    (encodeModelAtom lhs) (encodeModelAtom rhs)
  rw [runtime_freshening] at fresh
  simp only [encodeModelAtom_renameTypeVars] at renamedOccurs
  exact fresh (rename name) renamedOccurs (covers (rename name) visible)

/-- Complete caller scope and the actual freshener construct a hygienic
alpha variant of both equation sides, at arbitrary nesting depth. -/
theorem freshRule_alphaVariant (live : List Atom) (query lhs rhs : Atom)
    (incoming : Bindings) (counter : Nat) :
    AlphaVariantRel live query incoming lhs rhs
      (freshRule (EquationScope.visibleNames live query incoming) counter lhs rhs).1
      (freshRule (EquationScope.visibleNames live query incoming) counter lhs rhs).2 :=
  freshRule_alphaVariant_of_covers live query lhs rhs incoming counter _
    (fun name visible => (EquationScope.mem_visibleNames_iff live query incoming name).mpr visible)




end Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationExactConformance.EquationFreshening
