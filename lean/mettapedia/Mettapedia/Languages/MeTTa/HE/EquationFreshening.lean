import Mettapedia.Languages.MeTTa.HE.EquationScope
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationExactConformance
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ScopeObservation
import MettaHyperonFull.Proofs.CaptureAvoidingFreshening

/-!
# Equation freshening realizes independent alpha variation

Both branches of LeaTTa's actual rule freshener are simultaneous, injective
renamings. The collision branch avoids the complete finite caller scope;
the normal branch retains its existing spelling when that spelling is fresh.
The structural HE adapter realizes `AlphaVariantRel` without an atom-depth
or evaluation-fuel bound.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.EquationFreshening

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge LeaTTaTypeConformance LeaTTaTypePresentationExactConformance
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

mutual

/-- Whole-atom renaming realizes the independent structural judgment. -/
theorem rename_alpha (rename : String → String) (atom : Atom) :
    AlphaRenameAtomRel rename atom (renameTypeVars rename atom) := by
  cases atom with
  | symbol name => simpa [renameTypeVars] using AlphaRenameAtomRel.symbol (rename := rename) name
  | var name => simpa [renameTypeVars] using AlphaRenameAtomRel.variable (rename := rename) name
  | grounded value => simpa [renameTypeVars] using AlphaRenameAtomRel.grounded (rename := rename) value
  | expression atoms =>
    simpa [renameTypeVars] using AlphaRenameAtomRel.expression (rename_list_alpha rename atoms)
termination_by 2 * sizeOf atom

theorem rename_list_alpha (rename : String → String) (atoms : List Atom) :
    AlphaRenameAtomsRel rename atoms (atoms.map (renameTypeVars rename)) := by
  cases atoms with
  | nil => exact .nil
  | cons head tail => exact .cons (rename_alpha rename head) (rename_list_alpha rename tail)
termination_by 2 * sizeOf atoms + 1
decreasing_by
  all_goals simp_wf
  all_goals omega

end

/-- Read the actual runtime's freshened HE equation back into HE syntax. -/
def freshRule (avoid : List String) (counter : Nat) (lhs rhs : Atom) : Atom × Atom :=
  let native := (Metta.Minimal.freshenRuleAvoiding counter avoid
    (toLeaTTaAtom lhs) (toLeaTTaAtom rhs)).1
  (fromLeaTTaAtom native.1, fromLeaTTaAtom native.2)

theorem freshRule_eq_renamed (avoid : List String) (counter : Nat) (lhs rhs : Atom) :
    freshRule avoid counter lhs rhs =
      (renameTypeVars (ruleRename avoid counter (toLeaTTaAtom lhs) (toLeaTTaAtom rhs)) lhs,
        renameTypeVars (ruleRename avoid counter (toLeaTTaAtom lhs) (toLeaTTaAtom rhs)) rhs) := by
  simp only [freshRule, runtime_freshening]
  rw [← toLeaTTaAtom_renameTypeVars, ← toLeaTTaAtom_renameTypeVars,
    fromLeaTTaAtom_toLeaTTaAtom, fromLeaTTaAtom_toLeaTTaAtom]

/-- Readback preserves the actual native freshened rule exactly. -/
theorem freshRule_translation (avoid : List String) (counter : Nat) (lhs rhs : Atom) :
    (toLeaTTaAtom (freshRule avoid counter lhs rhs).1,
      toLeaTTaAtom (freshRule avoid counter lhs rhs).2) =
      (Metta.Minimal.freshenRuleAvoiding counter avoid (toLeaTTaAtom lhs) (toLeaTTaAtom rhs)).1 := by
  rw [freshRule_eq_renamed, runtime_freshening]
  simp only [toLeaTTaAtom_renameTypeVars]

/-- Neither side of the returned equation contains an avoided variable. -/
theorem freshRule_variables_avoid (avoid : List String) (counter : Nat) (lhs rhs : Atom) :
    ∀ name ∈ (toLeaTTaAtom (freshRule avoid counter lhs rhs).1).vars ++
        (toLeaTTaAtom (freshRule avoid counter lhs rhs).2).vars,
      name ∉ avoid := by
  have nativeFresh := Metta.Minimal.freshenRuleAvoiding_vars_fresh counter avoid
    (toLeaTTaAtom lhs) (toLeaTTaAtom rhs)
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
  let rename := ruleRename avoid counter (toLeaTTaAtom lhs) (toLeaTTaAtom rhs)
  rw [freshRule_eq_renamed]
  refine ⟨rename, ruleRename_injective _ _ _ _, rename_alpha _ _, rename_alpha _ _, ?_⟩
  intro name occurs visible
  have renamedOccurs : rename name ∈
      (toLeaTTaAtom (renameTypeVars rename lhs)).vars ++
        (toLeaTTaAtom (renameTypeVars rename rhs)).vars := by
    rw [toLeaTTaAtom_vars_eq_typeVars, toLeaTTaAtom_vars_eq_typeVars,
      Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars,
      Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars]
    rcases occurs with left | right
    · apply List.mem_append_left
      apply List.mem_map_of_mem
      rw [← toLeaTTaAtom_vars_eq_typeVars]
      exact Spec.Match.ModelTheory.atomOccurs_iff_mem_translated_vars.mp left
    · apply List.mem_append_right
      apply List.mem_map_of_mem
      rw [← toLeaTTaAtom_vars_eq_typeVars]
      exact Spec.Match.ModelTheory.atomOccurs_iff_mem_translated_vars.mp right
  have fresh := Metta.Minimal.freshenRuleAvoiding_vars_fresh counter avoid
    (toLeaTTaAtom lhs) (toLeaTTaAtom rhs)
  rw [runtime_freshening] at fresh
  simp only [toLeaTTaAtom_renameTypeVars] at renamedOccurs
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

end Mettapedia.Languages.MeTTa.HE.EquationFreshening
