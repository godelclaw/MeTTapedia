import Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceReplies
import Mettapedia.Languages.MeTTa.HE.BindingComposition
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Instantiation
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Normal
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.BindingComposition
open Mettapedia.Languages.MeTTa.HE.MatchSizeTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-!
# Constructed substitution boundary for retained argument requests

The source binding application is connected to the independent finite
presentation relation on normal, equality-free substitutions. Stored values
may contain unassigned variables and arbitrarily nested expressions. The
original argument and telescope domain remain in the saved state, while the
prepared service request contains their independently earned instantiations.

This boundary does not identify an original request with its resolved one.
Native equality-class import, dependent-domain refinement and heap/export
correspondence remain separate implementation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessPreparedArguments

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Instantiation Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open NativeArgumentControl NativeArgumentControlPolicy

/-- The finite presentation's assignments, without an invented equality
relation. Normality is an explicit invariant of this imported binding profile. -/
def presentedBindings (substitution : TypeSubst) : Bindings := ⟨substitution, []⟩

@[simp] theorem lookup_presented (substitution : TypeSubst) (name : String) :
    (presentedBindings substitution).lookup name = substitution.lookup name := by
  induction substitution with
  | nil => rfl
  | cons entry remaining ih =>
      rcases entry with ⟨key, value⟩
      by_cases same : name = key
      · subst key
        simp [presentedBindings, Bindings.lookup, TypeSubst.lookup]
      · have different : (name == key) = false := beq_eq_false_iff_ne.mpr same
        simp [presentedBindings, Bindings.lookup, List.lookup, TypeSubst.lookup, same, different] at ih ⊢
        exact ih

private theorem child_variable (child : Atom) (children : List Atom)
    (present : child ∈ children) (name : String)
    (occurs : name ∈ TypeSubst.typeVars child) :
    name ∈ TypeSubst.typeVarsList children := by
  induction children with
  | nil => simp at present
  | cons head remaining ih =>
      rcases List.mem_cons.mp present with rfl | tail
      · simp [TypeSubst.typeVarsList, occurs]
      · simp only [TypeSubst.typeVarsList, List.mem_append]
        exact Or.inr (ih tail)

/-- No finite scan discovers an assigned variable in an atom whose variables
are all absent from the presentation's keys. This requires no groundness. -/
theorem scan_absent (substitution : TypeSubst) (fuel : Nat) (value : Atom)
    (absent : ∀ name ∈ TypeSubst.typeVars value, name ∉ substitution.keys) :
    (presentedBindings substitution).hasAssignedVarAux fuel value = false := by
  induction fuel generalizing value with
  | zero => rfl
  | succ fuel ih =>
      cases value with
      | symbol name => rfl
      | grounded value => rfl
      | var name =>
          have missing := TypeSubst.lookup_eq_none_of_not_mem_keys
            (absent name (by simp [TypeSubst.typeVars]))
          simp [Bindings.hasAssignedVarAux, Bindings.isBound, missing]
      | expression children =>
          simp only [Bindings.hasAssignedVarAux, List.any_eq_false]
          intro child present
          rw [ih child (fun name occurs => absent name
            (child_variable child children present name occurs))]
          decide

theorem presented_assignment_independence {substitution : TypeSubst}
    (normal : substitution.Normal) : AssignmentValuesIndependent (presentedBindings substitution) := by
  intro name value lookup
  have found : substitution.lookup name = some value := by simpa using lookup
  exact scan_absent substitution _ value
    (normal.2 name value (TypeSubst.lookup_eq_some_mem found))

/-- The actual source application agrees with independent one-pass
instantiation at every sufficient structural budget. -/
theorem apply_presented {substitution : TypeSubst} (normal : substitution.Normal) :
    ∀ fuel value, atomDepth value + 2 ≤ fuel →
      (presentedBindings substitution).apply value fuel = substitution.apply value := by
  have independent := presented_assignment_independence normal
  intro fuel
  induction fuel with
  | zero => intro value enough; omega
  | succ fuel ih =>
      intro value enough
      cases fuel with
      | zero => cases value <;> simp [atomDepth] at enough
      | succ fuel =>
          cases value with
          | symbol name => simp only [Bindings.apply, TypeSubst.apply]
          | grounded value => simp only [Bindings.apply, TypeSubst.apply]
          | var name =>
              simp only [Bindings.apply,
                resolve_eq_lookup_of_assignmentValuesIndependent independent name fuel,
                lookup_presented, TypeSubst.apply]
              cases substitution.lookup name <;> rfl
          | expression children =>
              have each : ∀ children : List Atom, listDepth children + 2 ≤ fuel + 1 →
                  children.map (fun child => (presentedBindings substitution).apply child (fuel + 1)) =
                    children.map substitution.apply := by
                intro children
                induction children with
                | nil => intro _; rfl
                | cons child remaining ihChildren =>
                    intro depth
                    have head : atomDepth child + 2 ≤ fuel + 1 := by
                      simp only [listDepth] at depth
                      omega
                    have tail : listDepth remaining + 2 ≤ fuel + 1 := by
                      simp only [listDepth] at depth
                      omega
                    simp only [List.map_cons, ih child head, ihChildren tail]
              have depth : listDepth children + 2 ≤ fuel + 1 := by
                simp only [atomDepth] at enough
                omega
              simpa only [Bindings.apply, TypeSubst.apply] using
                congrArg Atom.expression (each children depth)

theorem applyFull_presented {substitution : TypeSubst} (normal : substitution.Normal)
    (fuel : Nat) (value : Atom) (enough : atomDepth value + 2 ≤ fuel) :
    (presentedBindings substitution).applyFull value fuel = substitution.apply value := by
  rw [Bindings.applyFull_no_equalities (show (presentedBindings substitution).equalities = [] from rfl)]
  exact apply_presented normal fuel value enough

/-- Source substitution and the independent grammar agree on exactly the
resolved atom, including unassigned variable names. -/
theorem application_iff {substitution : TypeSubst} (normal : substitution.Normal)
    (fuel : Nat) (original resolved : Atom) (enough : atomDepth original + 2 ≤ fuel) :
    (presentedBindings substitution).applyFull original fuel = resolved ↔
      TypeInstantiatePresentationRel substitution original resolved := by
  rw [applyFull_presented normal fuel original enough]
  exact (coincidence substitution original resolved).symm

/-- Independent preparation keeps both original projections in the input
state. Evaluation is subsequently requested at the resolved endpoint. -/
inductive PreparationRel (substitution : TypeSubst) (state : TypedApplyState)
    (policy : Policy) : Prepared → Prop where
  | prepared {domain bound : Atom} :
      TypeInstantiatePresentationRel substitution (originalDomain state) domain →
      TypeInstantiatePresentationRel substitution (original state) bound →
      PreparationRel substitution state policy ⟨domain, bound, policy⟩

def prepareSource (state : TypedApplyState) (policy : Policy) (fuel : Nat) : Prepared :=
  ⟨state.env.applyFull (originalDomain state) fuel,
    state.env.applyFull (original state) fuel, policy⟩

theorem preparation_sound {substitution : TypeSubst} (normal : substitution.Normal)
    (state : TypedApplyState) (policy : Policy) (fuel : Nat)
    (imported : state.env = presentedBindings substitution)
    (domainBudget : atomDepth (originalDomain state) + 2 ≤ fuel)
    (argumentBudget : atomDepth (original state) + 2 ≤ fuel) :
    PreparationRel substitution state policy (prepareSource state policy fuel) := by
  unfold prepareSource
  rw [imported]
  exact .prepared
    ((application_iff normal fuel _ _ domainBudget).mp rfl)
    ((application_iff normal fuel _ _ argumentBudget).mp rfl)

theorem preparation_complete {substitution : TypeSubst} (normal : substitution.Normal)
    (state : TypedApplyState) (policy : Policy) (fuel : Nat)
    (imported : state.env = presentedBindings substitution)
    (domainBudget : atomDepth (originalDomain state) + 2 ≤ fuel)
    (argumentBudget : atomDepth (original state) + 2 ≤ fuel) (prepared : Prepared)
    (earned : PreparationRel substitution state policy prepared) :
    prepareSource state policy fuel = prepared := by
  cases earned with
  | prepared domain bound =>
      unfold prepareSource
      rw [imported, (application_iff normal fuel _ _ domainBudget).mpr domain,
        (application_iff normal fuel _ _ argumentBudget).mpr bound]

theorem preparation_iff {substitution : TypeSubst} (normal : substitution.Normal)
    (state : TypedApplyState) (policy : Policy) (fuel : Nat)
    (imported : state.env = presentedBindings substitution)
    (domainBudget : atomDepth (originalDomain state) + 2 ≤ fuel)
    (argumentBudget : atomDepth (original state) + 2 ≤ fuel) (prepared : Prepared) :
    prepareSource state policy fuel = prepared ↔ PreparationRel substitution state policy prepared := by
  constructor
  · rintro rfl
    exact preparation_sound normal state policy fuel imported domainBudget argumentBudget
  · exact preparation_complete normal state policy fuel imported domainBudget argumentBudget prepared

theorem preparation_originals_retained (state : TypedApplyState) (policy : Policy) (fuel : Nat) :
    (NativeArgumentControl.selectedSnapshot state (prepareSource state policy fuel) []).original =
      original state ∧
    (NativeArgumentControl.selectedSnapshot state (prepareSource state policy fuel) []).domain =
      originalDomain state := ⟨rfl, rfl⟩

/-- The existing readiness guard earns sufficient evaluation of the same
normal table even when its original depth is below the convenient syntax bound. -/
theorem applyFull_presented_of_covered {table : TypeSubst} (normal : table.Normal)
    (atom : Atom) (depth : Nat)
    (covered : (presentedBindings table).applyFullCovered atom depth = true) :
    (presentedBindings table).applyFull atom depth = table.apply atom := by
  rw [← Bindings.applyFullCovered_stable (presentedBindings table) atom depth
    (BindingComposition.atomDepth atom + 2) covered]
  exact applyFull_presented normal _ atom (by omega)


end Mettapedia.Languages.MeTTa.HE.FirstSuccessPreparedArguments
