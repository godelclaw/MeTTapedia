import Mettapedia.OSLF.Syntax.RhoSourceEquationModel
import Mettapedia.OSLF.Syntax.BindingConstructorPredicates

/-!
# A nonconstant structural predicate on the complete rho equation quotient

The existing output-occurrence count respects all source equations, including
name reflection and congruence beneath input binders. Its positive predicate
is stable under arbitrary quotient-valued substitution. The zero predicate
is a current-context observation: substituting an output for a process
variable shows that it is not a substitution-stable native family.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoSourceOutputPredicate

open RhoSchema BindingConstructorPredicates BindingSubstitutionAlgebra

/-- The complete source equation list preserves the existing occurrence
count for every contextual body and both closing environments. -/
theorem outputCount_source_equation : ∀ (i : Fin rhoSourceE.length)
    {Θ Γ : Ctx sig} (body : ContextualAssignment sig metas Θ)
    (ambient : Sub sig Θ Γ) (close : Sub sig (rhoSourceE.get i).ctx Γ),
    outputCount (ContextualAssignment.instantiate body ambient close (rhoSourceE.get i).lhs) =
      outputCount (ContextualAssignment.instantiate body ambient close (rhoSourceE.get i).rhs)
  | ⟨0, _⟩, _, _, body, ambient, close =>
      outputCount_axiom ⟨0, by decide⟩ body ambient close
  | ⟨1, _⟩, _, _, body, ambient, close =>
      outputCount_axiom ⟨1, by decide⟩ body ambient close
  | ⟨2, _⟩, _, _, body, ambient, close =>
      outputCount_axiom ⟨2, by decide⟩ body ambient close
  | ⟨3, _⟩, _, _, body, ambient, close => by
      simp only [rhoSourceE, List.get, quoteDrop, ContextualAssignment.instantiate,
        ContextualAssignment.instantiateArgs, liftSub, outputCount, outputCountArgs,
        outputHeadCount, Nat.zero_add, Nat.add_zero]
  | ⟨_ + 4, bound⟩, _, _, _, _, _ => by simp [rhoSourceE] at bound

mutual
/-- Output count is constant on the complete source congruence at every
context and sort, including under actual input binders. -/
theorem outputCount_source_congruence : ∀ {Γ : Ctx sig} {sort : Srt}
    {first second : Term sig Γ sort},
    EqClosure rhoSourceE first second → outputCount first = outputCount second
  | _, _, _, _, .ax i body ambient ordinary =>
      outputCount_source_equation i body ambient ordinary
  | _, _, _, _, .refl _ => rfl
  | _, _, _, _, .symm related => (outputCount_source_congruence related).symm
  | _, _, _, _, .trans first second =>
      (outputCount_source_congruence first).trans (outputCount_source_congruence second)
  | _, _, _, _, .cong _ related => by
      simp only [outputCount, outputCountArgs_source_congruence related]

theorem outputCountArgs_source_congruence : ∀ {arity : List (List Srt × Srt)}
    {Γ : Ctx sig} {first second : Args sig arity Γ},
    EqArgs rhoSourceE first second → outputCountArgs first = outputCountArgs second
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons head tail => by
      simp only [outputCountArgs, outputCount_source_congruence head,
        outputCountArgs_source_congruence tail]
end

/-- A constructed, nonconstant readout of actual source equation classes. -/
def count {Γ : Ctx sig} {sort : Srt} : TermQ rhoSourceE Γ sort → Nat :=
  Quotient.lift outputCount (fun _ _ related => outputCount_source_congruence related)

theorem count_mk {Γ : Ctx sig} {sort : Srt} (term : Term sig Γ sort) :
    count (Quotient.mk _ term : TermQ rhoSourceE Γ sort) = outputCount term := rfl

/-- Counting a selected representative recovers the constructed class
readout; this equality is earned from congruence invariance. -/
theorem count_representative {Γ : Ctx sig} {sort : Srt}
    (value : TermQ rhoSourceE Γ sort) :
    outputCount (Quotient.out value) = count value :=
  congrArg count (Quotient.out_eq value)

/-- Count the complete semantic argument vector, including binder bodies. -/
def countArguments : {arity : List (List Srt × Srt)} → {Γ : Ctx sig} →
    FreeBindingTerms.FamilyArgs sig (TermQ rhoSourceE) arity Γ → Nat
  | _, _, .nil => 0
  | _, _, .cons head tail => count head + countArguments tail

theorem count_representativeArguments : ∀ {arity : List (List Srt × Srt)}
    {Γ : Ctx sig}
    (arguments : FreeBindingTerms.FamilyArgs sig (TermQ rhoSourceE) arity Γ),
    outputCountArgs (BindingEquationQuotientModel.representativeArgs rhoSourceE arguments) =
      countArguments arguments
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [BindingEquationQuotientModel.representativeArgs, outputCountArgs,
        countArguments, count_representative head, count_representativeArguments tail]

/-- The readout of the independently constructed quotient operation counts
its actual head and every retained argument occurrence. -/
theorem count_operation {Γ : Ctx sig} {sort : Srt} (operator : Op sort)
    (arguments : FreeBindingTerms.FamilyArgs sig (TermQ rhoSourceE) (sig.arity operator) Γ) :
    count ((BindingEquationQuotientModel.algebra rhoSourceE).operation operator arguments) =
      outputHeadCount operator + countArguments arguments := by
  change outputCount (.op operator
    (BindingEquationQuotientModel.representativeArgs rhoSourceE arguments)) = _
  rw [outputCount, count_representativeArguments]

mutual
/-- Substitution can add outputs through variables, but cannot erase the
output constructors already present in a term. -/
theorem outputCount_le_bind : ∀ {Γ Δ : Ctx sig} (env : Sub sig Γ Δ)
    {sort : Srt} (term : Term sig Γ sort),
    outputCount term ≤ outputCount (bind env term)
  | _, _, _, _, .var _ => Nat.zero_le _
  | _, _, env, _, .op _operator arguments =>
      Nat.add_le_add_left (outputCountArgs_le_bind env arguments) _

theorem outputCountArgs_le_bind : ∀ {Γ Δ : Ctx sig} (env : Sub sig Γ Δ)
    {arity : List (List Srt × Srt)} (arguments : Args sig arity Γ),
    outputCountArgs arguments ≤ outputCountArgs (bindArgs env arguments)
  | _, _, _, _, .nil => Nat.le_refl _
  | _, _, env, _, .cons (bs := binders) head tail =>
      Nat.add_le_add (outputCount_le_bind (liftSub env binders) head)
        (outputCountArgs_le_bind env tail)
end

/-- The same bound holds for arbitrary equation-class environments, using
the already constructed full quotient binding model. -/
theorem count_le_substitute {Γ Δ : Ctx sig} {sort : Srt}
    (env : Environment sig (TermQ rhoSourceE) Γ Δ)
    (value : TermQ rhoSourceE Γ sort) :
    count value ≤ count
      ((BindingEquationQuotientModel.algebra rhoSourceE).substitution.substitute env value) := by
  induction value using Quotient.inductionOn with
  | _ term =>
      change outputCount term ≤ outputCount
        (bind (BindingEquationQuotientSubstitution.representativeEnv rhoSourceE env) term)
      exact outputCount_le_bind _ term

/-- Positive output occurrence is an equation-compatible native predicate
at each sort, with all quotient-valued future substitutions admitted. -/
noncomputable def positive (sort : Srt) :
    Predicate (BindingEquationQuotientModel.algebra rhoSourceE) sort where
  holds := fun value => 0 < count value
  substitute := by
    intro Γ Δ env value present
    exact present.trans_le (count_le_substitute env value)

/-- A closed source output. Its payload and quoted channel are null. -/
def output : Term sig [] Srt.pr :=
  .op Op.out (.cons chan (.cons nilP .nil))

theorem output_count : outputCount output = 1 := rfl

theorem null_count : outputCount nilP = 0 := rfl

/-- The positive native predicate distinguishes actual output from null. -/
theorem positive_output :
    (positive Srt.pr).holds (Quotient.mk _ output : TermQ rhoSourceE [] Srt.pr) := by
  change 0 < outputCount output
  decide

theorem null_not_positive :
    ¬ (positive Srt.pr).holds (Quotient.mk _ nilP : TermQ rhoSourceE [] Srt.pr) := by
  change ¬ 0 < outputCount nilP
  decide

/-- Current absence of output cannot be the exact readout of a
substitution-stable family: a variable can receive a genuine output. -/
theorem zero_count_not_stable :
    ¬ ∃ predicate : Predicate (BindingEquationQuotientModel.algebra rhoSourceE) Srt.pr,
      ∀ {Γ : Ctx sig} (value : TermQ rhoSourceE Γ Srt.pr),
        predicate.holds value ↔ count value = 0 := by
  rintro ⟨predicate, readout⟩
  let variableValue : TermQ rhoSourceE [Srt.pr] Srt.pr := Quotient.mk _ (.var .zero)
  let env : Environment sig (TermQ rhoSourceE) [Srt.pr] [] :=
    fun _ position => match position with
      | .zero => Quotient.mk _ output
  have before : predicate.holds variableValue := (readout variableValue).mpr rfl
  have after := predicate.substitute env variableValue before
  have reading := (readout _).mp after
  change count (BindingEquationQuotientSubstitution.substitute rhoSourceE env
    (Quotient.mk _ (.var .zero))) = 0 at reading
  rw [BindingEquationQuotientSubstitution.substitute_var] at reading
  change outputCount output = 0 at reading
  rw [output_count] at reading
  cases reading

end Mettapedia.OSLF.Binding.RhoSourceOutputPredicate
