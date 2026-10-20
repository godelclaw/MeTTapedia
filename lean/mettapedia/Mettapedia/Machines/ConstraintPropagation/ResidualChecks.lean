import Mettapedia.Machines.ConstraintPropagation.Readiness

/-!
# Residual checks and conditional answers

A ready check is either discharged or refuted. An unready check remains in
the answer. The executable pass preserves the models of the entire store;
its failure refutes that store, while a nonempty residual is not a proof that
all its eventual checks succeed. Probe correctness is relative to a fixed
world and one completion of the partial bindings.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ConstraintPropagation.ResidualChecks

variable {C : Type*}

def Holds (meaning : C → Prop) (store : List C) : Prop :=
  ∀ c ∈ store, meaning c

def discharge (probe : C → Option Bool) : List C → Option (List C)
  | [] => some []
  | c :: rest =>
    match probe c with
    | some false => none
    | some true => discharge probe rest
    | none => (discharge probe rest).map (c :: ·)

def OutcomeHolds (meaning : C → Prop) : Option (List C) → Prop
  | none => False
  | some pending => Holds meaning pending

theorem discharge_correct (meaning : C → Prop) (probe : C → Option Bool)
    (ready : ∀ c b, probe c = some b → (meaning c ↔ b = true))
    (store : List C) :
    OutcomeHolds meaning (discharge probe store) ↔ Holds meaning store := by
  induction store with
  | nil => simp [discharge, OutcomeHolds, Holds]
  | cons c rest ih =>
    have holdsCons : Holds meaning (c :: rest) ↔ meaning c ∧ Holds meaning rest := by
      simp [Holds]
    cases hp : probe c with
    | none =>
      simp only [discharge, hp]
      cases hr : discharge probe rest with
      | none => simpa [hr, OutcomeHolds, holdsCons] using
          (and_congr_right fun _ => ih)
      | some pending =>
        simpa [hr, OutcomeHolds, Holds, holdsCons] using
          (and_congr_right fun _ => ih)
    | some b =>
      cases b with
      | false => simp [discharge, hp, OutcomeHolds, holdsCons, ready c false hp]
      | true => simpa [discharge, hp, holdsCons, ready c true hp] using ih

theorem refuted_has_no_model (meaning : C → Prop) (probe : C → Option Bool)
    (ready : ∀ c b, probe c = some b → (meaning c ↔ b = true))
    (store : List C) (refuted : discharge probe store = none) :
    ¬ Holds meaning store := by
  rw [← discharge_correct meaning probe ready store, refuted]
  exact id

theorem retained_correct (meaning : C → Prop) (probe : C → Option Bool)
    (ready : ∀ c b, probe c = some b → (meaning c ↔ b = true))
    (store pending : List C) (retained : discharge probe store = some pending) :
    Holds meaning pending ↔ Holds meaning store := by
  simpa [retained, OutcomeHolds] using discharge_correct meaning probe ready store

theorem pending_sublist (probe : C → Option Bool) (store pending : List C)
    (retained : discharge probe store = some pending) : pending.Sublist store := by
  induction store generalizing pending with
  | nil => simpa [discharge] using retained
  | cons c rest ih =>
    cases hp : probe c with
    | none =>
      simp only [discharge, hp] at retained
      cases hr : discharge probe rest with
      | none => simp [hr] at retained
      | some tail =>
        simp only [hr, Option.map_some, Option.some.injEq] at retained
        subst pending
        exact (ih tail hr).cons_cons c
    | some b =>
      cases b with
      | false => simp [discharge, hp] at retained
      | true => exact (ih pending (by simpa [discharge, hp] using retained)).cons c

theorem retained_are_unready (probe : C → Option Bool) (store pending : List C)
    (retained : discharge probe store = some pending) :
    ∀ c ∈ pending, probe c = none := by
  induction store generalizing pending with
  | nil => simp [discharge] at retained; subst pending; simp
  | cons c rest ih =>
    cases hp : probe c with
    | none =>
      simp only [discharge, hp] at retained
      cases hr : discharge probe rest with
      | none => simp [hr] at retained
      | some tail =>
        simp only [hr, Option.map_some, Option.some.injEq] at retained
        subst pending
        simpa [hp] using ih tail hr
    | some b =>
      cases b with
      | false => simp [discharge, hp] at retained
      | true => exact ih pending (by simpa [discharge, hp] using retained)

theorem discharge_unready (probe : C → Option Bool) (store : List C)
    (unready : ∀ c ∈ store, probe c = none) : discharge probe store = some store := by
  induction store with
  | nil => rfl
  | cons c rest ih =>
    simp only [discharge, unready c (by simp)]
    rw [ih (fun d hd => unready d (by simp [hd]))]
    rfl

theorem discharge_idempotent (probe : C → Option Bool) (store pending : List C)
    (retained : discharge probe store = some pending) :
    discharge probe pending = some pending :=
  discharge_unready probe pending (retained_are_unready probe store pending retained)

/-- Incremental checking equals one final pass when ready decisions stay stable. -/
theorem discharge_compose (early late : C → Option Bool)
    (stable : ∀ c b, early c = some b → late c = some b) (store : List C) :
    (discharge early store).bind (discharge late) = discharge late store := by
  induction store with
  | nil => rfl
  | cons c rest ih =>
    cases he : early c with
    | some b =>
      have hl := stable c b he
      cases b with
      | false => simp [discharge, he, hl]
      | true => simp [discharge, he, hl, ih]
    | none =>
      cases hr : discharge early rest with
      | none =>
        have hn : discharge late rest = none := by simpa [hr] using ih.symm
        cases hl : late c with
        | none => simp [discharge, he, hr, hl, hn]
        | some b => cases b <;> simp [discharge, he, hr, hl, hn]
      | some pending =>
        have hp : discharge late pending = discharge late rest := by simpa [hr] using ih
        cases hl : late c with
        | none => simp [discharge, he, hr, hl, hp]
        | some b => cases b <;> simp [discharge, he, hr, hl, hp]

theorem holds_perm (meaning : C → Prop) (one two : List C) (perm : one.Perm two) :
    Holds meaning one ↔ Holds meaning two := by
  simp only [Holds, perm.mem_iff]

end Mettapedia.Machines.ConstraintPropagation.ResidualChecks
