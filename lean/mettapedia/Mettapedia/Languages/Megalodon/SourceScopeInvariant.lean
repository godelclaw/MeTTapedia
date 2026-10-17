import Mettapedia.Languages.Megalodon.SourceTermFragment

/-!
# Term-variable scope at polymorphic regions

The surface fragment is not closed under polymorphic definition expansion.
A type abstraction can appear internally after unfolding a closed definition.
The relevant stronger invariant is that each type-level region is closed in
term variables. Type variables can still refer to the enclosing type context.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SourceScopeInvariant
open MathdataKernel

def Scoped (depth : Nat) : Tm → Prop
  | .db index => index < depth
  | .named _ | .prim _ => True
  | .app first second | .imp first second => Scoped depth first ∧ Scoped depth second
  | .lam _ body | .all _ body => Scoped (depth + 1) body
  | .typeApp body _ | .typeLam body | .typeAll body => Scoped depth body

def Protected : Tm → Prop
  | .db _ | .named _ | .prim _ => True
  | .app first second | .imp first second => Protected first ∧ Protected second
  | .lam _ body | .all _ body => Protected body
  | .typeApp body _ | .typeLam body | .typeAll body => Scoped 0 body ∧ Protected body

instance scopedDecidable (depth : Nat) : (term : Tm) → Decidable (Scoped depth term)
  | .db index => inferInstanceAs (Decidable (index < depth))
  | .named _ | .prim _ => isTrue trivial
  | .app first second | .imp first second =>
      haveI := scopedDecidable depth first
      haveI := scopedDecidable depth second
      inferInstanceAs (Decidable (Scoped depth first ∧ Scoped depth second))
  | .lam _ body | .all _ body => scopedDecidable (depth + 1) body
  | .typeApp body _ | .typeLam body | .typeAll body => scopedDecidable depth body

instance protectedDecidable : (term : Tm) → Decidable (Protected term)
  | .db _ | .named _ | .prim _ => isTrue trivial
  | .app first second | .imp first second =>
      haveI := protectedDecidable first
      haveI := protectedDecidable second
      inferInstanceAs (Decidable (Protected first ∧ Protected second))
  | .lam _ body | .all _ body => protectedDecidable body
  | .typeApp body _ | .typeLam body | .typeAll body =>
      haveI := protectedDecidable body
      inferInstanceAs (Decidable (Scoped 0 body ∧ Protected body))

theorem scoped_mono {body : Tm} {first second : Nat} (scope : Scoped first body)
    (increased : first ≤ second) : Scoped second body := by
  induction body generalizing first second with
  | db index => exact Nat.lt_of_lt_of_le scope increased
  | named | prim => trivial
  | app _ _ ihf iha | imp _ _ ihf iha => exact ⟨ihf scope.1 increased, iha scope.2 increased⟩
  | lam _ _ ih | all _ _ ih => exact ih scope (by omega)
  | typeApp _ _ ih | typeLam _ ih | typeAll _ ih => exact ih scope increased

theorem shift_eq {body : Tm} {bound : Nat} (scope : Scoped bound body)
    (cutoff amount : Nat) (below : bound ≤ cutoff) : Tm.shift cutoff amount body = body := by
  induction body generalizing bound cutoff with
  | db index => simp [Tm.shift, show index < cutoff from Nat.lt_of_lt_of_le scope below]
  | named | prim => rfl
  | app _ _ ihf iha | imp _ _ ihf iha => simp [Tm.shift, ihf scope.1 cutoff below, iha scope.2 cutoff below]
  | lam _ _ ih | all _ _ ih => simp [Tm.shift, ih scope (cutoff + 1) (by omega)]
  | typeApp _ _ ih | typeLam _ ih | typeAll _ ih => simp [Tm.shift, ih scope cutoff below]

theorem instantiate_eq {body : Tm} {bound : Nat} (scope : Scoped bound body)
    (depth : Nat) (replacement : Tm) (below : bound ≤ depth) : Tm.instantiateAt depth replacement body = body := by
  induction body generalizing bound depth with
  | db index => simp [Tm.instantiateAt, show index < depth from Nat.lt_of_lt_of_le scope below]
  | named | prim => rfl
  | app _ _ ihf iha | imp _ _ ihf iha =>
      simp [Tm.instantiateAt, ihf scope.1 depth below, iha scope.2 depth below]
  | lam _ _ ih | all _ _ ih => simp [Tm.instantiateAt, ih scope (depth + 1) (by omega)]
  | typeApp _ _ ih | typeLam _ ih | typeAll _ ih => simp [Tm.instantiateAt, ih scope depth below]

theorem drop_eq {body : Tm} {bound : Nat} (scope : Scoped bound body)
    (cutoff : Nat) (below : bound ≤ cutoff) : Tm.dropAt? cutoff body = some body := by
  induction body generalizing bound cutoff with
  | db index => simp [Tm.dropAt?, show index < cutoff from Nat.lt_of_lt_of_le scope below]
  | named | prim => rfl
  | app _ _ ihf iha | imp _ _ ihf iha => simp [Tm.dropAt?, ihf scope.1 cutoff below, iha scope.2 cutoff below]
  | lam _ _ ih | all _ _ ih => simp [Tm.dropAt?, ih scope (cutoff + 1) (by omega)]
  | typeApp _ _ ih | typeLam _ ih | typeAll _ ih => simp [Tm.dropAt?, ih scope cutoff below]

theorem scoped_shift {body : Tm} {bound : Nat} (scope : Scoped bound body) (cutoff amount : Nat) :
    Scoped (bound + amount) (Tm.shift cutoff amount body) := by
  induction body generalizing bound cutoff with
  | db index =>
      change index < bound at scope
      simp only [Tm.shift]; split <;> simp only [Scoped] <;> omega
  | named | prim => trivial
  | app _ _ ihf iha | imp _ _ ihf iha => exact ⟨ihf scope.1 cutoff, iha scope.2 cutoff⟩
  | lam _ _ ih | all _ _ ih => simpa [Tm.shift, Scoped, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih scope (cutoff + 1)
  | typeApp _ _ ih | typeLam _ ih | typeAll _ ih => exact ih scope cutoff

theorem scoped_typeInstantiate (body : Tm) (bound depth : Nat) (replacement : Tp) :
    Scoped bound (Tm.typeInstantiateAt depth replacement body) = Scoped bound body := by
  induction body generalizing bound depth <;> simp_all [Tm.typeInstantiateAt, Scoped]

theorem scoped_instantiate {body replacement : Tm} {bound : Nat} (argument : Scoped bound replacement)
    (depth : Nat) (scope : Scoped (bound + depth + 1) body) :
    Scoped (bound + depth) (Tm.instantiateAt depth replacement body) := by
  induction body generalizing depth with
  | db index =>
      change index < bound + depth + 1 at scope
      simp only [Tm.instantiateAt]
      split
      · simp only [Scoped]; omega
      · split
        · exact scoped_shift argument 0 depth
        · simp only [Scoped]; omega
  | named | prim => trivial
  | app _ _ ihf iha | imp _ _ ihf iha => exact ⟨ihf depth scope.1, iha depth scope.2⟩
  | lam _ _ ih | all _ _ ih =>
      simpa only [Tm.instantiateAt, Scoped, Nat.add_assoc] using ih (depth + 1) (by simpa only [Scoped, Nat.add_assoc] using scope)
  | typeApp _ _ ih | typeLam _ ih | typeAll _ ih => exact ih depth scope

theorem protected_shift {body : Tm} (safe : Protected body) (cutoff amount : Nat) :
    Protected (Tm.shift cutoff amount body) := by
  induction body generalizing cutoff with
  | db index => simp only [Tm.shift]; split <;> trivial
  | named | prim => trivial
  | app _ _ ihf iha | imp _ _ ihf iha => exact ⟨ihf safe.1 cutoff, iha safe.2 cutoff⟩
  | lam _ _ ih | all _ _ ih => exact ih safe (cutoff + 1)
  | typeApp _ _ _ | typeLam _ _ | typeAll _ _ =>
      simpa only [Tm.shift, shift_eq safe.1 cutoff amount (Nat.zero_le cutoff)] using safe

theorem protected_instantiate {body replacement : Tm} (safe : Protected body) (argument : Protected replacement)
    (depth : Nat) : Protected (Tm.instantiateAt depth replacement body) := by
  induction body generalizing depth with
  | db index =>
      simp only [Tm.instantiateAt]
      split
      · trivial
      · split
        · exact protected_shift argument 0 depth
        · trivial
  | named | prim => trivial
  | app _ _ ihf iha | imp _ _ ihf iha => exact ⟨ihf safe.1 depth, iha safe.2 depth⟩
  | lam _ _ ih | all _ _ ih => exact ih safe (depth + 1)
  | typeApp _ _ _ | typeLam _ _ | typeAll _ _ =>
      simpa only [Tm.instantiateAt, instantiate_eq safe.1 depth replacement (Nat.zero_le depth)] using safe

theorem protected_typeInstantiate {body : Tm} (safe : Protected body) (depth : Nat) (replacement : Tp) :
    Protected (Tm.typeInstantiateAt depth replacement body) := by
  induction body generalizing depth with
  | db | named | prim => trivial
  | app _ _ ihf iha | imp _ _ ihf iha => exact ⟨ihf safe.1 depth, iha safe.2 depth⟩
  | lam _ _ ih | all _ _ ih => exact ih safe depth
  | typeApp body type ih => exact ⟨(scoped_typeInstantiate body 0 depth replacement) ▸ safe.1, ih safe.2 depth⟩
  | typeLam body ih | typeAll body ih =>
      exact ⟨(scoped_typeInstantiate body 0 (depth + 1) replacement) ▸ safe.1, ih safe.2 (depth + 1)⟩

/-- Publication's type-region traversal boundary is harmless on Protected
terms, even after a polymorphic definition introduces an internal type lambda. -/
theorem publication_substitution_agrees {body : Tm} (safe : Protected body) (depth : Nat) (replacement : Tm) :
    SourceTermFragment.publicationSubstitute depth replacement body = Tm.instantiateAt depth replacement body := by
  induction body generalizing depth with
  | db | named | prim => rfl
  | app _ _ ihf iha | imp _ _ ihf iha =>
      simp [SourceTermFragment.publicationSubstitute, Tm.instantiateAt, ihf safe.1, iha safe.2]
  | lam _ _ ih | all _ _ ih => simp [SourceTermFragment.publicationSubstitute, Tm.instantiateAt, ih safe]
  | typeApp _ _ _ | typeLam _ _ | typeAll _ _ =>
      simp [SourceTermFragment.publicationSubstitute, Tm.instantiateAt,
        instantiate_eq safe.1 depth replacement (Nat.zero_le depth)]

theorem source_head_closed {head : Tm} (admitted : SourceTermFragment.Head head) : Scoped 0 head ∧ Protected head := by
  induction admitted with
  | named | prim => exact ⟨trivial, trivial⟩
  | typeApp _ _ ih => exact ⟨ih.1, ih⟩

theorem source_term_protected {term : Tm} (admitted : SourceTermFragment.Term term) : Protected term := by
  induction admitted with
  | db => trivial
  | head head => exact (source_head_closed head).2
  | app _ _ ihf iha | imp _ _ ihf iha => exact ⟨ihf, iha⟩
  | lam _ _ ih | all _ _ ih => exact ih

theorem expanded_polymorphic_identity_protected :
    Protected (.typeApp (.typeLam (.lam (.var 0) (.db 0))) (.var 0)) := by decide

theorem raw_capture_example_excluded : ¬ Protected (.typeLam (.db 0)) := by decide

end Mettapedia.Languages.Megalodon.SourceScopeInvariant
