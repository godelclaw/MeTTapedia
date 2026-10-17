import Mettapedia.Languages.Megalodon.SourceScopeInvariant

/-! # Scope and protected polymorphic regions through unused-binder removal -/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SourceScopeInvariant
open MathdataKernel

theorem scoped_drop {body result : Tm} (bound cutoff : Nat)
    (scope : Scoped (bound + cutoff + 1) body) (removed : Tm.dropAt? cutoff body = some result) :
    Scoped (bound + cutoff) result := by
  induction body generalizing cutoff result with
  | db index =>
      change index < bound + cutoff + 1 at scope
      simp only [Tm.dropAt?] at removed
      split at removed
      · cases Option.some.inj removed
        change index < bound + cutoff
        omega
      · split at removed
        · cases removed
        · cases Option.some.inj removed
          change index - 1 < bound + cutoff
          omega
  | named | prim => cases Option.some.inj removed; trivial
  | app _ _ ihf iha | imp _ _ ihf iha =>
      simp [Tm.dropAt?, Option.bind_eq_some_iff] at removed
      obtain ⟨first, firstRemoved, second, secondRemoved, rfl⟩ := removed
      exact ⟨ihf cutoff scope.1 firstRemoved, iha cutoff scope.2 secondRemoved⟩
  | lam _ _ ih | all _ _ ih =>
      simp [Tm.dropAt?, Option.bind_eq_some_iff] at removed
      obtain ⟨body, bodyRemoved, rfl⟩ := removed
      simpa only [Scoped, Nat.add_assoc] using ih (cutoff + 1)
        (by simpa only [Scoped, Nat.add_assoc] using scope) bodyRemoved
  | typeApp _ _ ih | typeLam _ ih | typeAll _ ih =>
      simp [Tm.dropAt?, Option.bind_eq_some_iff] at removed
      obtain ⟨body, bodyRemoved, rfl⟩ := removed
      exact ih (result := body) cutoff scope bodyRemoved

theorem protected_drop {body result : Tm} (safe : Protected body) (cutoff : Nat)
    (removed : Tm.dropAt? cutoff body = some result) : Protected result := by
  induction body generalizing cutoff result with
  | db index =>
      simp only [Tm.dropAt?] at removed
      split at removed
      · cases Option.some.inj removed; trivial
      · split at removed
        · cases removed
        · cases Option.some.inj removed; trivial
  | named | prim => cases Option.some.inj removed; trivial
  | app _ _ ihf iha | imp _ _ ihf iha =>
      simp [Tm.dropAt?, Option.bind_eq_some_iff] at removed
      obtain ⟨first, firstRemoved, second, secondRemoved, rfl⟩ := removed
      exact ⟨ihf safe.1 cutoff firstRemoved, iha safe.2 cutoff secondRemoved⟩
  | lam _ _ ih | all _ _ ih =>
      simp [Tm.dropAt?, Option.bind_eq_some_iff] at removed
      obtain ⟨body, bodyRemoved, rfl⟩ := removed
      exact ih (result := body) safe (cutoff + 1) bodyRemoved
  | typeApp | typeLam | typeAll =>
      simp only [Tm.dropAt?, drop_eq safe.1 cutoff (Nat.zero_le cutoff),
        Option.pure_def] at removed
      cases removed
      exact safe

theorem scoped_typeDrop {body result : Tm} (bound cutoff : Nat)
    (removed : Tm.typeDropAt? cutoff body = some result) : Scoped bound result = Scoped bound body := by
  induction body generalizing bound cutoff result with
  | db | named | prim => cases Option.some.inj removed; rfl
  | app _ _ ihf iha | imp _ _ ihf iha =>
      simp [Tm.typeDropAt?, Option.bind_eq_some_iff] at removed
      obtain ⟨first, firstRemoved, second, secondRemoved, rfl⟩ := removed
      simp only [Scoped, ihf bound cutoff firstRemoved, iha bound cutoff secondRemoved]
  | lam _ _ ih | all _ _ ih =>
      simp [Tm.typeDropAt?, Option.bind_eq_some_iff] at removed
      obtain ⟨type, _, body, bodyRemoved, rfl⟩ := removed
      exact ih (bound + 1) cutoff bodyRemoved
  | typeApp _ _ ih =>
      simp [Tm.typeDropAt?, Option.bind_eq_some_iff] at removed
      obtain ⟨body, bodyRemoved, type, _, rfl⟩ := removed
      exact ih (result := body) bound cutoff bodyRemoved
  | typeLam _ ih | typeAll _ ih =>
      simp [Tm.typeDropAt?, Option.bind_eq_some_iff] at removed
      obtain ⟨body, bodyRemoved, rfl⟩ := removed
      exact ih (result := body) bound (cutoff + 1) bodyRemoved

theorem protected_typeDrop {body result : Tm} (safe : Protected body) (cutoff : Nat)
    (removed : Tm.typeDropAt? cutoff body = some result) : Protected result := by
  induction body generalizing cutoff result with
  | db | named | prim => cases Option.some.inj removed; trivial
  | app _ _ ihf iha | imp _ _ ihf iha =>
      simp [Tm.typeDropAt?, Option.bind_eq_some_iff] at removed
      obtain ⟨first, firstRemoved, second, secondRemoved, rfl⟩ := removed
      exact ⟨ihf safe.1 cutoff firstRemoved, iha safe.2 cutoff secondRemoved⟩
  | lam _ _ ih | all _ _ ih =>
      simp [Tm.typeDropAt?, Option.bind_eq_some_iff] at removed
      obtain ⟨type, _, body, bodyRemoved, rfl⟩ := removed
      exact ih (result := body) safe cutoff bodyRemoved
  | typeApp _ _ ih =>
      simp [Tm.typeDropAt?, Option.bind_eq_some_iff] at removed
      obtain ⟨body, bodyRemoved, type, _, rfl⟩ := removed
      exact ⟨(scoped_typeDrop 0 cutoff bodyRemoved) ▸ safe.1, ih safe.2 cutoff bodyRemoved⟩
  | typeLam _ ih | typeAll _ ih =>
      simp [Tm.typeDropAt?, Option.bind_eq_some_iff] at removed
      obtain ⟨body, bodyRemoved, rfl⟩ := removed
      exact ⟨(scoped_typeDrop 0 (cutoff + 1) bodyRemoved) ▸ safe.1, ih safe.2 (cutoff + 1) bodyRemoved⟩

end Mettapedia.Languages.Megalodon.SourceScopeInvariant
