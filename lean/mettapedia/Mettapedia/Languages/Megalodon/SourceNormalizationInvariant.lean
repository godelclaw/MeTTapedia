import Mettapedia.Languages.Megalodon.SourceScopeRemoval

/-! # Scope preservation through the actual beta/eta normalization passes -/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SourceScopeInvariant
open MathdataKernel

theorem pass_scoped {body : Tm} (depth : Nat) (scope : Scoped depth body) :
    Scoped depth (Tm.normalizeOne body).1 := by
  induction body generalizing depth with
  | db | named | prim => exact scope
  | app function argument ihf iha =>
      have fs := ihf depth scope.1
      have ars := iha depth scope.2
      cases hf : Tm.normalizeOne function with
      | mk fr fb =>
          cases ha : Tm.normalizeOne argument with
          | mk ar ab =>
              simp only [hf, ha] at fs ars
              cases fr <;> simp only [Tm.normalizeOne, hf, ha]
              all_goals first
                | exact ⟨fs, ars⟩
                | exact scoped_instantiate ars 0 fs
  | lam type body ih =>
      have bs := ih (depth + 1) scope
      cases hb : Tm.normalizeOne body with
      | mk br bb =>
          simp only [hb] at bs
          cases br with
          | app function argument =>
              cases argument with
              | db index =>
                  cases index with
                  | zero =>
                      cases removed : Tm.dropAt? 0 function with
                      | none => simpa only [Tm.normalizeOne, hb, removed, Scoped] using bs
                      | some result =>
                          simpa only [Tm.normalizeOne, hb, removed, Nat.add_zero] using scoped_drop depth 0 bs.1 removed
                  | succ index => simp only [Tm.normalizeOne, hb, Scoped] at bs ⊢ <;> exact bs
              | _ => simp only [Tm.normalizeOne, hb, Scoped] at bs ⊢ <;> exact bs
          | _ => simp only [Tm.normalizeOne, hb, Scoped] at bs ⊢ <;> exact bs
  | imp domain codomain ihd ihc =>
      exact ⟨ihd depth scope.1, ihc depth scope.2⟩
  | all type body ih => exact ih (depth + 1) scope
  | typeApp function type ih =>
      have fs := ih depth scope
      cases hf : Tm.normalizeOne function with
      | mk fr fb =>
          simp only [hf] at fs
          cases fr <;> simp only [Tm.normalizeOne, hf]
          all_goals first
            | exact fs
            | simpa only [Tm.typeInstantiate, scoped_typeInstantiate, Scoped] using fs
  | typeLam body ih =>
      have bs := ih depth scope
      cases hb : Tm.normalizeOne body with
      | mk br bb =>
          simp only [hb] at bs
          cases br with
          | typeApp function type =>
              cases type with
              | var index =>
                  cases index with
                  | zero =>
                      cases removed : Tm.typeDropAt? 0 function with
                      | none => simpa only [Tm.normalizeOne, hb, removed, Scoped] using bs
                      | some result =>
                          simpa only [Tm.normalizeOne, hb, removed] using (scoped_typeDrop depth 0 removed) ▸ bs
                  | succ index => simp only [Tm.normalizeOne, hb, Scoped] at bs ⊢ <;> exact bs
              | _ => simp only [Tm.normalizeOne, hb, Scoped] at bs ⊢ <;> exact bs
          | _ => simp only [Tm.normalizeOne, hb, Scoped] at bs ⊢ <;> exact bs
  | typeAll body ih => exact ih depth scope

theorem pass_protected {body : Tm} (safe : Protected body) : Protected (Tm.normalizeOne body).1 := by
  induction body with
  | db | named | prim => trivial
  | app function argument ihf iha =>
      have fs := ihf safe.1
      have ars := iha safe.2
      cases hf : Tm.normalizeOne function with
      | mk fr fb =>
          cases ha : Tm.normalizeOne argument with
          | mk ar ab =>
              simp only [hf, ha] at fs ars
              cases fr <;> simp only [Tm.normalizeOne, hf, ha]
              all_goals first
                | exact ⟨fs, ars⟩
                | (apply protected_instantiate <;> assumption)
  | lam type body ih =>
      have bs := ih safe
      cases hb : Tm.normalizeOne body with
      | mk br bb =>
          simp only [hb] at bs
          cases br with
          | app function argument =>
              cases argument with
              | db index =>
                  cases index with
                  | zero =>
                      cases removed : Tm.dropAt? 0 function with
                      | none => simpa only [Tm.normalizeOne, hb, removed, Protected] using bs
                      | some result =>
                          simpa only [Tm.normalizeOne, hb, removed] using protected_drop bs.1 0 removed
                  | succ index => simp only [Tm.normalizeOne, hb, Protected] at bs ⊢ <;> exact bs
              | _ => simp only [Tm.normalizeOne, hb, Protected] at bs ⊢ <;> exact bs
          | _ => simp only [Tm.normalizeOne, hb, Protected] at bs ⊢ <;> exact bs
  | imp domain codomain ihd ihc => exact ⟨ihd safe.1, ihc safe.2⟩
  | all type body ih => exact ih safe
  | typeApp function type ih =>
      have fs := ih safe.2
      have scope := pass_scoped 0 safe.1
      cases hf : Tm.normalizeOne function with
      | mk fr fb =>
          simp only [hf] at fs scope
          cases fr <;> simp only [Tm.normalizeOne, hf]
          all_goals first
            | exact ⟨scope, fs⟩
            | exact protected_typeInstantiate fs.2 0 type
  | typeLam body ih =>
      have bs := ih safe.2
      have scope := pass_scoped 0 safe.1
      cases hb : Tm.normalizeOne body with
      | mk br bb =>
          simp only [hb] at bs scope
          cases br with
          | typeApp function type =>
              cases type with
              | var index =>
                  cases index with
                  | zero =>
                      cases removed : Tm.typeDropAt? 0 function with
                      | none =>
                          simpa only [Tm.normalizeOne, hb, removed, Protected] using And.intro scope bs
                      | some result =>
                          simpa only [Tm.normalizeOne, hb, removed] using protected_typeDrop bs.2 0 removed
                  | succ index =>
                      simpa only [Tm.normalizeOne, hb, Protected] using And.intro scope bs
              | _ => simpa only [Tm.normalizeOne, hb, Protected] using And.intro scope bs
          | _ => simpa only [Tm.normalizeOne, hb, Protected] using And.intro scope bs
  | typeAll body ih => exact ⟨pass_scoped 0 safe.1, ih safe.2⟩

theorem normalize_scoped {body result : Tm} (depth fuel : Nat) (scope : Scoped depth body)
    (normalized : Tm.normalize fuel body = some result) : Scoped depth result := by
  induction fuel generalizing body with
  | zero =>
      have kept := pass_scoped depth scope
      cases pass : Tm.normalizeOne body with
      | mk next stable =>
          simp only [pass] at kept
          cases stable <;> simp [Tm.normalize, pass] at normalized
          cases normalized
          exact kept
  | succ fuel ih =>
      have kept := pass_scoped depth scope
      cases pass : Tm.normalizeOne body with
      | mk next stable =>
          simp only [pass] at kept
          cases stable
          · exact ih kept (by simpa [Tm.normalize, pass] using normalized)
          · simp [Tm.normalize, pass] at normalized
            cases normalized
            exact kept

theorem normalize_protected {body result : Tm} (fuel : Nat) (safe : Protected body)
    (normalized : Tm.normalize fuel body = some result) : Protected result := by
  induction fuel generalizing body with
  | zero =>
      have kept := pass_protected safe
      cases pass : Tm.normalizeOne body with
      | mk next stable =>
          simp only [pass] at kept
          cases stable <;> simp [Tm.normalize, pass] at normalized
          cases normalized
          exact kept
  | succ fuel ih =>
      have kept := pass_protected safe
      cases pass : Tm.normalizeOne body with
      | mk next stable =>
          simp only [pass] at kept
          cases stable
          · exact ih kept (by simpa [Tm.normalize, pass] using normalized)
          · simp [Tm.normalize, pass] at normalized
            cases normalized
            exact kept

end Mettapedia.Languages.Megalodon.SourceScopeInvariant
