import Mettapedia.OSLF.MeTTaIL.GeneralFamilySnapshotKeys
import Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralRhoBinding

/-!
# Computational recognition of two complete source profiles

Recognition compares the complete authored snapshot and operational
permission data. Guard rows are decoded only to recover the original finite
provider list, preserving its order and duplicates. This does not restrict
the object-term syntax. The rho profile explicitly selects COMM declaration
zero and excludes authored and derived equation closure.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderFamily

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission EquationFrontierBinderProfile

def rowToken? (row : GeneralPremise.ProviderRow) : Option Token :=
  if row = ⟨"allow", [guard .permit]⟩ then some .permit
  else if row = ⟨"allow", [guard .reserve]⟩ then some .reserve
  else if row = ⟨"allow", [guard .revoked]⟩ then some .revoked
  else none

def candidate (source : Snapshot) : List Token := source.provider.rows.filterMap rowToken?

theorem row_decoded (token : Token) : rowToken? ⟨"allow", [guard token]⟩ = some token := by
  cases token <;> decide +kernel

theorem candidate_snapshot (allowed : List Token) :
    candidate (GeneralGuardedBinderAdmission.snapshot allowed) = allowed := by
  change (allowed.map (fun token => (⟨"allow", [guard token]⟩ : GeneralPremise.ProviderRow))).filterMap rowToken? = allowed
  induction allowed with
  | nil => rfl
  | cons token remaining ih => simp only [List.map_cons, List.filterMap_cons, row_decoded, ih]

def check (source : Snapshot) (permissions : Permissions) : Bool :=
  GeneralFamilySnapshotKeys.checkProfile source (GeneralGuardedBinderAdmission.snapshot (candidate source))
    permissions GeneralGuardedBinderAdmission.permissions

theorem check_iff (source : Snapshot) (permissions : Permissions) :
    check source permissions = true ↔
      ∃ allowed, source = GeneralGuardedBinderAdmission.snapshot allowed ∧
        permissions = GeneralGuardedBinderAdmission.permissions := by
  constructor
  · intro checked
    exact ⟨candidate source, (GeneralFamilySnapshotKeys.checkProfile_iff _ _ _ _).mp checked⟩
  · rintro ⟨allowed, rfl, rfl⟩
    unfold check
    rw [candidate_snapshot]
    exact (GeneralFamilySnapshotKeys.checkProfile_iff _ _ _ _).mpr ⟨rfl, rfl⟩

theorem compilation_checked {source : Snapshot} {permissions : Permissions}
    (checked : check source permissions = true) : (compile source permissions).complete = true := by
  obtain ⟨allowed, rfl, rfl⟩ := (check_iff source permissions).mp checked
  exact GeneralGuardedBinderAdmission.admission_complete allowed

theorem duplicate_rows_recognized :
    check (GeneralGuardedBinderAdmission.snapshot [.permit, .permit, .reserve])
      GeneralGuardedBinderAdmission.permissions = true :=
  (check_iff _ _).mpr ⟨_, rfl, rfl⟩

theorem changed_query_mode_rejected :
    check { GeneralGuardedBinderAdmission.snapshot [.permit] with
      provider := {GeneralGuardedBinderAdmission.providerSnapshot [.permit] with
        signatures := [⟨"allow", [.proc], [.output]⟩]} }
      GeneralGuardedBinderAdmission.permissions = false := by decide +kernel

theorem changed_permissions_rejected :
    check (GeneralGuardedBinderAdmission.snapshot [])
      {GeneralGuardedBinderAdmission.permissions with equationDirections := [.forward]} = false := by decide +kernel

#print axioms check_iff
#print axioms compilation_checked

end Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderFamily

namespace Mettapedia.OSLF.MeTTaIL.GeneralRhoFamily

open GeneralExecutionAdmission

def check (source : Snapshot) (permissions : Permissions) : Bool :=
  GeneralFamilySnapshotKeys.checkProfile source GeneralRho.snapshot permissions GeneralRho.permissions

theorem check_iff (source : Snapshot) (permissions : Permissions) :
    check source permissions = true ↔ source = GeneralRho.snapshot ∧ permissions = GeneralRho.permissions :=
  GeneralFamilySnapshotKeys.checkProfile_iff _ _ _ _

theorem compilation_checked {source : Snapshot} {permissions : Permissions}
    (checked : check source permissions = true) : (compile source permissions).complete = true := by
  obtain ⟨rfl, rfl⟩ := (check_iff source permissions).mp checked
  exact GeneralRho.compilation_complete

theorem original_comm_profile_recognized : check GeneralRho.snapshot GeneralRho.permissions = true :=
  (check_iff _ _).mpr ⟨rfl, rfl⟩

theorem reverse_quote_drop_closure_rejected :
    check GeneralRho.snapshot { GeneralRho.permissions with includeDerivedEquations := true } = false := by decide +kernel

#print axioms check_iff
#print axioms compilation_checked

end Mettapedia.OSLF.MeTTaIL.GeneralRhoFamily
