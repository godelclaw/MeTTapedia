import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusResponseChecking
import Mathlib.Data.List.Pi

/-!
# Complete finite-rely certificates for generated focus classifiers

Each rely classifier is an explicit finite list of independently typed
contextual values. Its full product is computed and proved exhaustive.
A certificate supplies actual source programs and complete firing payloads;
every rely request must have an accepted response. Rejected certificates do
not refute membership. The target remains mandatory with zero rely slots.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FiniteFocusChecking

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.Modal
open NativeReceiptRechecking NativeBindingEventAction
open Mettapedia.GSLT.LanguageDef.WellSorted
open FocusMeaning

variable {installed : Joined.Installed} {index : installed.Index} {ambient : List String}

structure Parameters (installed : Joined.Installed) (index : installed.Index) (ambient : List String) where
  indices : (position : IndexPosition installed index) → IndexArgument installed index ambient position
  relies : (position : RelyPosition installed index) → List (RelyValue installed index ambient position)
  target : RelyValues installed index ambient → ScopedRuleMatching.Assignment → Pattern → Bool

def Parameters.meaning (parameters : Parameters installed index ambient) : Arguments installed index ambient :=
  ⟨parameters.indices, fun position value => value ∈ parameters.relies position,
    fun values assignment target => parameters.target values assignment target = true⟩

instance targetDecidable (parameters : Parameters installed index ambient) :
    ∀ values assignment target, Decidable (parameters.meaning.target values assignment target) :=
  fun _ _ _ => inferInstanceAs (Decidable (_ = true))

/-- The computation enumerates the dependent product of all rely domains. -/
def requests (parameters : Parameters installed index ambient) : List (RelyValues installed index ambient) :=
  (List.pi (List.finRange _) parameters.relies).map
    (fun row position => row position (List.mem_finRange position))

theorem requests_exact (parameters : Parameters installed index ambient)
    (values : RelyValues installed index ambient) :
    values ∈ requests parameters ↔ Requested parameters.meaning values := by
  constructor
  · intro member
    obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
    have entries := (List.mem_pi parameters.relies row).mp present
    exact fun position => entries position (List.mem_finRange position)
  · intro admitted
    apply List.mem_map.mpr
    refine ⟨fun position _ => values position, ?_, rfl⟩
    exact (List.mem_pi parameters.relies _).mpr (fun position _ => admitted position)

structure Witness where
  source : Pattern
  payload : Payload
  deriving DecidableEq, Repr

def accepts (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) (witness : Witness) : Bool :=
  (checkResponse parameters.meaning focus values witness.source witness.payload).isSome

theorem accepts_exact (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) (witness : Witness) :
    accepts parameters focus values witness = true ↔
      SourceResponse parameters.meaning focus values witness.source witness.payload :=
  checkResponse_exact parameters.meaning focus values witness.source witness.payload

def checkFocus (installed : Joined.Installed) (index : installed.Index)
    (ambient : List String) (focus : Pattern) : Bool :=
  let plan := BindingPipeline.plan installed.indexed.operational.generated
  checkHasType plan.snapshot.language plan.snapshot.free
    ((installed.indexed.schema index).focusBound ++ bound ambient) focus
    (installed.indexed.schema index).focusCarrier &&
  isObjectPattern focus && focus.hasCanonicalBinderMetadata

theorem checkFocus_exact (installed : Joined.Installed) (index : installed.Index)
    (ambient : List String) (focus : Pattern) :
    checkFocus installed index ambient focus = true ↔ FocusAdmitted installed index ambient focus := by
  simp only [checkFocus, Bool.and_eq_true, FocusAdmitted]
  constructor
  · rintro ⟨⟨typed, object⟩, canonical⟩
    exact ⟨checkHasType_sound typed, object, canonical⟩
  · rintro ⟨typed, object, canonical⟩
    exact ⟨⟨checkHasType_complete_of_object typed object, object⟩, canonical⟩

def check (parameters : Parameters installed index ambient) (focus : Pattern)
    (certificate : List Witness) : Bool :=
  checkFocus installed index ambient focus && (requests parameters).all fun values =>
    certificate.any (accepts parameters focus values)

/-- Exact certificate checking, including every rely result. This statement
uses source firings and does not define validity in terms of the checker. -/
theorem check_exact (parameters : Parameters installed index ambient) (focus : Pattern)
    (certificate : List Witness) : check parameters focus certificate = true ↔
    FocusAdmitted installed index ambient focus ∧
      ∀ values, Requested parameters.meaning values →
        ∃ witness ∈ certificate,
          SourceResponse parameters.meaning focus values witness.source witness.payload := by
  simp only [check, Bool.and_eq_true, checkFocus_exact, List.all_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨typed, all⟩
    refine ⟨typed, fun values requested => ?_⟩
    obtain ⟨witness, present, accepted⟩ := all values ((requests_exact parameters values).mpr requested)
    exact ⟨witness, present, (accepts_exact parameters focus values witness).mp accepted⟩
  · rintro ⟨typed, all⟩
    refine ⟨typed, fun values member => ?_⟩
    obtain ⟨witness, present, valid⟩ := all values ((requests_exact parameters values).mp member)
    exact ⟨witness, present, (accepts_exact parameters focus values witness).mpr valid⟩

theorem check_sound (parameters : Parameters installed index ambient) (focus : Pattern)
    (certificate : List Witness) (accepted : check parameters focus certificate = true) :
    Inhabits parameters.meaning focus := by
  obtain ⟨typed, all⟩ := (check_exact parameters focus certificate).mp accepted
  apply (inhabits_iff_source parameters.meaning focus).mpr
  refine ⟨typed, fun values requested => ?_⟩
  obtain ⟨witness, _, valid⟩ := all values requested
  exact ⟨witness.source, witness.payload, valid⟩

private theorem finite_witnesses {α β : Type} (inputs : List α) (relation : α → β → Prop)
    (provided : ∀ input ∈ inputs, ∃ witness, relation input witness) :
    ∃ witnesses : List β, ∀ input ∈ inputs, ∃ witness ∈ witnesses, relation input witness := by
  induction inputs with
  | nil => exact ⟨[], by simp⟩
  | cons first rest ih =>
      obtain ⟨witness, valid⟩ := provided first (List.mem_cons_self)
      obtain ⟨tail, covered⟩ := ih (fun input member => provided input (List.mem_cons_of_mem _ member))
      refine ⟨witness :: tail, ?_⟩
      intro input member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨witness, List.mem_cons_self, valid⟩
      · obtain ⟨found, present, good⟩ := covered input later
        exact ⟨found, List.mem_cons_of_mem _ present, good⟩

/-- Finite certificates suffice for the whole universal rely family.
Coverage is earned by `requests_exact`, not supplied as an interface field. -/
theorem certificate_exists_iff (parameters : Parameters installed index ambient) (focus : Pattern) :
    (∃ certificate, check parameters focus certificate = true) ↔ Inhabits parameters.meaning focus := by
  constructor
  · rintro ⟨certificate, accepted⟩
    exact check_sound parameters focus certificate accepted
  · intro inhabited
    obtain ⟨typed, all⟩ := (inhabits_iff_source parameters.meaning focus).mp inhabited
    obtain ⟨certificate, covered⟩ := finite_witnesses (requests parameters)
      (fun values (witness : Witness) =>
        SourceResponse parameters.meaning focus values witness.source witness.payload) (by
          intro values member
          obtain ⟨source, payload, valid⟩ := all values ((requests_exact parameters values).mp member)
          exact ⟨⟨source, payload⟩, valid⟩)
    refine ⟨certificate, (check_exact parameters focus certificate).mpr ⟨typed, ?_⟩⟩
    intro values requested
    exact covered values ((requests_exact parameters values).mpr requested)

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FiniteFocusChecking
