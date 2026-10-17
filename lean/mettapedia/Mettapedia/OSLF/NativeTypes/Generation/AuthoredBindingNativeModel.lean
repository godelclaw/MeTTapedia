import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingModalDiagram
import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeModalQualification
import Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline

/-!
# Actual authored constructor and receipt interpretation

The admission checker qualifies the finite modal header catalogue and positive operational substitution profile. The initial model
retains its explicit empty named-free condition. The checked result
constructs the independent operational diagram in the same binding clone as
the original constructors. The common native evaluator and contextual model
then interpret those actual families without a supplied realization field.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredBindingNativeModel

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.TypeTheory.Calculi.NativeDependent
open Mettapedia.OSLF.NativeTypes.Modal
open CurriedBindingLanguage

def headers? (installed : BindingPipeline.Installed) :
    Option (∀ index : Fin installed.modal.length, NativeBindingModalAdmission.Admitted installed.modal[index]) :=
  NativeBindingModalAdmission.allFin? (fun index => NativeBindingModalAdmission.check? installed.modal[index])

structure Admitted (installed : BindingPipeline.Installed) : Prop where
  operational : NativeOperationalProfile.Admitted (BindingPipeline.environment installed.generated)
  headers : ∀ index : Fin installed.modal.length, Nonempty (NativeBindingModalAdmission.Admitted installed.modal[index])

def check (installed : BindingPipeline.Installed) : Bool :=
  NativeOperationalProfile.check (BindingPipeline.environment installed.generated) &&
    (headers? installed).isSome

theorem free_empty_iff (snapshot : Snapshot) :
    snapshot.free = FreeTypeContext.empty ↔ snapshot.freeTypes = [] := by
  constructor
  · intro same
    cases data : snapshot.freeTypes with
    | nil => rfl
    | cons entry rest =>
        have selected := congrFun same entry.1
        simp [Snapshot.free, data, FreeTypeContext.empty] at selected
  · intro empty
    funext name
    simp only [Snapshot.free, empty, List.find?_nil, Option.map_none, FreeTypeContext.empty]

def checkClosed (installed : BindingPipeline.Installed) : Bool :=
  (BindingPipeline.plan installed.generated).snapshot.freeTypes.isEmpty && check installed

theorem headers?_exact (installed : BindingPipeline.Installed) :
    (headers? installed).isSome = true ↔
      ∀ index : Fin installed.modal.length, Nonempty (NativeBindingModalAdmission.Admitted installed.modal[index]) := by
  constructor
  · intro checked
    cases decoded : headers? installed with
    | none => simp [decoded] at checked
    | some values => exact fun index => ⟨values index⟩
  · intro admitted
    have each : ∀ index : Fin installed.modal.length, ∃ value,
        NativeBindingModalAdmission.check? installed.modal[index] = some value :=
      fun index => NativeBindingModalAdmission.check?_complete (Classical.choice (admitted index))
    obtain ⟨values, decoded⟩ := NativeBindingModalAdmission.allFin?_complete
      (fun index => NativeBindingModalAdmission.check? installed.modal[index]) each
    change (headers? installed).isSome = true
    rw [show headers? installed = some values from decoded]
    rfl

theorem check_exact (installed : BindingPipeline.Installed) : check installed = true ↔ Admitted installed := by
  simp only [check, Bool.and_eq_true, NativeOperationalProfile.check_exact, headers?_exact]
  constructor
  · rintro ⟨operational, headers⟩
    exact ⟨operational, headers⟩
  · intro admitted
    exact ⟨admitted.operational, admitted.headers⟩

theorem checkClosed_exact (installed : BindingPipeline.Installed) :
    checkClosed installed = true ↔
      (BindingPipeline.plan installed.generated).snapshot.free = FreeTypeContext.empty ∧ Admitted installed := by
  simp only [checkClosed, Bool.and_eq_true, List.isEmpty_iff, check_exact, free_empty_iff]

private theorem decoded_member {plan : Plan} {origins : List (Modal.NativeEventDeclarations.Index plan)}
    {headers : List (NativeModalHeaders.Header plan)}
    (paired : List.Forall₂ (fun origin header => NativeModalHeaders.decode? plan origin = some header) origins headers) :
    ∀ header ∈ headers, ∃ origin, NativeModalHeaders.decode? plan origin = some header := by
  induction paired with
  | nil => intro header member; cases member
  | cons found rest ih =>
      intro header member
      cases List.mem_cons.mp member with
      | inl same => cases same; exact ⟨_, found⟩
      | inr member => exact ih header member

theorem header_decoded (installed : BindingPipeline.Installed) (index : Fin installed.modal.length) :
    NativeModalHeaders.decode? (BindingPipeline.plan installed.generated) installed.modal[index].origin =
      some installed.modal[index] := by
  have paired := NativeSignature.decodeList_sound installed.modalDecoded
  obtain ⟨origin, found⟩ := decoded_member paired installed.modal[index] (List.getElem_mem index.isLt)
  have actualOrigin := (NativeModalHeaders.decode_sound _ found).1
  rw [actualOrigin]
  exact found

private theorem allFin?_apply {n : Nat} {A : Fin n → Type}
    (candidate : ∀ index, Option (A index)) {values : ∀ index, A index}
    (found : NativeBindingModalAdmission.allFin? candidate = some values) :
    ∀ index, candidate index = some (values index) := by
  induction n with
  | zero => intro index; exact index.elim0
  | succ n ih =>
      cases firstFound : candidate 0 with
      | none => simp [NativeBindingModalAdmission.allFin?, firstFound] at found
      | some first =>
          cases restFound : NativeBindingModalAdmission.allFin?
              (A := fun index : Fin n => A index.succ)
              (fun index => candidate index.succ) with
          | none => simp [NativeBindingModalAdmission.allFin?, firstFound, restFound] at found
          | some rest =>
              have same : Fin.cases first rest = values := by
                simpa [NativeBindingModalAdmission.allFin?, firstFound, restFound] using found
              cases same
              intro index
              refine Fin.cases ?_ (fun index => ?_) index
              · exact firstFound
              · exact ih (fun index : Fin n => candidate index.succ) restFound index

/-- Decode the selected header without rebuilding the entire finite catalogue. -/
def checkedHeaders (installed : BindingPipeline.Installed) (checked : check installed = true)
    (index : Fin installed.modal.length) : NativeBindingModalAdmission.Admitted installed.modal[index] :=
  (NativeBindingModalAdmission.check? installed.modal[index]).get
    (Option.isSome_iff_exists.mpr ((NativeBindingModalAdmission.check?_exact _).mpr
      (((check_exact installed).mp checked).headers index)))

theorem checkedHeaders_decoded (installed : BindingPipeline.Installed)
    (checked : check installed = true) (index : Fin installed.modal.length) :
    NativeBindingModalAdmission.check? installed.modal[index] =
      some (checkedHeaders installed checked index) :=
  (Option.some_get _).symm

/-- Pointwise decoding returns exactly the prior whole-catalogue selection. -/
theorem checkedHeaders_catalogue (installed : BindingPipeline.Installed)
    (checked : check installed = true)
    (available : (headers? installed).isSome = true) :
    checkedHeaders installed checked = (headers? installed).get available := by
  funext index
  have selected := allFin?_apply
    (fun index => NativeBindingModalAdmission.check? installed.modal[index])
    (show NativeBindingModalAdmission.allFin?
      (fun index => NativeBindingModalAdmission.check? installed.modal[index]) =
        some ((headers? installed).get available) from (Option.some_get available).symm) index
  exact Option.some.inj ((checkedHeaders_decoded installed checked index).symm.trans selected)

noncomputable def diagram (installed : BindingPipeline.Installed) (freeEmpty : (BindingPipeline.plan installed.generated).snapshot.free = FreeTypeContext.empty)
    (checked : check installed = true) :
    CurriedNativeModalModel.Diagram (BindingPipeline.plan installed.generated) installed.modal :=
  NativeBindingModalDiagram.diagram freeEmpty
    ((check_exact installed).mp checked).operational installed.nativeMeaning_admitted
    installed.distinctLabels (header_decoded installed) (checkedHeaders installed checked)

noncomputable def model (installed : BindingPipeline.Installed) (freeEmpty : (BindingPipeline.plan installed.generated).snapshot.free = FreeTypeContext.empty)
    (checked : check installed = true) :
    Refinement.ModelData installed.symbols (Worlds (BindingPipeline.plan installed.generated).snapshot.language) :=
  CurriedNativeModalModel.model installed.declarations installed.nativeMeaning_admitted (diagram installed freeEmpty checked)

theorem realization (installed : BindingPipeline.Installed) (freeEmpty : (BindingPipeline.plan installed.generated).snapshot.free = FreeTypeContext.empty)
    (checked : check installed = true) :
    Refinement.SignatureRealization (model installed freeEmpty checked) installed.signature :=
  CurriedNativeModalModel.realization installed.declarations installed.nativeMeaning_admitted (diagram installed freeEmpty checked)

noncomputable def qualifiedTarget (installed : BindingPipeline.Installed) (freeEmpty : (BindingPipeline.plan installed.generated).snapshot.free = FreeTypeContext.empty)
    (checked : check installed = true) :
    Refinement.Contextual.Interpretation.QualifiedModel installed.signature
      (Refinement.NativeModel (Worlds (BindingPipeline.plan installed.generated).snapshot.language)) :=
  CurriedNativeModalModel.qualifiedModel installed.declarations installed.nativeMeaning_admitted
    (diagram installed freeEmpty checked)

noncomputable def closedDiagram (installed : BindingPipeline.Installed) (checked : checkClosed installed = true) :
    CurriedNativeModalModel.Diagram (BindingPipeline.plan installed.generated) installed.modal :=
  diagram installed ((checkClosed_exact installed).mp checked).1
    ((check_exact installed).mpr ((checkClosed_exact installed).mp checked).2)

theorem checked_native_sound (installed : BindingPipeline.Installed) (freeEmpty : (BindingPipeline.plan installed.generated).snapshot.free = FreeTypeContext.empty)
    (checked : check installed = true)
    (certificate : Certificates.Refinement.Certificate installed.signature)
    (judgment : Refinement.Judgment installed.symbols)
    (accepted : Certificates.Refinement.check certificate judgment = true) :
    Refinement.Interprets (model installed freeEmpty checked) judgment :=
  CurriedNativeModalModel.checked_native_sound installed.declarations installed.nativeMeaning_admitted
    (diagram installed freeEmpty checked) certificate judgment accepted

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredBindingNativeModel
