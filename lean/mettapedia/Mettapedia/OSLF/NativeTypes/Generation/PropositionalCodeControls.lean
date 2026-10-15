import Mettapedia.OSLF.NativeTypes.Semantics.Sorted.PropositionalCodes
import Mettapedia.OSLF.NativeTypes.SortProfiles.Source.AdmissionControls
import Mettapedia.OSLF.NativeTypes.Structural.ObservationControls

open Mettapedia.OSLF.Framework

/-!
# Native propositional formation and sort-relative separation controls

The two actual typed constants inhabit different nonempty interpreted sort
subobjects. Generated top and complement respect those subobjects. The
formation checker distinguishes a disabled connective, a wrong universe input,
and a formed expression with no inhabitants.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodeControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation (Generated)
open Mettapedia.OSLF.NativeTypes.Modal.Rules (TypeCode)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Source (LeafCodes)
open Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes (Expression)
open Mettapedia.OSLF.NativeTypes.Semantics.Sorted.PropositionalCodes
open ModalHypercube (HSort)

open Mettapedia.OSLF.NativeTypes.SortProfiles.Source.AdmissionControls (generated carrier first second)

def interpretation : SortInterpretation generated [] where
  sortDomain type sort term :=
    HasType generated.snapshot.language generated.snapshot.free [] term type ∧
      term = match sort with | .star => first | .box => second
  carrierBounded _ _ _ inhabited := inhabited.1

def nativeLeaf (sort : HSort) : TypeCode generated.plan [] carrier sort where
  meaning := interpretation.sortDomain carrier sort
  bounded term inhabited := interpretation.carrierBounded carrier sort term inhabited

def leaves : LeafCodes generated [] := fun index =>
  let sort := if index = 1 then HSort.box else HSort.star
  ⟨carrier, sort, nativeLeaf sort⟩

theorem first_typed : HasType generated.snapshot.language generated.snapshot.free [] first carrier := by
  apply checkHasType_sound
  cbv

theorem second_typed : HasType generated.snapshot.language generated.snapshot.free [] second carrier := by
  apply checkHasType_sound
  cbv

theorem both_sort_subobjects_nonempty :
    interpretation.sortDomain carrier .star first ∧
      interpretation.sortDomain carrier .box second :=
  ⟨⟨first_typed, rfl⟩, ⟨second_typed, rfl⟩⟩

theorem sort_subobjects_separate_actual_terms :
    ¬ interpretation.sortDomain carrier .star second ∧
      ¬ interpretation.sortDomain carrier .box first := by
  have distinct : first ≠ second := by decide +kernel
  constructor
  · intro inhabited
    exact distinct inhabited.2.symm
  · intro inhabited
    exact distinct inhabited.2

theorem star_top_forms :
    ∃ output, compile generated [] interpretation leaves carrier .star .top = .ok output ∧
      output.expression = .top :=
  formation_complete _ _ _ _ _ _ _ (.top rfl)

theorem box_top_forms :
    ∃ output, compile generated [] interpretation leaves carrier .box .top = .ok output ∧
      output.expression = .top :=
  formation_complete _ _ _ _ _ _ _ (.top rfl)

theorem actual_star_top_readout {output : ClassifiedCode generated [] interpretation leaves carrier .star}
    (checked : compile generated [] interpretation leaves carrier .star .top = .ok output) :
    output.code.meaning first ∧ ¬ output.code.meaning second := by
  constructor
  · exact (readout_exact checked first).mpr ⟨both_sort_subobjects_nonempty.1, trivial⟩
  · intro inhabited
    exact sort_subobjects_separate_actual_terms.1 ((readout_exact checked second).mp inhabited).1

theorem actual_box_top_readout {output : ClassifiedCode generated [] interpretation leaves carrier .box}
    (checked : compile generated [] interpretation leaves carrier .box .top = .ok output) :
    output.code.meaning second ∧ ¬ output.code.meaning first := by
  constructor
  · exact (readout_exact checked second).mpr ⟨both_sort_subobjects_nonempty.2, trivial⟩
  · intro inhabited
    exact sort_subobjects_separate_actual_terms.2 ((readout_exact checked first).mp inhabited).1

theorem complement_of_star_leaf_forms :
    ∃ output, compile generated [] interpretation leaves carrier .star (.negation (.leaf 0)) = .ok output ∧
      output.expression = .negation (.leaf 0) := by
  apply formation_complete
  exact .negation rfl (.leaf 0 rfl rfl)

theorem star_complement_does_not_admit_box_term
    {output : ClassifiedCode generated [] interpretation leaves carrier .star}
    (checked : compile generated [] interpretation leaves carrier .star (.negation (.leaf 0)) = .ok output) :
    ¬ output.code.meaning second := by
  intro inhabited
  exact sort_subobjects_separate_actual_terms.1 ((readout_exact checked second).mp inhabited).1

theorem carrier_only_complement_would_admit_box_term :
    Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes.meaning generated [] leaves carrier
      (.negation (.leaf 0)) second := by
  refine ⟨second_typed, ?_⟩
  exact sort_subobjects_separate_actual_terms.1

theorem wrong_universe_is_formation_refusal :
    Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes.compilePropositionalCode generated [] leaves carrier .box (.leaf 0) =
      .error .incompatibleCarrierOrUniverse := by
  apply Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes.mixed_universe_leaf_rejected
  decide +kernel

theorem bottom_forms_but_is_uninhabited :
    ∃ output, compile generated [] interpretation leaves carrier .star .bottom = .ok output ∧
      ∀ term, ¬ output.code.meaning term := by
  obtain ⟨output, checked, _⟩ :=
    formation_complete generated [] interpretation leaves carrier .star .bottom (.bottom rfl)
  refine ⟨output, checked, ?_⟩
  intro term inhabited
  exact ((readout_exact checked term).mp inhabited).2

theorem disabled_negation_is_not_false :
    Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes.compilePropositionalCode Mettapedia.OSLF.NativeTypes.Structural.ObservationControls.generated []
      (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.AdmissionControls.leaves Mettapedia.OSLF.NativeTypes.Structural.ObservationControls.generated)
      Mettapedia.OSLF.NativeTypes.Structural.ObservationControls.carrier .star (.negation .top) =
        .error (.unavailable .negation) :=
  Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes.disabled_negation_refused _ _ _ _ _ _
    Mettapedia.OSLF.NativeTypes.Structural.ObservationControls.generated_fragment_has_no_negation

end Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodeControls
