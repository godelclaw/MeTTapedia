import Mettapedia.OSLF.NativeTypes.Modal.ProgramAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralRhoTyping

open Mettapedia.OSLF.Framework

/-!
# Original rho COMM retains its open collection schema

The declaration-derived program-source readout admits the actual authored
COMM left side with its REST name intact. No closed substitute replaces the
rule to manufacture a typed schema, and arbitrary raw collection carriers
are not advertised as part of the finite program family.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.ProgramCarrierControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers

theorem original_source_retained : GeneralRho.comm.left = rhoCommRewrite.left := rfl

theorem open_rest_metadata_retained :
    ∃ elements, GeneralRho.comm.left = .collection .hashBag elements (some "rest") :=
  ⟨_, rfl⟩

theorem program_candidates_derived : programCandidates GeneralRho.language =
    [.base "Proc", .base "Name"] := by decide +kernel

theorem original_comm_classified : classifyingProgramSource? GeneralRho.language GeneralRho.comm = true :=
  by decide +kernel

theorem original_comm_supported : Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences.substitutionFree GeneralRho.comm.left = true := rfl

theorem actual_program_carrier_readout :
    programCarrierStatus GeneralRho.language GeneralRho.comm = .classified [.base "Proc"] :=
  by decide +kernel

theorem actual_program_source_typing :
    HasType GeneralRho.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree GeneralRho.comm) []
      GeneralRho.comm.left (.base "Proc") :=
  (program_status_sound actual_program_carrier_readout).2.2.2 _ List.mem_cons_self |>.2

theorem actual_program_carrier_candidate :
    TypeExpr.base "Proc" ∈ Mettapedia.OSLF.NativeTypes.Generation.Occurrences.sourceCandidates GeneralRho.language GeneralRho.comm :=
  classified_program_source_candidate original_comm_classified actual_program_source_typing

/-- The separate object-oriented carrier diagnostic does not gate or erase
the admitted schematic program result. -/
theorem object_diagnostic_is_separate :
    Mettapedia.OSLF.NativeTypes.Modal.SourceCarriers.carrierStatus GeneralRho.language GeneralRho.comm = .unclassifiedSource ∧
      programCarrierStatus GeneralRho.language GeneralRho.comm = .classified [.base "Proc"] :=
  ⟨rfl, actual_program_carrier_readout⟩

end Mettapedia.OSLF.NativeTypes.Modal.ProgramCarrierControls
