import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppend

/-! # One program for authored append and its spatial observations

Ordered library agreement transports both component executions into the
concatenated program. The adapter observes length while retaining the original
array. Its packets are reached by execution; arbitrary submitted packets are
not certified by these declarations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppendExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.NativeTypes.Decision.Spatial
open MeTTaIL WireKit BridgeKit Eval
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram := petta_source_file%
  "../../../../../../../../metta/gslt/lib/gslt_inductive_observations.metta"
  sha256 "1be0b78eb1ac0509916db1ee33e88d117ea50a522757174388ae90bc00f19bf9"

def library : Library :=
  ⟨IndexedInductiveAppend.library.runtime.append SpatialRuntime.source.program,
    source.program, ["native:append:"]⟩

def emittedText : String := IndexedInductiveAppend.source.text ++ "\n" ++
  SpatialRuntime.source.text ++ "\n" ++ source.text

theorem library_checked : library.check = true := by decide +kernel

def appendHeads (head : String) : Bool := !head.startsWith "native:"
def spatialHeads (head : String) : Bool :=
  !(head.startsWith "gslt:inductive:" || head.startsWith "native:append:")

theorem append_closed : ProgramClosed appendHeads IndexedInductiveAppend.library.runtime :=
  closed_of_all _ _ (by decide +kernel) (by decide +kernel)

theorem spatial_closed : ProgramClosed spatialHeads SpatialRuntime.library.runtime :=
  closed_of_all _ _ (by decide +kernel) (by decide +kernel)

local instance : DecidableEq SpaceSemantics.Equation := fun first second =>
  match first, second with
  | ⟨head, arguments, body⟩, ⟨head', arguments', body'⟩ =>
    decidable_of_iff (head = head' ∧ arguments = arguments' ∧ body = body')
      (by simp only [SpaceSemantics.Equation.mk.injEq])

theorem append_agreement :
    ProgramAgreementOn appendHeads IndexedInductiveAppend.library.runtime library.runtime :=
  programAgreementOn_of_retained_rows _ _ _ (by decide +kernel) (by decide +kernel)

theorem spatial_agreement :
    ProgramAgreementOn spatialHeads SpatialRuntime.library.runtime library.runtime :=
  programAgreementOn_of_retained_rows _ _ _ (by decide +kernel) (by decide +kernel)

def packet (values : List Atom) (session : Execution.Session) : Atom :=
  apply "NativeAppendSession" [.expression values, encoded (SpatialRuntime.bagTerm session.bag),
    encoded (SpatialRuntime.sessionTerm session)]

def observation (values : List Atom) (session : Execution.Session) : Atom :=
  apply "NativeAppendObservation" [.expression values, encoded (SpatialRuntime.bagTerm session.bag),
    encoded (SpatialRuntime.sessionTerm session),
    encoded (SpatialRuntime.answerTerm (Execution.answer session.cursor))]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppendExecution
