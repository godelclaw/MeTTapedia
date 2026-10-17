import Mettapedia.Languages.MM0.MeTTa.Session.StreamProtocol
import Mettapedia.Languages.MM0.MeTTa.Formats.Textual.TextualDeclarations
import Mettapedia.Languages.MM0.MeTTa.Formats.Textual.TextualAuthoredSource
import Mettapedia.Languages.MM0.MeTTa.Formats.Textual.TextualParserLinkage
import Mettapedia.Languages.MM0.MeTTa.Formats.MMU.MMUSubmission
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.MMBProofRunSoundness
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.ExecutedSoundness
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.ProofRunExecution
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.TheoremExecution
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.TheoremCommandExecution
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.SlotExecution
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.AssertionMatchExecution
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.RecursiveMatchExecution
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.TheoremSignatureExecution

/-!
# The MM0 checker written in MeTTa

`Program` quotes the retained MeTTa files of the checker with their digests.
Every theorem below is about those quoted equations run in the PeTTa
semantics. The folders follow the layers of the program, and a module imports
only its own layer and earlier ones.

* `Data`: the data file. Encoding of MM0 data as atoms, naturals, the private
  stores, lists, tables, vectors and the inference cache.
* `Kernel`: checks on one term or one proof. Typing, substitution, variable
  dependencies and free variables, definition unfolding, conversion, and
  supplied proofs. `Proof.certificate_accepted_iff_petta_judgment` and
  `Proof.certificate_accepted_iff_gslt_path` say that a translated certificate
  of the `kernelCalculus` calculus is accepted exactly when the proof call succeeds.
* `Formation`: well-formed sorts, contexts, terms, dummies, definition bodies,
  statements and theorems.
* `Admission`: the stores allocated at start, and the admission of one
  declaration against the specification.
* `Session`: a whole run. The reset before each declaration, saved proofs, the
  drivers, and the request stream. `StreamProtocol.accepted_consumes_specification`
  says that a run printing true for every request has verified the whole
  specification, using exactly the specification's axioms.
* `Formats`: the readers that turn a file into requests.
  * `Textual`: how a `.mm0` specification projects to requests, the admission
    of the grammar's source files as rule presentations, and their link to the
    parser tables.
  * `MMU`: name resolution in the text proof format, and the submission loop
    reaching the session protocol.
  * `MMB`: the binary proof format run as a stack machine. Each machine step
    keeps typed stores and justified stack and heap entries
    (`MMBProofRunSoundness.step_preserves_evidence`). `ExecutedSoundness`
    connects original binary assertion/file acceptance to kernel derivability
    under independently established declaration correspondence.
    `ProofRunExecution` follows the actual quoted reference, save and
    hypothesis commands through finite runs, including refusal and untouched
    suffixes. `TheoremExecution` qualifies original theorem lookup, typed
    ordered child checking and chronological proof recording under the binary
    program; the complete binary theorem wrapper still needs its decoder,
    stack-consumption and structural-matching joins.

No theorem here covers the byte scanners or the rest of the readers'
execution.
-/
