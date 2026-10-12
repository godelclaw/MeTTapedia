import Mettapedia.Languages.Metamath.DatabaseCheckerAuthority

/-!
# Executable whole-database checker audit

This build-time executable reads one Metamath database and submits its exact
bytes to the statusful database authority.  It reports only the SemanticService outcome;
the authority itself recomputes parsing, ordinary/compressed proof checking,
and incomplete-proof rejection.

Formerly `Mettapedia.Languages.Metamath.DatabaseNIKAudit`, part of the native inference kernel (NIK) development of 2026-08-11 to 2026-10-08; renamed to its subject name on 2026-10-08.
The namespace was `Mettapedia.Languages.Metamath.DatabaseNIKAudit`; it is now `Mettapedia.Languages.Metamath.DatabaseCheckerAudit`.
-/

namespace Mettapedia.Languages.Metamath.DatabaseCheckerAudit

open Mettapedia.GSLT.LanguageDef.SubmissionOutcomeProfile
open Mettapedia.Languages.Metamath.DatabaseCheckerAuthority

inductive AuditMode where
  | verifyDatabase
  | compileKnowledgeV1

def AuditMode.request (mode : AuditMode) (sourceBytes : ByteArray) :
    Request :=
  match mode with
  | .verifyDatabase => .verifyDatabase sourceBytes
  | .compileKnowledgeV1 => .compileKnowledgeV1 sourceBytes

def AuditMode.acceptedMessage (mode : AuditMode) : String :=
  match mode with
  | .verifyDatabase => "NIKMetamathDatabaseAccepted"
  | .compileKnowledgeV1 => "NIKMetamathKnowledgeV1Accepted"

def AuditMode.rejectedMessage (mode : AuditMode) : String :=
  match mode with
  | .verifyDatabase => "NIKMetamathDatabaseRejected"
  | .compileKnowledgeV1 => "NIKMetamathKnowledgeV1Rejected"

def main (arguments : List String) : IO UInt32 := do
  let (mode, sourcePath) : AuditMode × String <- match arguments with
    | [sourcePath] => pure (AuditMode.verifyDatabase, sourcePath)
    | ["--compile-knowledge-v1", sourcePath] =>
        pure (AuditMode.compileKnowledgeV1, sourcePath)
    | _ =>
        IO.eprintln
          "usage: DatabaseCheckerAudit [--compile-knowledge-v1] <database.mm>"
        return 2
  let sourceBytes <- IO.FS.readBinFile sourcePath
  match frontend.run (AuditMode.request mode sourceBytes) with
  | .accepted _ =>
      IO.println s!"{AuditMode.acceptedMessage mode} {sourceBytes.size}"
      return 0
  | .rejected _ =>
      IO.eprintln (AuditMode.rejectedMessage mode)
      return 1
  | .malformed =>
      IO.eprintln "NIKMetamathRequestMalformed"
      return 2
  | .unsupported =>
      IO.eprintln "NIKMetamathAuthorityUnsupported"
      return 2

end Mettapedia.Languages.Metamath.DatabaseCheckerAudit

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.Metamath.DatabaseCheckerAudit.main arguments
