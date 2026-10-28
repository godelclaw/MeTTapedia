import Mettapedia.OSLF.MeTTaIL.GeneralPremiseProviderCongruence
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseControls

/-! Replacement rows can change query answers while retaining compiled
code. Bad rows still fail admission, and missing signatures change rule
selection instead of borrowing the old provider's authority. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.ProviderCongruenceControls

open Syntax GeneralPremise
open GeneralPremise.Controls

def guarded : RewriteRule := {child with
  premises := [.relationQuery "seen" [.fvar "X"]]}

def language : LanguageDef := {GeneralPremise.Controls.language with
  name := "query-snapshot-replacement", rewrites := [guarded]}

def snapshot (rows : List ProviderRow) (signatures : List Signature := provider.signatures) : Snapshot :=
  ⟨language,[],⟨signatures,rows,[]⟩⟩

def before : Snapshot := snapshot [⟨"seen",[zero]⟩]
def after : Snapshot := snapshot [⟨"seen",[.apply "Successor" [zero]]⟩]
def wrongRow : Snapshot := snapshot [⟨"seen",[.apply "Undeclared" []]⟩]
def missingSignature : Snapshot := snapshot [⟨"seen",[zero]⟩] []
def permissions : Permissions := {sites := .rootOnly,includeDerivedEquations := false}

#guard (compile before permissions).complete
#guard (compile after permissions).complete
#guard !(compile wrongRow permissions).complete
#guard !(compile missingSignature permissions).complete
#guard (compile before permissions).rules.length == 1
#guard (compile wrongRow permissions).rules.length == 1
#guard (compile missingSignature permissions).rules.isEmpty

theorem replacement_preserves_rules : (compile before permissions).rules = (compile after permissions).rules :=
  rules_congr rfl rfl permissions

theorem replacement_remains_admitted : (compile after permissions).complete = true :=
  complete_replace_provider (before := before) (after := after) rfl rfl rfl permissions
    (by decide_cbv) (by decide_cbv)

#print axioms replacement_preserves_rules
#print axioms replacement_remains_admitted

end Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.ProviderCongruenceControls
