import Mettapedia.OSLF.NativeTypes.Runtime.Evidence
import Mettapedia.OSLF.NativeTypes.Runtime.Atoms
import Mettapedia.OSLF.NativeTypes.Executable

/-!
# Atomic observations and saved scoped lambda histories

These controls execute the public installed runtime. Exact-pattern atoms
have an independently specified equation-invariant meaning over intrinsically
scoped lambda terms. Mixed successors separate possibility from universality;
coincident targets preserve both congruence origins, and open-context beta
reduction preserves the free reference through capture-avoiding substitution.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Runtime.EvidenceControls

open Mettapedia.OSLF.Binding
open LambdaContextualRung LambdaScopedAuthoringComparison
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Runtime.Description (Meaning Readout)

def identity : Term sig [] .term := lamT (.var .zero)
def redex : Term sig [] .term := appT identity identity
def mixed : Term sig [] .term := appT redex redex
def mixedLeft : Term sig [] .term := appT identity redex
def selfApply : Term sig [] .term := lamT (appT (.var .zero) (.var .zero))
def omegaTerm : Term sig [] .term := appT selfApply selfApply
def duplicate : Term sig [] .term := appT omegaTerm omegaTerm
def captureSource : Term sig [.term] .term :=
  appT (lamT (lamT (.var (.succ .zero)))) (.var .zero)
def captureTarget : Term sig [.term] .term := lamT (.var (.succ .zero))
def capturedIncorrectly : Term sig [.term] .term := lamT (.var .zero)

def exactObservation (context : Ctx sig) (expected : Term sig context .term) :
    Atoms.Observation (Profiles.lambda {} context).native where
  predicate := ⟨fun source => encodeTerm source = encodeTerm expected, by
    intro source other related
    change source = other at related
    cases related
    rfl⟩
  accepts source := decide (encodeTerm source = encodeTerm expected)
  exact source := by simp only [decide_eq_true_eq]

def atomicAdmission (context : Ctx sig) :
    Mettapedia.OSLF.NativeTypes.Decision.Admission.LeafAdmission (Term sig context .term) where
  admitted expected := Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.Source context expected
  probe _ := .ok ()
  exact expected := ⟨fun _ => Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.source_admitted expected,
    fun _ => rfl⟩

def installed (context : Ctx sig) : Installed :=
  Atoms.installed (Profiles.lambda {} context) (exactObservation context) (atomicAdmission context)

def equalsFormula {context : Ctx sig} (expected : Term sig context .term) :
    (installed context).native.Formula := .atom (.inr expected)

def observe {context : Ctx sig} (formula : (installed context).native.Formula)
    (source : Term sig context .term) (budget : Nat) : Readout :=
  (Mettapedia.OSLF.NativeTypes.Executable.search (installed context) formula (encodeTerm source) budget).readout

def receipts {context : Ctx sig} (formula : (installed context).native.Formula)
    (source : Term sig context .term) (budget : Nat) :=
  (Mettapedia.OSLF.NativeTypes.Executable.search (installed context) formula (encodeTerm source) budget).observations.filter
    (fun observation => observation.location.isEmpty)

def targets {context : Ctx sig} (formula : (installed context).native.Formula)
    (source : Term sig context .term) (budget : Nat) : List Pattern :=
  (receipts formula source budget).map fun observation =>
    encodeTerm ((installed context).runtime.cursor.target observation.source observation.receipt)

def histories {context : Ctx sig} (formula : (installed context).native.Formula)
    (source : Term sig context .term) (budget : Nat) :=
  (receipts formula source budget).map (fun observation => observation.receipt.history)

def yes : Readout := .judgment (.decided true)
def no : Readout := .judgment (.decided false)
def pending : Readout := .judgment .unknown

#guard observe (equalsFormula identity) identity 3 == pending
#guard observe (equalsFormula identity) identity 4 == yes
#guard observe (equalsFormula redex) identity 4 == no
#guard observe (.conj (equalsFormula identity) (equalsFormula redex)) identity 20 == no
#guard observe (.disj (equalsFormula redex) (equalsFormula identity)) identity 20 == yes
#guard observe (.neg (equalsFormula redex)) identity 20 == yes
#guard observe (.imp (equalsFormula identity) (equalsFormula redex)) identity 20 == no
#guard observe (.imp (equalsFormula redex) .bottom) identity 20 == yes
#guard observe (.possibility (equalsFormula identity)) redex 100 == yes
#guard observe (.possibility (equalsFormula redex)) redex 100 == no
#guard observe (.outgoingUniversal (equalsFormula identity)) redex 100 == yes
#guard observe (.outgoingUniversal (equalsFormula redex)) redex 100 == no
#guard observe (.possibility (.possibility .top)) redex 100 == no
#guard observe (.outgoingUniversal (.neg (.possibility .top))) redex 100 == yes

#guard observe (.possibility (equalsFormula mixedLeft)) mixed 200 == yes
#guard observe (.outgoingUniversal (equalsFormula mixedLeft)) mixed 200 == no
#guard (receipts (.possibility (equalsFormula mixedLeft)) mixed 200).length == 1
#guard (receipts (.outgoingUniversal (equalsFormula mixedLeft)) mixed 200).length == 2
#guard targets (.possibility (equalsFormula mixedLeft)) mixed 200 == [encodeTerm mixedLeft]

#guard observe (.possibility (equalsFormula duplicate)) duplicate 500 == yes
#guard observe (.outgoingUniversal (equalsFormula duplicate)) duplicate 500 == yes
#guard targets (.outgoingUniversal (equalsFormula duplicate)) duplicate 500 ==
  [encodeTerm duplicate, encodeTerm duplicate]
#guard reprStr (histories (.outgoingUniversal (equalsFormula duplicate)) duplicate 500) ==
  reprStr ([.fire 2 [.step 0 0 (.fire 0 [])], .fire 3 [.step 0 0 (.fire 0 [])]] :
    List MeTTaIL.ScopedPremiseExecution.RuleHistory)
#guard (receipts (.possibility (equalsFormula duplicate)) duplicate 500).length == 1
#guard observe (.possibility (equalsFormula identity)) duplicate 500 == no
#guard (receipts (.possibility (equalsFormula identity)) duplicate 500).length == 2

#guard observe (.possibility (equalsFormula captureTarget)) captureSource 100 == yes
#guard observe (.possibility (equalsFormula capturedIncorrectly)) captureSource 100 == no
#guard targets (.possibility (equalsFormula captureTarget)) captureSource 100 == [encodeTerm captureTarget]
#guard !(targets (.possibility (equalsFormula capturedIncorrectly)) captureSource 100).contains
  (encodeTerm capturedIncorrectly)

theorem atomic_meaning_exact {context : Ctx sig} (expected : Term sig context .term) (raw : Pattern) :
    Meaning (installed context).native (equalsFormula expected) raw ↔
      ∃ source : Term sig context .term,
        Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.Source context source ∧
        encodeTerm source = raw ∧ encodeTerm source = encodeTerm expected :=
  Atoms.atomic_meaning (Profiles.lambda {} context).native
    (fun expected => (exactObservation context expected).test) (atomicAdmission context) expected raw

theorem exact_total_resume {context : Ctx sig} (formula : (installed context).native.Formula)
    (source : Term sig context .term) (first more : Nat) :
    Mettapedia.OSLF.NativeTypes.Executable.search (installed context) formula (encodeTerm source) (first + more) =
      Mettapedia.OSLF.NativeTypes.Executable.resume more
        (Mettapedia.OSLF.NativeTypes.Executable.search (installed context) formula (encodeTerm source) first) :=
  Mettapedia.OSLF.NativeTypes.Executable.search_resume (installed context) formula (encodeTerm source) first more

theorem total_budget_is_shared {context : Ctx sig} (formula : (installed context).native.Formula)
    (source : Term sig context .term) (budget : Nat) :
    (Mettapedia.OSLF.NativeTypes.Executable.search (installed context) formula (encodeTerm source) budget).spent ≤ budget :=
  Mettapedia.OSLF.NativeTypes.Executable.search_spent_le (installed context) formula (encodeTerm source) budget

theorem resumed_archive_preserves_order {context : Ctx sig} (formula : (installed context).native.Formula)
    (source : Term sig context .term) (first more : Nat) : ∃ suffix,
    (Mettapedia.OSLF.NativeTypes.Executable.resume more
      (Mettapedia.OSLF.NativeTypes.Executable.search (installed context) formula (encodeTerm source) first)).observations =
      (Mettapedia.OSLF.NativeTypes.Executable.search (installed context) formula (encodeTerm source) first).observations ++ suffix :=
  resume_observations_prefix more
    (Mettapedia.OSLF.NativeTypes.Executable.search (installed context) formula (encodeTerm source) first)

theorem every_positive_atomic_answer_has_native_meaning {context : Ctx sig}
    (expected source : Term sig context .term) (budget : Nat)
    (read : observe (equalsFormula expected) source budget = yes) :
    encodeTerm source = encodeTerm expected := by
  have holds := Mettapedia.OSLF.NativeTypes.Executable.search_positive (installed context)
    (equalsFormula expected) (encodeTerm source) budget read
  obtain ⟨actual, _, same, agrees⟩ := atomic_meaning_exact expected (encodeTerm source) |>.mp holds
  exact same.symm.trans agrees

theorem every_negative_atomic_answer_refutes_native_meaning {context : Ctx sig}
    (expected source : Term sig context .term) (budget : Nat)
    (read : observe (equalsFormula expected) source budget = no) :
    encodeTerm source ≠ encodeTerm expected := by
  have absent := Mettapedia.OSLF.NativeTypes.Executable.search_negative (installed context)
    (equalsFormula expected) (encodeTerm source) budget read
  intro same
  exact absent ((atomic_meaning_exact expected (encodeTerm source)).mpr
    ⟨source, Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.source_admitted source, rfl, same⟩)

theorem every_positive_modal_atom_has_saved_matching_receipt {context : Ctx sig}
    (expected source : Term sig context .term) (budget : Nat)
    (read : observe (.possibility (equalsFormula expected)) source budget = yes) :
    ∃ observation,
      observation ∈ (Mettapedia.OSLF.NativeTypes.Executable.search (installed context)
        (.possibility (equalsFormula expected)) (encodeTerm source) budget).observations ∧
      observation.location = [] ∧
      encodeTerm ((installed context).runtime.cursor.target observation.source observation.receipt) =
        encodeTerm expected := by
  obtain ⟨decoded, receipt, listed, saved, _, holds⟩ := Evidence.search_positive_receipt
    (installed context).native (installed context).runtime (equalsFormula expected) (encodeTerm source) budget read
  obtain ⟨actual, _, same, agrees⟩ :=
    (atomic_meaning_exact expected (encodeTerm ((installed context).runtime.cursor.target decoded.val receipt))).mp holds
  exact ⟨⟨decoded.val, receipt, listed, []⟩, saved, rfl, same.symm.trans agrees⟩

def decodedSource {context : Ctx sig} (source : Term sig context .term) :
    (installed context).native.Decoded (encodeTerm source) :=
  ⟨source, Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.source_admitted source, rfl⟩

theorem every_formed_formula_completes {context : Ctx sig}
    (formula : (installed context).native.Formula) (source : Term sig context .term)
    (formed : Mettapedia.OSLF.NativeTypes.Decision.Admission.Formed
      (installed context).native.generated.logicFragment (installed context).native.leafAdmission formula) :
    ∃ answer, (Mettapedia.OSLF.NativeTypes.Executable.check (installed context) formula (decodedSource source)
      (Mettapedia.OSLF.NativeTypes.Executable.decisionBound (installed context) formula (decodedSource source))).readout =
        .judgment (.decided answer) :=
  Mettapedia.OSLF.NativeTypes.Executable.check_complete (installed context) formula (decodedSource source)
    formed rfl _ (Nat.le_refl _)

end Mettapedia.OSLF.NativeTypes.Runtime.EvidenceControls
