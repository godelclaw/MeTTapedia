import Mettapedia.Languages.HOLLight.MeTTa.RulePrograms
import Mettapedia.Languages.HOLLight.MeTTa.InferenceScheduleControls
import Mettapedia.Languages.HOLLight.MeTTa.DefinitionHistory
import Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionCacheHistory
import Mettapedia.Languages.HOLLight.ExportReplayComposition

/-!
# Programmable primitive and extension examples from the HOL reference

Requests are generated with the existing source term, type, premise and
declaration renderers. The executable corpus evaluates the maintained MeTTa
checker in CeTTa, including whole-state resumption and policy controls. Its
serialized theorem records remain data, distinct from native owned handles.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.RuleProgramExamples

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.OpenTheory
open SourceReplay

def key (name : String) : Atom := .grounded (.string name)
def inert : Atom := .symbol "None"
def a : Ty := .var (Name.global "A")
def x : SourceTerm := .var (Name.global "x") a
def y : SourceTerm := .var (Name.global "y") a
def p : SourceTerm := .var (Name.global "p") Ty.bool
def f : SourceTerm := .var (Name.global "f") (.function a a)
def fx : SourceTerm := .app f x
def abstraction : SourceTerm := .abs (Name.global "y") a fx
def redex : SourceTerm := .app (.abs (Name.global "x") a x) x
def equation (type : Ty) (left right : SourceTerm) : SourceTerm :=
  .app (.app (.const Const.equality (Ty.equality type)) left) right

structure Case where
  name : String
  kind : InferenceKind
  payload : Atom := inert
  first : Atom := inert
  second : Atom := inert
  hypotheses : List SourceTerm := []
  conclusion : SourceTerm

def Case.command (item : Case) : Command :=
  ⟨key item.name, Premises.request item.kind item.payload item.first item.second⟩

def cases : List Case := [
  { name := "r", kind := .refl, payload := TermReading.sourceAtom x, conclusion := equation a x x },
  { name := "t", kind := .trans, first := key "r", second := key "r", conclusion := equation a x x },
  { name := "rf", kind := .refl, payload := TermReading.sourceAtom f,
    conclusion := equation (.function a a) f f },
  { name := "application", kind := .mkComb, first := key "rf", second := key "t",
    conclusion := equation a fx fx },
  { name := "abstract", kind := .abs, payload := TermReading.sourceAtom y, first := key "application",
    conclusion := equation (.function a a) abstraction abstraction },
  { name := "beta", kind := .beta, payload := TermReading.sourceAtom redex, conclusion := equation a redex x },
  { name := "assume", kind := .assume, payload := TermReading.sourceAtom p,
    hypotheses := [p], conclusion := p },
  { name := "deduct", kind := .deductAntisym, first := key "assume", second := key "assume",
    conclusion := equation Ty.bool p p },
  { name := "eq-mp", kind := .eqMp, first := key "deduct", second := key "assume",
    hypotheses := [p], conclusion := p },
  { name := "inst", kind := .inst,
    payload := Premises.keys [.expression [.symbol "HOL:Maplet", TermReading.sourceAtom y, TermReading.sourceAtom x]],
    first := key "t", conclusion := equation a y y },
  { name := "inst-type", kind := .instType,
    payload := TypeSubstitution.maplets Representation.registeredOperatorAtom [(Ty.bool, a)],
    first := key "r", conclusion := equation Ty.bool (.var (Name.global "x") Ty.bool) (.var (Name.global "x") Ty.bool) }]

theorem covers_primitives (kind : InferenceKind) : kind ∈ cases.map Case.kind := by
  cases kind <;> decide +kernel

def commands : List Command := cases.map Case.command

theorem command_readback : RulePrograms.readCommands (commandsAtom commands) = some commands :=
  RulePrograms.readCommands_commandsAtom commands

theorem repeated_occurrences : RuleData.readPremises (commands[1]'(by decide)).request =
    some [key "r", key "r"] := by decide +kernel

/-- The separate admitted mixed plan supplies a nonempty execution witness
for the generic retained-history theorem, starting from an empty cache. -/
theorem admitted_history (state : Mettapedia.Languages.MeTTa.PeTTa.Effects.State) :
    ∃ (added : CacheAuthorization.Cache) (recorded : List ReceiptKeys.Entry) (source : List Command),
      added.length = 3 ∧ recorded.length = 3 ∧ source.length = 3 ∧
      recorded.reverse.map RulePrograms.receiptCommand = source ∧
      (∀ receipt ∈ recorded, RuleData.readPremises receipt.request = some receipt.premises) ∧
      CacheAuthorization.Valid InferenceScheduleControls.frame.policy
        InferenceScheduleControls.frame.world added ∧
      Trace state (InferenceScheduleControls.frame.source [] []) source
        (InferenceScheduleControls.frame.source added recorded) := by
  simpa using RulePrograms.plan_trace_history InferenceScheduleControls.frame
    InferenceScheduleControls.mixedPlan (CacheAuthorization.empty_valid _ _) state

def form (name : String) (arguments : List Atom) : Atom := .expression (.symbol name :: arguments)
def check (actual expected : Atom) : String := "!" ++ toString (form "assertEqual" [actual, expected]) ++ "\n"
def yes : Atom := .symbol "True"
def no : Atom := .symbol "False"
def nil : Atom := .symbol "HOL:Nil"
def run (body : List Command) : Atom := form "hol-light:run" [nil, commandsAtom body]
def whole : Atom := form "program:whole" []

def step (name : String) (kind : InferenceKind) (payload : Atom := inert)
    (first : Atom := inert) (second : Atom := inert) : Command :=
  ⟨key name, Premises.request kind payload first second⟩

def identity : CheckedSourceTerm :=
  ⟨.abs (Name.global "z") Ty.bool (.var (Name.global "z") Ty.bool), .function Ty.bool Ty.bool,
    by simp [SourceTerm.inferType]⟩

def definitionCommands : List Command :=
  [⟨key "definition", DefinitionExecution.definitionRequest "identity" identity⟩,
    step "use-definition" .refl
      (TermReading.sourceAtom (.const (.mk (Name.global "identity") .undefined) identity.ty))]

def typeDefinitionCommands : List Command :=
  [step "exists" .refl (TermReading.sourceAtom identity.source),
    ⟨key "type-definition", TypeDefinitionFormation.command "carrier" "abstract" "represent" (key "exists")⟩]

def declaredType : Ty := .op (.mk (Name.global "sample") .undefined) []
def declarationCommands : List Command :=
  [⟨key "new-type", form "DECLARE_TYPE" [key "sample", .grounded (.int 0)]⟩,
    ⟨key "new-constant", DeclarationExecution.constantRequest "member" declaredType⟩,
    step "use-declaration" .refl
      (TermReading.sourceAtom (.const (.mk (Name.global "member") .undefined) declaredType))]

def axiomCommand : Command := ⟨key "axiom", form "AXIOM" [key "selected", TermReading.sourceAtom p]⟩
def commitments : Atom := Premises.keys [form "HOL:Entry" [key "selected", TermReading.sourceAtom p]]

def text : String :=
  "; Generated by RuleProgramExamples from the maintained source request constructors.\n" ++
  "!(import! &self ../../lib/hol_light/data.metta)\n" ++
  "!(import! &self ../../lib/hol_light/syntax.metta)\n" ++
  "!(import! &self ../../lib/hol_light/kernel.metta)\n" ++
  "!(import! &self ../../lib/hol_light/definitions.metta)\n" ++
  "!(import! &self ../../lib/hol_light/derived.metta)\n" ++
  "!(import! &self ../../lib/hol_light/receive.metta)\n" ++
  "(= (program:commands) " ++ toString (commandsAtom commands) ++ ")\n" ++
  "(= (program:execute) (let $commands (program:commands) (hol-light:run HOL:Nil $commands)))\n" ++
  "; Compute the source run once, then inspect its returned data in one workspace.\n" ++
  "!(bind! &program-results (new-space))\n" ++
  "!(let $result (program:execute) (add-atom &program-results (ProgramResult $result)))\n" ++
  "(= (program:whole) (match &program-results (ProgramResult $result) $result))\n" ++
  "(= (program:refl-then-repeat $term)\n" ++
  "   (HOL:Cons (HOL:Step \"r\" (REFL $term))\n" ++
  "     (HOL:Cons (HOL:Step \"t\" (TRANS \"r\" \"r\")) HOL:Nil)))\n" ++
  "!(let $builder (lam term (program:refl-then-repeat term))\n" ++
  "   (assertEqual ($builder " ++ toString (TermReading.sourceAtom x) ++ ") " ++
    toString (commandsAtom (commands.take 2)) ++ "))\n" ++
  "!(let $first (program:refl-then-repeat " ++ toString (TermReading.sourceAtom x) ++ ")\n" ++
  "   (assertEqual (hol-light:append $first " ++ toString (commandsAtom (commands.drop 2)) ++ ") (program:commands)))\n" ++
  String.join (cases.map fun item =>
    check (form "hol-light:check-result" [whole, key item.name,
      Premises.keys (item.hypotheses.map TermReading.sourceAtom), TermReading.sourceAtom item.conclusion]) yes ++
    check (form "hol-light:dependencies" [whole, key item.name]) nil ++
    check (form "hol-light:premise-count" [whole, key item.name])
      (.grounded (.int (Premises.occurrences item.kind item.first item.second).length))) ++
  "!(let (Some $middle) " ++ toString (run (commands.take 4)) ++ "\n" ++
  "   (assertEqual (hol-light:run-from $middle " ++ toString (commandsAtom (commands.drop 4)) ++ ") (program:whole)))\n" ++
  check (run [step "missing" .trans inert (key "absent") (key "absent")]) (.symbol "None") ++
  check (run (commands ++ [commands[0]'(by decide)])) (.symbol "None") ++
  check (form "hol-light:check-result" [whole, key "r", nil, TermReading.sourceAtom (equation a x y)]) no ++
  check (run [step "bad-beta" .beta (TermReading.sourceAtom (.app (.abs (Name.global "x") a x) y))]) (.symbol "None") ++
  check (run [step "assume-eq" .assume (TermReading.sourceAtom (equation a x x)),
    step "captured" .abs (TermReading.sourceAtom x) (key "assume-eq")]) (.symbol "None") ++
  check (form "hol-light:accepted" [run declarationCommands]) yes ++
  check (form "hol-light:dependencies" [run declarationCommands, key "use-declaration"]) nil ++
  check (run [⟨key "bad-type", form "DECLARE_TYPE" [key "sample", .grounded (.int (-1))]⟩]) (.symbol "None") ++
  check (form "hol-light:accepted" [run definitionCommands]) yes ++
  check (form "hol-light:check-result" [run definitionCommands, key "definition", nil,
    TermReading.sourceAtom (equation identity.ty (.const (.mk (Name.global "identity") .undefined) identity.ty)
      identity.source)]) yes ++
  check (run (definitionCommands ++ definitionCommands)) (.symbol "None") ++
  check (form "hol-light:accepted" [run typeDefinitionCommands]) yes ++
  check (form "hol-light:receipt-count" [run typeDefinitionCommands]) (.grounded (.int 3)) ++
  check (form "hol-light:premise-count" [run typeDefinitionCommands,
    TypeDefinitionFormation.representationKey (key "type-definition")]) (.grounded (.int 1)) ++
  check (form "hol-light:accepted" [form "hol-light:run" [commitments, commandsAtom [axiomCommand]]]) yes ++
  check (run [axiomCommand]) (.symbol "None") ++
  check (form "hol-light:dependencies" [form "hol-light:run" [commitments, commandsAtom [axiomCommand]], key "axiom"])
    (Premises.keys [form "HOL:AxiomDependency" [key "selected",
      form "HOL:Free" [key "p", TypeSubstitution.typeAtom Representation.registeredOperatorAtom Ty.bool]]])

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [output] => IO.FS.writeFile output text; pure 0
  | _ => IO.eprintln "usage: RuleProgramExamples <output.metta>"; pure 1

#print axioms covers_primitives
#print axioms admitted_history

end Mettapedia.Languages.HOLLight.MeTTa.RuleProgramExamples

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.HOLLight.MeTTa.RuleProgramExamples.main arguments
