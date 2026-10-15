import Mettapedia.Languages.MM0.Translation.FirstOrderControls
import Mettapedia.Languages.MM0.MeTTa.Admission.SpecificationMatching

/-!
Export an authored typed module, its certificates and independent expected
MM0 declarations. The MeTTa module backend generates the specification and
proof artifacts; this script supplies canonical source data and test cases.
It also exercises the human-facing Lean MM0/MMU/MM1 printer. No raw MM0 input
is parsed or prepared by this exporter.
-/

open Mettapedia.Languages.MM0
open Translation.FirstOrderControls
open Mettapedia.GSLT.LanguageDef
open ModuleAlgebra.SortedFirstOrderAuthoring InferenceCettaWire
open CertificateGSLT
open Translation.FirstOrderRules Translation.FirstOrderModules
open Mettapedia.OSLF.MeTTaIL.Syntax

def mutated (language : LanguageDef := quotedInferenceTheory.toLanguageDef)
    (rows : List SortedFirstOrderRules.Rule := implicationPresentation.rules)
    (exports : List String := ["wff", "set"]) (judgments : List String := ["wff"]) :
    QuotedInferenceTheory :=
  ⟨language, exports, judgments, rows⟩

def malformedSources : List (String × QuotedInferenceTheory) :=
  let language := quotedInferenceTheory.toLanguageDef
  let truthConstructor := (language.terms[0]?).get (by decide +kernel)
  [("DuplicateSort", mutated { language with «types» := language.types ++ [.plain "wff"] }),
   ("DuplicateConstructor", mutated { language with «terms» := language.terms ++ [truthConstructor] }),
   ("DuplicateRule", mutated (rows := implicationPresentation.rules ++ [truthIntroduction])),
   ("UnknownFormal", mutated (rows := [{ truthIntroduction with row :=
       { truthIntroduction.row with conclusion := .fvar "missing" } }])),
   ("UnusedBadPremise", mutated (rows := [{ truthIntroduction with row :=
       { truthIntroduction.row with premises := [.apply "emptySet" []] } }])),
   ("MissingFormalType", mutated (rows := [{ implicationIdentity with variableTypes := [] }])),
   ("WrongFormalSort", mutated (rows := [{ implicationIdentity with variableTypes := [.base "set"] }])),
   ("UnknownConstructor", mutated (rows := [{ truthIntroduction with row :=
       { truthIntroduction.row with conclusion := .apply "missing" [] } }])),
   ("UnknownJudgment", mutated (judgments := ["missing"])),
   ("UnknownExport", mutated (exports := ["missing"])),
   ("ObjectBinder", mutated { language with «terms» := [{ truthConstructor with
       params := [.abstraction "body" (.arrow (.base "wff") (.base "wff"))] }] }),
   ("ImplicitComputation", mutated { language with «terms» := [{ truthConstructor with
       evalPolicy? := some .oracle }] }),
   ("Equation", mutated { language with equations := [{
       name := "unexpected", typeContext := [], premises := [],
       left := .apply "truth" [], right := .apply "truth" [] }] }),
   ("Rewrite", mutated { language with rewrites := [{
       name := "unexpected", typeContext := [], premises := [],
       left := .apply "truth" [], right := .apply "truth" [] }] })]

def required (label : String) (value : Option String) : IO String :=
  match value with
  | some value => pure value
  | none => throw (IO.userError s!"Refused {label}")

def main (arguments : List String) : IO Unit := do
  let [output] := arguments | throw (IO.userError "usage: export_mm0_module_controls.lean OUTPUT_DIR")
  let directory : System.FilePath := output
  IO.FS.createDirAll directory
  let source ← required "module" (render? quotedInferenceTheory)
  let reorderedSource ← required "reordered module" (render? (mutated
    reorderedPresentation.syntaxSignature.language reorderedPresentation.rules))
  let goal : SortedFirstOrderRules.Rule :=
    { row := { id := "checked_goal", vars := [], premises := [], conclusion := .apply "truth" [] }
      variableTypes := [] }
  let openGoal : SortedFirstOrderRules.Rule :=
    { row := { id := "checked_goal", vars := ["ph"], premises := [.fvar "ph"], conclusion := .fvar "ph" }
      variableTypes := [.base "wff"] }
  let closedRow ← required "goal" (renderRule? goal)
  let openRow ← required "open goal" (renderRule? openGoal)
  let encode := fun proof => CettaTerm.render (encodeOpenProof proof)
  let truth := encode namedEliminationCertificate
  let openProof := encode (RawOpenProof.node ⟨⟨"modus_ponens"⟩, [.bvar 0, .bvar 0]⟩
    [.premise 0, namedIdentityCertificate (.bvar 0)])
  let swapped := encode (RawOpenProof.node ⟨⟨"modus_ponens"⟩, [.apply "truth" [], .apply "truth" []]⟩
    [namedIdentityCertificate (.apply "truth" []), namedTruthCertificate])
  let wrongSort := encode (RawOpenProof.node ⟨⟨"modus_ponens"⟩, [.apply "emptySet" [], .apply "truth" []]⟩
    [namedTruthCertificate, namedIdentityCertificate (.apply "truth" [])])
  let future := encode (RawOpenProof.node ⟨⟨"future_rule"⟩, []⟩ [])
  let expected := MeTTa.SpecificationMatching.pendingValue
    (implicationPresentation.theory.sorts.map (fun (index, value) => .sort index value) ++
     implicationPresentation.theory.terms.map (fun (index, value) => .term index value) ++
     implicationPresentation.theory.theorems.map (fun (index, value) => .axiomDecl index value))
  let emitted := "(= (module:fixture) " ++ source ++ ")\n" ++
    "(= (module:reordered) " ++ reorderedSource ++ ")\n" ++
    "(: module:certificate-refused (-> Atom Atom Atom %Undefined%))\n" ++
    "(= (module:certificate-refused $compiled $goal $proof)\n" ++
    "  (case $compiled\n" ++
    "    (((Some (MM0:CompiledModule $source $spec $commands $theory $sorts $terms $rules))\n" ++
    "      (== (mm0:module:check $compiled $goal $proof) False))\n" ++
    "     ($bad False))))\n" ++
    "!(let $source (module:fixture)\n  (let $compiled (mm0:module:compile $source)\n" ++
    "    (case $compiled\n      (((Some (MM0:CompiledModule $original $spec $commands $theory $sorts $terms $rules))\n" ++
    "        (println! (ModulePayloadExact (== $spec " ++ toString expected ++ "))))\n" ++
    "       ($bad (println! (ModulePayloadExact False)))))))\n" ++
    "!(let $source (module:fixture)\n  (let $compiled (mm0:module:compile $source)\n" ++
    "    (println! (ModuleClosed (mm0:module:check $compiled " ++ closedRow ++ " " ++ truth ++ ")))))\n" ++
    "!(let $source (module:fixture)\n  (let $compiled (mm0:module:compile $source)\n" ++
    "    (println! (ModuleOpen (mm0:module:check $compiled " ++ openRow ++ " " ++ openProof ++ ")))))\n" ++
    "!(let $source (module:fixture)\n  (let $compiled (mm0:module:compile $source)\n" ++
    "    (println! (ModuleSwapped (mm0:module:check $compiled " ++ closedRow ++ " " ++ swapped ++ ")))))\n" ++
    "!(let $source (module:fixture)\n  (let $compiled (mm0:module:compile $source)\n" ++
    "    (println! (ModuleWrongSort (mm0:module:check $compiled " ++ closedRow ++ " " ++ wrongSort ++ ")))))\n" ++
    "!(let $source (module:fixture)\n  (let $compiled (mm0:module:compile $source)\n" ++
    "    (println! (ModuleFuture (mm0:module:check $compiled " ++ closedRow ++ " " ++ future ++ ")))))\n" ++
    "!(let $source (module:reordered)\n  (let $compiled (mm0:module:compile $source)\n" ++
    "    (println! (ModuleReordered (mm0:module:check $compiled " ++ closedRow ++ " " ++ truth ++ ")))))\n"
  -- Unsupported data also exercises the native refusal boundary. The shared
  -- canonical renderer intentionally has no encoding for binders or equations.
  let unsupportedMutators :=
    "(= (module:object-binder (GSLTInferenceTheoryWireV1 (GSLTLanguageDefWireV1 $name $types $terms $eqs $steps) $exports $judgments $rules))\n" ++
    "  (GSLTInferenceTheoryWireV1 (GSLTLanguageDefWireV1 $name $types\n" ++
    "    (LCons (GrammarRule \"binding\" \"wff\" (LCons (TermAbstraction \"body\" (TBase \"wff\")) LNil) LNil EvalNone) LNil)\n" ++
    "    $eqs $steps) $exports $judgments $rules))\n" ++
    "(= (module:equation (GSLTInferenceTheoryWireV1 (GSLTLanguageDefWireV1 $name $types $terms $eqs $steps) $exports $judgments $rules))\n" ++
    "  (GSLTInferenceTheoryWireV1 (GSLTLanguageDefWireV1 $name $types $terms\n" ++
    "    (LCons UnsupportedEquation LNil) $steps) $exports $judgments $rules))\n"
  let mut refused := unsupportedMutators
  for (label, badSource) in malformedSources do
    if (admitQuotation? badSource).isSome then
      throw (IO.userError ("Malformed fixture unexpectedly admitted: " ++ label))
    let wire ← match render? badSource with
      | some wire => pure wire
      | none => match label with
        | "ObjectBinder" => pure "(module:object-binder $original)"
        | "Equation" => pure "(module:equation $original)"
        | _ => throw (IO.userError ("Unsupported fixture encoding: " ++ label))
    refused := refused ++ "!(let $original (module:fixture)\n  (let $wire " ++ wire ++
      "\n    (println! (ModuleSource" ++ label ++ " (== (mm0:module:compile $wire) None)))))\n"
  let badOpen := ["-1", "0.5", "\"1\"", "1"]
  for (index, badIndex) in badOpen.zipIdx do
    refused := refused ++ "!(let $source (module:fixture)\n  (let $compiled (mm0:module:compile $source)\n" ++
      "    (println! (ModuleBadHyp" ++ toString badIndex ++
      " (module:certificate-refused $compiled " ++ openRow ++ " (GOpenHyp " ++ index ++ "))))))\n"
  let wrongGoal := { goal with row := { goal.row with
    conclusion := .apply "imp" [.apply "truth" [], .apply "truth" []] } }
  let wrongRow ← required "wrong root" (renderRule? wrongGoal)
  refused := refused ++ "!(let $source (module:fixture)\n  (let $compiled (mm0:module:compile $source)\n" ++
    "    (println! (ModuleWrongRoot (module:certificate-refused $compiled " ++ wrongRow ++ " " ++ truth ++ ")))))\n"
  IO.FS.writeFile (directory / "module-controls.metta") (emitted ++ refused)
  IO.FS.writeFile (directory / "expected-controls.txt")
    ("(ModulePayloadExact true)\n(ModuleClosed true)\n(ModuleOpen true)\n" ++
     "(ModuleSwapped false)\n(ModuleWrongSort false)\n(ModuleFuture false)\n(ModuleReordered true)\n" ++
     String.join (malformedSources.map (fun (label, _) => "(ModuleSource" ++ label ++ " true)\n")) ++
     String.join ((List.range badOpen.length).map (fun index => "(ModuleBadHyp" ++ toString index ++ " true)\n")) ++
     "(ModuleWrongRoot true)\n")
  let artifactsDirectory := directory / "native-artifacts"
  IO.FS.createDirAll artifactsDirectory
  let emitArtifacts := fun (stem row proof : String) =>
    "!(let $source (module:fixture)\n  (let $compiled (mm0:module:compile $source)\n" ++
    "    (let $artifact (mm0:module:artifacts $compiled " ++ row ++ " " ++ proof ++ ")\n" ++
    "      (case $artifact\n        (((Some (MM0:ModuleArtifacts $specification $proofFile))\n" ++
    "          (let* (($writtenSpec (fs:write " ++ reprStr (artifactsDirectory / s!"{stem}.mm0").toString ++ " $specification))\n" ++
    "                 ($writtenProof (fs:write " ++ reprStr (artifactsDirectory / s!"{stem}.mm1").toString ++ " $proofFile)))\n" ++
    "            (println! (ModuleArtifact " ++ reprStr stem ++ " $writtenSpec $writtenProof))))\n" ++
    "         ($bad (println! (ModuleArtifactRefused " ++ reprStr stem ++ " $bad))))))))\n"
  IO.FS.writeFile (directory / "module-artifacts.metta")
    (emitArtifacts "closed" closedRow truth ++ emitArtifacts "open" openRow openProof ++
     emitArtifacts "swapped" closedRow swapped ++ emitArtifacts "wrong-sort" closedRow wrongSort ++
     emitArtifacts "wrong-root" wrongRow truth ++
     (emitArtifacts "reordered" closedRow truth).replace "(module:fixture)" "(module:reordered)")
  let printed := directory / "printed"
  IO.FS.createDirAll printed
  let cases : List (String × List String × Kernel.TheoremDecl × Kernel.ProofWitness) :=
    [("closed", [], ⟨[], [], .term 0⟩, eliminationCertificate),
     ("open", ["ph"], ⟨[.regular 0 ∅], [.var 0], .var 0⟩, .hyp 0),
     ("swapped", [], ⟨[], [], .term 0⟩,
       .theoremApp 2 [.term 0, .term 0] [identityCertificate (.term 0), truthCertificate]),
     ("wrong-sort", [], ⟨[], [], .term 0⟩,
       .theoremApp 2 [.term 2, .term 0] [truthCertificate, identityCertificate (.term 0)])]
  for (stem, locals, declaration, witness) in cases do
    let spec ← required stem (Translation.FirstOrderPrinting.specification? implicationPresentation
      "checked_goal" locals declaration)
    let mmu ← required stem (Translation.FirstOrderPrinting.mmu? implicationPresentation
      "checked_goal" locals declaration witness)
    let mm1 ← required stem (Translation.FirstOrderPrinting.mm1? implicationPresentation
      "checked_goal" locals declaration witness)
    IO.FS.writeFile (printed / s!"{stem}.mm0") spec
    IO.FS.writeFile (printed / s!"{stem}.mmu") mmu
    IO.FS.writeFile (printed / s!"{stem}.mm1") mm1
  IO.println "Exported the canonical typed module, open certificates and independent expected specification."
