import Mettapedia.Languages.GuardedAtomRule.Evidence

/-!
# Independent guarded atom-rule evidence client

`guardedAtomRuleCheck check FILE` reads native Atom requests with the existing source
reader. `check-root` and `check-call` check the complete supplied expanded
article; `expand-root` and `expand-call` are separate certificate producers.
The `checked` response gives acceptance, inspected rows, premise/root tests,
structural work and materialized endpoint-word volume. Those counts are not
host time and do not include reading, rule admission or endpoint encoding.

The declarations are exactly the submitted source rows and fixed Atom service
registration. A rejected article does not establish absence of other proofs.
Unknown requests retain their literal Atom. The profile is the independently
specified guarded atom-rule source judgment. It does not check HE or PeTTa
evaluation or give their nested-call semantics.

`check-wire FILE` uses the existing lossless Atom codec and finite alphabet;
its output is a lossless encoded response. This covers original fields which
have no ordinary source-reader spelling. Native-text output is a display,
not a claimed roundtrip printer. File-mode exit status reports protocol
processing; each `checked` response carries its own acceptance Boolean.

This is the Lean reference checker compiled by the Lean toolchain. It is not
a kernel written in a MeTTa dialect or a verified C implementation.
-/

set_option autoImplicit false

open Mettapedia.Languages.MeTTa

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.OSLF.NativeTypes.Certificates
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands
open Mettapedia.Languages.GuardedAtomRule.Evidence.Source

namespace Mettapedia.Languages.GuardedAtomRule.Evidence.Client

def a : Atom := .symbol "a"
def b : Atom := .symbol "b"
def x : Atom := .var "x"
def equation (lhs rhs : Atom) : Atom := .expression [.symbol "=", lhs, rhs]
def guarded (lhs rhs : Atom) (guards : List Atom) : Atom := .expression (.symbol "rule!" :: lhs :: rhs :: guards)
def fresh (name : String) (value : Atom) : Atom := .expression [.symbol "fresh", .var name, value]
def child (source target : Atom) : Atom := .expression [.symbol "==", source, target]
def query (relation : String) (arguments : List Atom) : Atom := .expression (.symbol relation :: arguments)
def tuple (kind relation : String) (arguments : List Atom) : Atom :=
  .expression (.symbol kind :: .symbol relation :: arguments)
def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)

def controls : List (String × List Atom × Conditional.Evidence × Atom × Option Atom) :=
  [ ("literal-equation", [equation a b], .firing 0 .empty, a, some b)
  , ("wrong-subject", [equation a b], .firing 0 .empty, b, none)
  , ("unknown-rule-ordinal", [equation a b], .firing 1 .empty, a, none)
  , ("symbol-is-not-nullary-expression", [equation (.expression [a]) b], .firing 0 .empty, a, none)
  , ("substitution-retains-both-occurrences", [equation x (.expression [x, x])], .firing 0 .empty, a,
      some (.expression [a, a]))
  , ("freshness-positive", [guarded a b [fresh "x" a]], .firing 0 (.cons .fresh .empty), a, some b)
  , ("freshness-negative", [guarded a b [fresh "x" x]], .firing 0 (.cons .fresh .empty), a, none)
  , ("missing-guard-proof", [guarded a b [fresh "x" a]], .firing 0 .empty, a, none)
  , ("recursive-child", [guarded a (.symbol "c") [child a b], equation a b],
      .firing 0 (.cons (.child (.firing 1 .empty)) .empty), a, some (.symbol "c"))
  , ("recursive-wrong-endpoint", [guarded a (.symbol "c") [child a a], equation a b],
      .firing 0 (.cons (.child (.firing 1 .empty)) .empty), a, none)
  , ("relation-output-binding", [guarded a x [query "r" [x]], tuple "relation!" "r" [b]],
      .firing 0 (.cons (.query (.relation 1)) .empty), a, some b)
  , ("builtin-row-binding", [guarded a x [query "r" [x]], tuple "builtin!" "r" [b]],
      .firing 0 (.cons (.query (.builtin 1)) .empty), a, some b)
  , ("wrong-relation-origin", [guarded a x [query "r" [x]], tuple "relation!" "r" [b]],
      .firing 0 (.cons (.query (.builtin 1)) .empty), a, none)
  , ("query-then-fresh-uses-captured-name", [guarded a x [query "r" [x], fresh "x" (.var "y")],
        tuple "relation!" "r" [.var "z"]],
      .firing 0 (.cons (.query (.relation 1)) (.cons .fresh .empty)), a, some (.var "z"))
  , ("query-then-fresh-refuses-captured-name", [guarded a x [query "r" [x], fresh "x" (.var "z")],
        tuple "relation!" "r" [.var "z"]],
      .firing 0 (.cons (.query (.relation 1)) (.cons .fresh .empty)), a, none)
  , ("native-fresh", [guarded a b [query "metta-atom-fresh-v1" [x, a]]],
      .firing 0 (.cons (.query (.native 0)) .empty), a, some b)
  , ("native-fresh-negative", [guarded a b [query "metta-atom-fresh-v1" [x, x]]],
      .firing 0 (.cons (.query (.native 0)) .empty), a, none)
  , ("native-fresh-bad-image", [guarded a b [query "metta-atom-fresh-v1" [a, b]]],
      .firing 0 (.cons (.query (.native 0)) .empty), a, none)
  , ("native-wrong-result-ordinal", [guarded a b [query "metta-atom-fresh-v1" [x, a]]],
      .firing 0 (.cons (.query (.native 1)) .empty), a, none)
  , ("unregistered-native-stays-unproved", [guarded a b [query "unregistered" [x, a]]],
      .firing 0 (.cons (.query (.native 0)) .empty), a, none)
  , ("native-value-cons", [guarded a (.var "out") [query "petta-match-value-v1"
        [ConfigurationEncoding.bindingsData [], .expression [.symbol "cons", x, .var "tail"],
          .expression [a, b], .var "out"]]],
      .firing 0 (.cons (.query (.native 0)) .empty), a,
      some (ConfigurationEncoding.bindingsData [("tail", .expression [b]), ("x", a)]))
  , ("native-value-repeat-refuses", [guarded a (.var "out") [query "petta-match-value-v1"
        [ConfigurationEncoding.bindingsData [], .expression [x, x], .expression [a, b], .var "out"]]],
      .firing 0 (.cons (.query (.native 0)) .empty), a, none)
  , ("native-binding-quoted-cons", [guarded a (.var "out") [query "petta-match-binding-v1"
        [ConfigurationEncoding.bindingsData [], .expression [.symbol "quote", .expression [.symbol "cons", x, .var "tail"]],
          .expression [.symbol "cons", a, b], .var "out"]]],
      .firing 0 (.cons (.query (.native 0)) .empty), a,
      some (ConfigurationEncoding.bindingsData [("tail", b), ("x", a)]))
  , ("native-value-first-binding-shadows", [guarded a (.var "out") [query "petta-match-value-v1"
        [ConfigurationEncoding.bindingsData [("x", a), ("x", b)], x, a, .var "out"]]],
      .firing 0 (.cons (.query (.native 0)) .empty), a,
      some (ConfigurationEncoding.bindingsData [("x", a), ("x", b)]))
  ]

def require (name : String) (held : Bool) : IO Unit := do
  unless held do throw (IO.userError ("failed: " ++ name))

private def testValue (name : String) (initial : Subst) (pattern value : Atom) (expected : Option Subst) : IO Nat := do
  let compiled := Primitive.expandValue? initial pattern value
  require (name ++ ":source") (compiled.map Prod.fst == expected)
  match compiled with
  | none => return 1
  | some (final, original) =>
      let article := Shared.Certificate.map (primitiveEmbedding []) original
      let raw := AtomWire.articleData article
      require (name ++ ":expanded-native-check") (AtomWire.check [] raw (.primitive (.value initial pattern value final)))
      require (name ++ ":expanded-native-roundtrip") ((AtomWire.read [] raw).map AtomWire.articleData == some raw)
      return 3

private def testBinding (name : String) (pattern value : Atom) (expected : Option Subst) : IO Nat := do
  let compiled := Primitive.expandBinding? [] pattern value
  require (name ++ ":source") (compiled.map Prod.fst == expected)
  match compiled with
  | none => return 1
  | some (final, original) =>
      let article := Shared.Certificate.map (primitiveEmbedding []) original
      require (name ++ ":expanded-native-check")
        (AtomWire.check [] (AtomWire.articleData article) (.primitive (.binding [] pattern value final)))
      return 2

private def primitiveControls : IO Nat := do
  let cons : Atom := .expression [.symbol "cons", x, .var "tail"]
  let repeated : Atom := .expression [x, x]
  let mut count := 0
  count := count + (← testValue "fresh-variable" [] x a (some [("x", a)]))
  count := count + (← testValue "captured-variable" [("x", a)] x a (some [("x", a)]))
  count := count + (← testValue "captured-variable-disagreement" [("x", a)] x b none)
  count := count + (← testValue "first-binding-shadows" [("x", a), ("x", b)] x a (some [("x", a), ("x", b)]))
  count := count + (← testValue "cons-head-tail" [] cons (.expression [a, b])
    (some [("tail", .expression [b]), ("x", a)]))
  count := count + (← testValue "cons-empty-refusal" [] cons (.expression []) none)
  count := count + (← testValue "repeated-variable-agreement" [] repeated (.expression [a, a]) (some [("x", a)]))
  count := count + (← testValue "repeated-variable-disagreement" [] repeated (.expression [a, b]) none)
  count := count + (← testValue "ordinary-constructor" [] (.expression [.symbol "constructor", x, .var "tail"])
    (.expression [.symbol "constructor", a, b]) (some [("tail", b), ("x", a)]))
  count := count + (← testBinding "quoted-cons-data" (.expression [.symbol "quote", cons])
    (.expression [.symbol "cons", a, b]) (some [("tail", b), ("x", a)]))
  count := count + (← testBinding "quoted-cons-not-native-list" (.expression [.symbol "quote", cons]) (.expression [a, b]) none)
  count := count + (← testBinding "ordinary-cons-native-list" cons (.expression [a, b])
    (some [("tail", .expression [b]), ("x", a)]))
  let original := Shared.emit (Primitive.deriveSubstitution [("x", .expression [a, b])] (.expression [x, x]))
  let article := Shared.Certificate.map (primitiveEmbedding []) original
  let raw := AtomWire.articleData article
  require "substitution-explicit-duplicate-output" (AtomWire.check [] raw
    (.primitive (.substitute [("x", .expression [a, b])] (.expression [x, x])
      (.expression [.expression [a, b], .expression [a, b]]))))
  require "substitution-wrong-output-refuses" (!AtomWire.check [] raw (.primitive (.substitute [("x", a)] x b)))
  return count + 2

private def runControls : IO UInt32 := do
  let mut count ← primitiveControls
  for (name, rows, evidence, subject, expected) in controls do
    let produced := AtomWire.expandRoot rows evidence subject
    require (name ++ ":original-endpoint") (produced.map Prod.fst == expected)
    count := count + 1
    match produced with
    | none => pure ()
    | some (target, article) =>
        require (name ++ ":native-article") (AtomWire.check rows article (.root evidence subject target))
        require (name ++ ":wrong-claim") (!AtomWire.check rows article (.root evidence subject (.symbol "forged")))
        require (name ++ ":changed-declaration-authority") (!AtomWire.check [] article (.root evidence subject target))
        require (name ++ ":canonical-read") ((AtomWire.read rows article).map AtomWire.articleData == some article)
        count := count + 4
  let rows := [equation a b]
  let evidence : Conditional.Evidence := .firing 0 .empty
  let some (target, raw) := AtomWire.expandRoot rows evidence a | throw (IO.userError "missing baseline")
  let some article := AtomWire.read rows raw | throw (IO.userError "cannot read baseline")
  let decision := Native.inspect rows raw (.root evidence a target)
  require "paid-accepted" (decision.any (·.decision.accepted))
  require "paid-quadratic-materialized-bound" (decision.any fun report =>
    report.decision.work ≤ (report.volume + 2) * (5 * report.volume + 10))
  require "native-request-dispatch" (match decision with
    | none => false
    | some report => Native.invoke (Native.rootRequest rows evidence a target raw) == Native.reportData report)
  let wrongRoot : AtomWire.Article rows := {article with root := article.rows.length}
  require "out-of-bounds-root" (!AtomWire.check rows (AtomWire.articleData wrongRoot) (.root evidence a target))
  let badUnused : Shared.Row (presentation rows) := ⟨.fresh [] "x" x, fun _ => 0⟩
  let corrupted : AtomWire.Article rows := {article with rows := article.rows ++ [badUnused]}
  require "invalid-unused-row" (!AtomWire.check rows (AtomWire.articleData corrupted) (.root evidence a target))
  let goodUnused : Shared.Row (presentation rows) := ⟨.premisesNil [], Fin.elim0⟩
  let augmented : AtomWire.Article rows := {article with rows := article.rows ++ [goodUnused]}
  require "valid-unused-row" (AtomWire.check rows (AtomWire.articleData augmented) (.root evidence a target))
  require "malformed-article" ((AtomWire.read rows (.expression [.symbol "article"])).isNone)
  require "extra-reference-refuses" ((AtomWire.readRow rows
    (.expression [.symbol "row", AtomWire.putRule (.premisesNil []), .expression [ConfigurationEncoding.index 0]])).isNone)
  require "missing-reference-refuses" ((AtomWire.readRow rows
    (.expression [.symbol "row", AtomWire.putRule (.fresh [] "x" a), .expression []])).isNone)
  let forward : AtomWire.Article rows := ⟨[⟨.fresh [] "x" a, fun _ => 1⟩,
      ⟨.primitive (.freshSymbol "x" "a"), Fin.elim0⟩], 0⟩
  require "forward-reference-refuses" (!AtomWire.check rows (AtomWire.articleData forward)
    (.premise .fresh (fresh "x" a) [] []))
  let unknown : Atom := .expression [.symbol "unknown-operation", a]
  require "unknown-request-retained" (Native.invoke unknown == unknown)
  require "symbol-nullary-wire-distinct" (AtomWire.articleData
      (Shared.emit (deriveAt rows [a] 0 a rfl)) != AtomWire.articleData
      (Shared.emit (deriveAt rows [.expression [a]] 0 (.expression [a]) rfl)))
  count := count + 12
  let duplicateRows := [equation a b, equation a b]
  let first := AtomWire.expandRoot duplicateRows (.firing 0 .empty) a
  let second := AtomWire.expandRoot duplicateRows (.firing 1 .empty) a
  require "duplicate-declarations-both-covered" (first.isSome && second.isSome)
  require "duplicate-declaration-occurrences-distinct" (first.map Prod.snd != second.map Prod.snd)
  count := count + 2
  let body := .expression [.symbol "quote", x]
  let callRows := [equation (call "f" [x]) body]
  let some ((ordinal, bindings, actualBody), callArticle) := AtomWire.expandCall callRows evidence "f" [a]
    | throw (IO.userError "missing callable")
  require "call-index" (ordinal == 0)
  require "call-original-body" (actualBody == body)
  require "call-bindings-retained-separately" (bindings == [("x", a)])
  require "call-native-check" (AtomWire.check callRows callArticle (.call "f" [a] evidence ordinal bindings body))
  require "call-pre-substituted-body-refuses" (!AtomWire.check callRows callArticle
    (.call "f" [a] evidence ordinal bindings (applySubst bindings body)))
  let callReply := Native.invoke (Native.callRequest callRows evidence "f" [a] ordinal bindings body callArticle)
  require "native-call-request-dispatch" (match callReply with
    | .expression [.symbol "checked", .grounded (.bool true), _, _, _, _] => true
    | _ => false)
  let callProducer : Atom := .expression [.symbol "expand-call", .expression callRows,
    MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands.Conditional.Wire.evidenceData evidence,
    .grounded (.string "f"), .expression [a]]
  require "native-call-producer-preserves-body-bindings" (match Native.invoke callProducer with
    | .expression [.symbol "expanded-call", actualOrdinal, actualBindings, actualBody, _] =>
        actualOrdinal == ConfigurationEncoding.index ordinal &&
        actualBindings == ConfigurationEncoding.bindingsData bindings && actualBody == body
    | _ => false)
  require "malformed-evidence-is-distinct" (match Native.invoke
      (.expression [.symbol "check-root", .expression rows, .symbol "bad-evidence", a, target, raw]) with
    | .expression [.symbol "malformed-request", _] => true
    | _ => false)
  count := count + 8
  let queryRows := [guarded a x [query "r" [x]], tuple "relation!" "r" [b], tuple "relation!" "r" [b]]
  let left := AtomWire.expandRoot queryRows (.firing 0 (.cons (.query (.relation 1)) .empty)) a
  let right := AtomWire.expandRoot queryRows (.firing 0 (.cons (.query (.relation 2)) .empty)) a
  require "duplicate-query-results-covered" (left.map Prod.fst == some b && right.map Prod.fst == some b)
  require "duplicate-query-occurrences-distinct" (left.map Prod.snd != right.map Prod.snd)
  let repeatedReferences : AtomWire.Article [] := ⟨[
    ⟨.primitive (.matchNil []), Fin.elim0⟩,
    ⟨.primitive (.matchCons [] [] [] (.expression []) (.expression []) [] []), fun _ => 0⟩], 1⟩
  require "repeated-premise-reference-valid" (AtomWire.check [] (AtomWire.articleData repeatedReferences)
    (.primitive (.structural [] (.expression [.expression []]) (.expression [.expression []]) [])))
  let repeatedRaw := AtomWire.articleData repeatedReferences
  require "repeated-premise-reference-retained" ((AtomWire.read [] repeatedRaw).map AtomWire.articleData == some repeatedRaw)
  count := count + 4
  let payloads : List Atom := [.symbol "True", .symbol "01", .symbol "name with spaces", .symbol "",
    .var "", .var "x🙂", .grounded (.string "quote\"\nbackslash\\"),
    .grounded (.custom "custom🙂" "payload\n"), .grounded (.int (-123)),
    .expression [.symbol "same", .symbol "same", .expression []]]
  for payload in payloads do
    let word := Native.encode payload
    require "lossless-original-Atom" (Native.onWord word == some payload)
    require "transport-trailing-refused" ((Native.onWord (word ++ [0])).isNone)
    require "transport-truncated-refused" ((Native.onWord (word.take (word.length - 1))).isNone)
    require "transport-text-roundtrip" (Mettapedia.OSLF.Binding.WireCodec.Binary.Text.parse
      (Mettapedia.OSLF.Binding.WireCodec.Binary.Text.render word) == some word)
    count := count + 4
  let sourceRequest := "(expand-root ((= a b)) (metta-proof-firing-v1 0 metta-proof-empty-v1) a)"
  require "original-reader-to-actual-expansion" (match Native.onText sourceRequest with
    | .ok [.expression [.symbol "expanded-root", actual, _]] => actual == b
    | _ => false)
  count := count + 1
  IO.println s!"PASS {count} guarded atom-rule controls"
  return 0

private def exportControls (directory : System.FilePath) : IO UInt32 := do
  IO.FS.createDirAll directory
  let mut manifest := ["file\texpected"]
  for (name, rows, evidence, subject, _) in controls do
    let produced := AtomWire.expandRoot rows evidence subject
    match produced with
    | none =>
        let request : Atom := .expression [.symbol "expand-root", .expression rows,
          MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands.Conditional.Wire.evidenceData evidence, subject]
        let file := name ++ ".metta"
        IO.FS.writeFile (directory / file) (toString request ++ "\n")
        manifest := manifest ++ [file ++ "\tno-expansion"]
    | some (target, article) =>
        let file := name ++ ".metta"
        IO.FS.writeFile (directory / file) (toString (Native.rootRequest rows evidence subject target article) ++ "\n")
        manifest := manifest ++ [file ++ "\tchecked-true"]
        let negativeFile := name ++ "-forged-target.metta"
        IO.FS.writeFile (directory / negativeFile)
          (toString (Native.rootRequest rows evidence subject (.symbol "forged") article) ++ "\n")
        manifest := manifest ++ [negativeFile ++ "\tchecked-false"]
  let rows := [equation a b]
  let evidence : Conditional.Evidence := .firing 0 .empty
  let target := b
  let special : List (String × Atom × String) :=
    [("malformed-article", Native.rootRequest rows evidence a target (.symbol "broken"), "malformed-article"),
     ("unknown-operation", .expression [.symbol "unknown-operation", a], "literal")]
  for (name, request, expected) in special do
    let file := name ++ ".metta"
    IO.FS.writeFile (directory / file) (toString request ++ "\n")
    manifest := manifest ++ [file ++ "\t" ++ expected]
  let callBody : Atom := .expression [.symbol "quote", x]
  let callRows := [equation (call "f" [x]) callBody]
  let some ((ordinal, bindings, body), article) := AtomWire.expandCall callRows evidence "f" [a]
    | throw (IO.userError "missing callable control")
  for (name, targetBody, expected) in [("call-quote", body, "checked-true"),
      ("call-forged-substituted-body", applySubst bindings body, "checked-false")] do
    let file := name ++ ".metta"
    IO.FS.writeFile (directory / file)
      (toString (Native.callRequest callRows evidence "f" [a] ordinal bindings targetBody article) ++ "\n")
    manifest := manifest ++ [file ++ "\t" ++ expected]
  let wireFile := "original-custom-Atom.metta-wire"
  let custom : Atom := .grounded (.custom "arbitrary tag🙂" "payload\n\"quoted\"")
  IO.FS.writeFile (directory / wireFile)
    (Mettapedia.OSLF.Binding.WireCodec.Binary.Text.render (Native.encode custom))
  manifest := manifest ++ [wireFile ++ "\tlossless-literal"]
  IO.FS.writeFile (directory / "controls.tsv") (String.intercalate "\n" manifest ++ "\n")
  IO.println s!"exported {manifest.length - 1} guarded atom-rule requests"
  return 0

private def checkFile (file : System.FilePath) : IO UInt32 := do
  match Native.onText (← IO.FS.readFile file) with
  | .error reason => IO.eprintln s!"reader: {reason}"; return 2
  | .ok replies =>
      for reply in replies do IO.println reply
      return 0

private def checkWire (file : System.FilePath) : IO UInt32 := do
  match Mettapedia.OSLF.Binding.WireCodec.Binary.Text.parse (← IO.FS.readFile file) with
  | none => IO.eprintln "invalid request alphabet"; return 2
  | some word =>
      match Native.onWord word with
      | none => IO.eprintln "noncanonical request"; return 2
      | some reply =>
          IO.println (Mettapedia.OSLF.Binding.WireCodec.Binary.Text.render (Native.encode reply))
          return 0

def run (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["controls"] => runControls
  | ["export-controls", directory] => exportControls directory
  | ["check", file] => checkFile file
  | ["check-wire", file] => checkWire file
  | _ =>
      IO.println "guardedAtomRuleCheck controls | export-controls DIRECTORY | check FILE | check-wire FILE"
      return 2

end Mettapedia.Languages.GuardedAtomRule.Evidence.Client

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.GuardedAtomRule.Evidence.Client.run arguments
