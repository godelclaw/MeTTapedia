import Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppendControls
import Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Bridges.IndexedInductiveAppend Controls
open Mettapedia.GSLT.LanguageDef.IndexedInductive

private def render (atom : Atom) : IO String :=
  match ReadAfterRender.render? atom with
  | some text => pure text
  | none => throw (IO.userError "fixture has no exact source rendering")

private def generate (directory : System.FilePath) (submitted : Option String := none) : IO Unit := do
  unless runtimeChecks && resumeCheck && rejectsChangedSource do
    throw (IO.userError "Lean execution/source controls failed")
  let some text := emit? AppendSource.IndexedNatVecAppend.module
    | throw (IO.userError "the authored append core was not admitted for specialization")
  if let some actual := submitted then
    unless actual == text do throw (IO.userError "submitted emission differs from the proved library")
  let text := submitted.getD text
  let mut controls := ""
  for fixture in fixtures do
    controls := controls ++ "!(let $packet (collapse " ++ (← render fixture.code) ++
      ") (println! (InductiveAppendPacket " ++ reprStr fixture.label ++ " $packet)))\n"
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory / "append-library.metta") text
  IO.FS.writeFile (directory / "append-controls.metta") controls
  IO.FS.writeFile (directory / "append-input.metta") (text ++ "\n" ++ controls)
  IO.FS.writeFile (directory / "append-payload-boundary.metta")
    (text ++ "\n!(let $packet (collapse " ++ (← render payloadBoundary.code) ++
      ") (println! (InductiveAppendBoundary $packet)))\n")
  IO.println s!"generated {fixtures.length} source-bound execution controls"

private def checkFixtures (marker : String) (expected : List Fixture) (text : String) : IO Unit := do
  let mut seen : List String := []
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith ("(" ++ marker) then
      let .ok atoms := SpaceSemantics.readSource line
        | throw (IO.userError "malformed result packet")
      let [.expression [.symbol actualMarker, .grounded (.string label), .expression answers]] := atoms
        | throw (IO.userError "wrong result packet shape")
      unless actualMarker == marker do throw (IO.userError "wrong result packet marker")
      if seen.contains label then throw (IO.userError s!"duplicate result packet: {label}")
      let some fixture := expected.find? (·.label == label)
        | throw (IO.userError s!"unexpected result packet: {label}")
      unless answers == fixture.answers do
        throw (IO.userError s!"wrong complete result packet: {label}")
      seen := label :: seen
    else if line != "" && line != "()" && line != "[()]" && line != "[]" &&
        line != "true" && line != "True" then
      throw (IO.userError s!"unexpected output: {line}")
  unless seen.length == expected.length do
    throw (IO.userError s!"missing result packets: got {seen.length}, expected {expected.length}")
  IO.println s!"{expected.length}/{expected.length} exact result packets accepted"

/-- Native lifetime stress uses the admitted append library and an ordinary
recursive client. Its independently computed packets check retained originals,
ordered growth and aliases. This is a runtime qualification workload, not a
general execution theorem for the recursive client or garbage collector. -/
private def lifetimeFixtures (rounds : Nat) : List Fixture := Id.run do
  let make (label : String) (count : Nat) (left right : List Int)
      (seed : Atom) : Fixture :=
    let original := left ++ right
    ⟨label, bind "original" seed
      (bind "grown" (call "native:array:grow" [num count, .var "original"])
        (bind "twice" (appendCall (.var "original") (.var "original"))
          (call "ArrayState" [.var "original", .var "grown", .var "twice"]))),
      [call "ArrayState" [array original, array (original ++ List.replicate count 0),
        array (original ++ original)]]⟩
  let large : Int := 340282366920938463463374607431768211456
  return [
    make "retained-small" 16 [3, 1, 1] [2] (appendCall (array [3, 1, 1]) (array [2])),
    make "retained-empty" 8 [] [] (appendCall (array []) (array [])),
    make "retained-large" rounds [large + 5, 1, 1] [2]
      (bind "large" (call "gslt:inductive:add" [num large, num 5])
        (appendCall (.expression [.var "large", num 1, num 1]) (array [2]))),
    make "alias-input" 16 [7, 7] [7, 7]
      (bind "shared" (appendCall (array [7]) (array [7]))
        (appendCall (.var "shared") (.var "shared")))]

private def lifetimeRounds (text : String) : IO Nat := do
  let some count := text.toNat? | throw (IO.userError "rounds must be a natural number")
  unless count > 0 do throw (IO.userError "lifetime pressure requires positive rounds")
  return count

private def generateLifetime (library directory : System.FilePath) (rounds : Nat) : IO Unit := do
  let some expected := emit? AppendSource.IndexedNatVecAppend.module
    | throw (IO.userError "the authored append core was not admitted for specialization")
  let submitted ← IO.FS.readFile library
  unless submitted == expected do throw (IO.userError "submitted emission differs from the proved library")
  let client := "\n(= (native:array:grow $n $values) " ++
    "(if (== $n 0) $values " ++
    "(let $next (gslt:inductive:append $values (0)) " ++
    "(native:array:grow (- $n 1) $next))))\n"
  let mut controls := ""
  for fixture in lifetimeFixtures rounds do
    controls := controls ++ "!(let $packet (collapse " ++ (← render fixture.code) ++
      ") (println! (ArrayLifetimePacket " ++ reprStr fixture.label ++ " $packet)))\n"
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory / "array-lifetime.metta") (submitted ++ client ++ controls)
  IO.println s!"generated {(lifetimeFixtures rounds).length} array lifetime controls"

def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["emit", directory] => generate directory
  | ["emit-library", library, directory] => generate directory (some (← IO.FS.readFile library))
  | ["check", path] => checkFixtures "InductiveAppendPacket" fixtures (← IO.FS.readFile path)
  | ["emit-lifetime", library, rounds, directory] =>
      generateLifetime library directory (← lifetimeRounds rounds)
  | ["check-lifetime", rounds, path] =>
      checkFixtures "ArrayLifetimePacket" (lifetimeFixtures (← lifetimeRounds rounds)) (← IO.FS.readFile path)
  | _ => throw (IO.userError "usage: qualify_inductive_append.lean emit DIRECTORY | emit-library LIBRARY DIRECTORY | check OUTPUT | emit-lifetime LIBRARY ROUNDS DIRECTORY | check-lifetime ROUNDS OUTPUT")
