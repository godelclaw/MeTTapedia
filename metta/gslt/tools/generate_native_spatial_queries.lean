import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.SpatialSource

/-! Emit native formulas and input bags. The target computes every cursor and verdict. -/

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Decision.Spatial
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.SpatialRuntime
open Mettapedia.GSLT.LanguageDef.CettaWire

def b : Pattern := .apply "b" []
def a : Pattern := .apply "a" []

def query (name : String) (formula : Execution.Expression) (bag : Execution.Bag)
    (fuel : Nat) (expected : String) : String :=
  s!"!(let* (($packet (native:spatial:start {formulaTerm formula |>.render} {bagTerm bag |>.render} {fuel})) " ++
    s!"($result (native:spatial:read $packet))) (NativeSpatialControl {reprStr name} (if (== $result {expected}) NativePass NativeFail)))\n"

def complete (name : String) (formula : Execution.Expression) (bag : Execution.Bag) : String :=
  query name formula bag 1000 (answerTerm (some (Execution.evaluate formula bag))).render

def producer (name : String) (formula : Execution.Expression) (expected : String) : String :=
  "!(let* (($answers (collapse (match &self (Observation $origin $payload) (PApp $payload LNil)))) " ++
    "($bag (foldl-atom $answers LNil $acc $item (LCons $item $acc))) " ++
    s!"($packet (native:spatial:start {formulaTerm formula |>.render} $bag 1000)) " ++
    s!"($result (native:spatial:read $packet))) (NativeSpatialControl {reprStr name} (if (== $result {expected}) NativePass NativeFail)))\n"

def generate : String := Id.run do
  let exactTwo := BagModel.packet [b, b]
  let atLeastTwo := BagModel.atLeast b 2
  let empty := BagModel.packet []
  let mut result := "; Shared formula execution: all answers are computed in the target.\n"
  result := result ++ complete "exact-two" exactTwo [b,b]
  result := result ++ complete "missing-copy" exactTwo [b]
  result := result ++ complete "extra-copy" exactTwo [b,b,b]
  result := result ++ complete "wrong-value" exactTwo [a,b]
  result := result ++ complete "order-irrelevant" (BagModel.packet [a,b]) [b,a]
  result := result ++ complete "empty-bag" empty []
  result := result ++ complete "nonempty-not-empty" empty [b]
  result := result ++ complete "at-least-two" atLeastTwo [b,b,b]
  result := result ++ complete "at-least-two-fails" atLeastTwo [b]
  result := result ++ complete "conjunction" (.conj atLeastTwo (.neg empty)) [b,b]
  result := result ++ complete "disjunction" (.disj empty exactTwo) [b,b]
  result := result ++ complete "negation" (.neg exactTwo) [b]
  result := result ++ complete "implication" (.imp empty exactTwo) [b]
  result := result ++ query "zero-budget" exactTwo [b,b] 0 "NativeUnknown"
  result := result ++ query "interrupted" exactTwo [b,b] 3 "NativeUnknown"
  result := result ++ query "unsupported-modality" (.possibility .top) [] 1000 "NativeUnsupported"
  result := result ++ query "unsupported-index" (.separating 1 .top .top) [] 1000 "NativeUnsupported"
  result := result ++ "(Observation Origin1 \"b\")\n(Observation Origin2 \"b\")\n"
  result := result ++ producer "actual-source-two-origins" exactTwo "NativeProved"
  result := result ++ producer "actual-source-missing-submission" (BagModel.packet [b]) "NativeRefuted"
  result := result ++ producer "actual-source-extra-submission" (BagModel.packet [b,b,b]) "NativeRefuted"
  result := result ++ producer "actual-source-wrong-submission" (BagModel.packet [a,b]) "NativeRefuted"
  result := result ++ s!"!(let $packet (native:spatial:start {formulaTerm exactTwo |>.render} {bagTerm [b,b] |>.render} 3) (NativeSpatialCursor $packet))\n"
  return result

def resume (input : String) : Except String String := do
  let marker :=  "(NativeSpatialCursor "
  let lines := input.splitOn "\n" |>.filter (·.startsWith marker)
  let line ← match lines with
    | [line] => pure line
    | _ => throw "expected exactly one returned spatial cursor"
  if !line.endsWith ")" then throw "malformed cursor envelope"
  let packet := line.drop marker.length |>.toString |>.dropEnd 1 |>.toString
  let formula := formulaTerm (BagModel.packet [b,b]) |>.render
  let bag := bagTerm [b,b] |>.render
  pure (s!"!(let* (($next (native:spatial:resume 1000 {packet})) ($result (native:spatial:read $next))) " ++
    "(NativeSpatialControl \"resume-complete\" (if (== $result NativeProved) NativePass NativeFail)))\n" ++
    s!"!(let* (($next (native:spatial:resume 1000 {packet})) ($whole (native:spatial:start {formula} {bag} 1003))) " ++
    "(NativeSpatialControl \"resume-composition\" (if (== $next $whole) NativePass NativeFail)))\n" ++
    "!(let* (($next (native:spatial:resume 1 (NativeSession (NativePossibly NativeTop) LNil (NativeReturn 1 NativeHalt)))) " ++
    "($result (native:spatial:read $next))) (NativeSpatialControl \"resume-rechecks-admission\" (if (== $result NativeUnsupported) NativePass NativeFail)))\n")

def main (args : List String) : IO Unit := do
  match args with
  | [output] => IO.FS.writeFile output generate
  | ["resume", input, output] =>
    match resume (← IO.FS.readFile input) with
    | .ok script => IO.FS.writeFile output script
    | .error reason => throw (IO.userError reason)
  | _ => throw (IO.userError "usage: generate_native_spatial_queries.lean OUTPUT | resume INPUT OUTPUT")
