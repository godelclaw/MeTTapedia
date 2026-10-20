import Mettapedia.Languages.MeTTa.PeTTa.ProgramQuotation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.OSLF.NativeTypes.Decision.Spatial.Execution

/-! # The shared spatial strategy as a pinned MeTTa program -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.SpatialRuntime

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Decision.Spatial Execution
open scoped ProgramQuotation

/-- A natural code for a Boolean keeps all cursor fields in the common wire carrier. -/
def boolTerm (value : Bool) : Term := .natural (if value then 1 else 0)

def leafTerm : BagModel.Leaf → Term
  | .emp => .symbol "NativeEmp"
  | .singleton value => .application "NativeSingle" [InferenceCettaWire.encodePattern value]

def formulaTerm : Expression → Term
  | .atom leaf => .application "NativeAtom" [leafTerm leaf]
  | .top => .symbol "NativeTop"
  | .bottom => .symbol "NativeBottom"
  | .conj left right => .application "NativeConj" [formulaTerm left, formulaTerm right]
  | .disj left right => .application "NativeDisj" [formulaTerm left, formulaTerm right]
  | .neg inner => .application "NativeNeg" [formulaTerm inner]
  | .imp left right => .application "NativeImpl" [formulaTerm left, formulaTerm right]
  | .possibility inner => .application "NativePossibly" [formulaTerm inner]
  | .outgoingUniversal inner => .application "NativeOutgoing" [formulaTerm inner]
  | .separating index left right => .application "NativeSep" [.natural index, formulaTerm left, formulaTerm right]

def bagTerm (bag : Bag) : Term := encodeList InferenceCettaWire.encodePattern bag

def splitTerm (pair : Bag × Bag) : Term := .application "Split" [bagTerm pair.1, bagTerm pair.2]

def splitsTerm (pairs : Splits) : Term := encodeList splitTerm pairs

def binaryTerm : Binary → Term
  | .conj => .symbol "NativeAnd"
  | .disj => .symbol "NativeOr"
  | .imp => .symbol "NativeImp"

def continuationTerm : Continuation → Term
  | .halt => .symbol "NativeHalt"
  | .negate next => .application "NativeNegate" [continuationTerm next]
  | .binaryLeft op right bag next => .application "NativeBinaryLeft"
      [binaryTerm op, formulaTerm right, bagTerm bag, continuationTerm next]
  | .binaryRight op left next => .application "NativeBinaryRight"
      [binaryTerm op, boolTerm left, continuationTerm next]
  | .splitLeft left right rightBag rest next => .application "NativeSplitLeft"
      [formulaTerm left, formulaTerm right, bagTerm rightBag, splitsTerm rest, continuationTerm next]
  | .splitRight left right result rest next => .application "NativeSplitRight"
      [formulaTerm left, formulaTerm right, boolTerm result, splitsTerm rest, continuationTerm next]
  | .splitRest found next => .application "NativeSplitRest" [boolTerm found, continuationTerm next]

def stateTerm : Execution.State → Term
  | .eval formula bag next => .application "NativeEval" [formulaTerm formula, bagTerm bag, continuationTerm next]
  | .choose left right remaining next => .application "NativeChoose"
      [formulaTerm left, formulaTerm right, splitsTerm remaining, continuationTerm next]
  | .ret result next => .application "NativeReturn" [boolTerm result, continuationTerm next]

def answerTerm : Option Bool → Term
  | some true => .symbol "NativeProved"
  | some false => .symbol "NativeRefuted"
  | none => .symbol "NativeUnknown"

def sessionTerm (session : Execution.Session) : Term :=
  .application "NativeSession" [formulaTerm session.formula, bagTerm session.bag, stateTerm session.cursor]

def unsupportedTerm (formula : Expression) (bag : Bag) : Term :=
  .application "NativeUnsupported" [formulaTerm formula, bagTerm bag]

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_native_spatial.metta"
    sha256 "d357c81ff18199655028c0795dbb3ed152e1bc24a30bb36c9f1f3f9dd79c098a"

def library : BridgeKit.Library := ⟨⟨[], [], [], [], []⟩, source.program, ["native:spatial:"]⟩

theorem library_checked : library.check = true := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.SpatialRuntime
