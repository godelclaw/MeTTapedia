import Mettapedia.GraphTheory.FourColor.ClassicalCertificateRankVectorDag

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateRankVectorProduct

open ClassicalCertificateKempeClosure
open ClassicalCertificatePackedRankVector
open ClassicalCertificateRankVectorDag
open ClassicalCertificateTraceTree

/-- One rank-independent transfer object for a fixed boundary length.  Source
leaves store the ranks of launch words; response leaves store the least ranks
available in the corresponding chromogram fiber. -/
structure Certificate (length : Nat) where
  ranks : ClassicalCertificatePackedRankVector.Code
  traceCode : TraceCode
  sourceRoot : Nat
  responseCode : ResponseCode
  responseRoot : Nat

variable {length : Nat}

def responseLeafBoolean (certificate : Certificate length)
    (sourceVector : Nat) : Option Nat → Bool
  | none => false
  | some responseRoot =>
      match certificate.responseCode.nodeAt responseRoot with
      | .leaf responseVector =>
          respondsBoolean certificate.ranks sourceVector responseVector
      | _ => false

/-- Product traversal of the launch-word trie, chromogram trie, and
noncrossing stack automaton.  Every rank and every configuration are checked
at once by the terminal packed-vector comparison. -/
def productBoolean (certificate : Certificate length) :
    Nat → Nat → Option Nat → List Bool → Bool
  | 0, sourceRoot, responseRoot, stack =>
      match certificate.traceCode.nodeAt sourceRoot with
      | .leaf sourceVector =>
          if stack = [] then
            responseLeafBoolean certificate sourceVector responseRoot
          else true
      | _ => true
  | remaining + 1, sourceRoot, responseRoot, stack =>
      if stack.length > remaining + 1 then true
      else
        match certificate.traceCode.nodeAt sourceRoot with
        | .node red blue purple =>
            let recurse (sourceChild : Nat) (step : ChromogramStep)
                (nextStack : List Bool) :=
              productBoolean certificate remaining sourceChild
                (certificate.responseCode.child? responseRoot step) nextStack
            let redCheck := recurse red .skip stack
            let bluePushCheck := recurse blue .push (false :: stack)
            let purplePushCheck := recurse purple .push (true :: stack)
            match stack with
            | [] => redCheck && bluePushCheck && purplePushCheck
            | false :: rest =>
                redCheck && bluePushCheck && recurse blue .popSame rest &&
                  purplePushCheck && recurse purple .popOpposite rest
            | true :: rest =>
                redCheck && bluePushCheck && recurse blue .popOpposite rest &&
                  purplePushCheck && recurse purple .popSame rest
        | _ => true

def Certificate.checker (certificate : Certificate length) : Bool :=
  productBoolean certificate length certificate.sourceRoot
    (some certificate.responseRoot) []

end ClassicalCertificateRankVectorProduct

end Mettapedia.GraphTheory.FourColor
