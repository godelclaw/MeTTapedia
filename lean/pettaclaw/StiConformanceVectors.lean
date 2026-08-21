import Lean
import StiMass

/-!
# Machine-readable STI conformance vectors

This executable emits canonical JSON Lines computed by `StiMass.exactStep`.
The vectors begin after host-side event classification and fixed-point
normalization: every salience and injection delta is already a `Nat` in micro
units.  Decimal-to-micro rounding is therefore an adapter concern, not part of
these vectors.
-/

open Lean
open StiMass

namespace StiConformanceVectors

structure VectorCase where
  name : String
  state : NamedState
  injections : List Injection

def params : ExactParams where
  micro := 1000000
  retained := 950000
  dmax := 300000
  cap := 980000
  micro_pos := by decide
  retained_le := by decide

def cases : List VectorCase :=
  [ { name := "zero"
      state := [("g1", 0)]
      injections := [] }
  , { name := "floor-one"
      state := [("g1", 1)]
      injections := [] }
  , { name := "dmax-clamp"
      state := [("g1", 0)]
      injections := [{ name := "g1", delta := 500000 }] }
  , { name := "cap-boundary"
      state := [("g1", 900000)]
      injections := [{ name := "g1", delta := 300000 }] }
  , { name := "missing-name"
      state := [("g1", 10)]
      injections := [{ name := "g2", delta := 7 }] }
  , { name := "repeated-injection"
      state := [("g1", 0)]
      injections :=
        [ { name := "g1", delta := 100000 }
        , { name := "g1", delta := 100000 }
        , { name := "g1", delta := 100000 }
        , { name := "g1", delta := 100000 } ] }
  , { name := "ordered-cap-and-drop"
      state := [("g1", 1), ("g2", 900000)]
      injections :=
        [ { name := "g2", delta := 300000 }
        , { name := "g3", delta := 7 } ] }
  ]

def namedValueToJson (entry : String × Nat) : Json :=
  Json.arr #[toJson entry.1, toJson entry.2]

def stateToJson (state : NamedState) : Json :=
  Json.arr (state.toArray.map namedValueToJson)

def injectionToJson (injection : Injection) : Json :=
  Json.mkObj
    [ ("name", toJson injection.name)
    , ("delta", toJson injection.delta) ]

def injectionsToJson (injections : List Injection) : Json :=
  Json.arr (injections.toArray.map injectionToJson)

def observationToJson (observation : StepObservation) : Json :=
  Json.mkObj
    [ ("applied", toJson observation.applied)
    , ("dropped", toJson observation.dropped)
    , ("admitted", toJson observation.admitted) ]

def paramsToJson (p : ExactParams) : Json :=
  Json.mkObj
    [ ("micro", toJson p.micro)
    , ("retained", toJson p.retained)
    , ("dmax", toJson p.dmax)
    , ("cap", toJson p.cap) ]

def vectorToJson (vector : VectorCase) : Json :=
  let result := exactStep params vector.state vector.injections
  Json.mkObj
    [ ("schema", toJson "sti-exact-step-v1")
    , ("case", toJson vector.name)
    , ("params", paramsToJson params)
    , ("input", Json.mkObj
        [ ("state", stateToJson vector.state)
        , ("injections", injectionsToJson vector.injections) ])
    , ("expected", Json.mkObj
        [ ("state", stateToJson result.state)
        , ("observation", observationToJson result.observation) ]) ]

def emit : IO Unit :=
  for vector in cases do
    IO.println (vectorToJson vector).compress

end StiConformanceVectors

def main : IO Unit :=
  StiConformanceVectors.emit
