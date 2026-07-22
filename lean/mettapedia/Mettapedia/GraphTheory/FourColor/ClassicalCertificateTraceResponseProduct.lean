import Mettapedia.GraphTheory.FourColor.ClassicalCertificateIndexedLayeredKempe

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateTraceResponseProduct

open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateKempeClosure
open ClassicalCertificateRankedKempe
open ClassicalCertificateResponseDag
open ClassicalCertificateTraceDag
open ClassicalCertificateTraceTree

variable {length : Nat}

def responseChild? (code : ClassicalCertificateResponseDag.Code) :
    Option Nat → ChromogramStep → Option Nat
  | none, _ => none
  | some root, step =>
      match ClassicalCertificateResponseDag.nodeAt code root with
      | .node push skip popSame popOpposite =>
          some (ClassicalCertificateResponseDag.child
            push skip popSame popOpposite step)
      | _ => none

/-- One state in the product of a source trace language, the response
dictionary, and the noncrossing-matching stack automaton. -/
structure State where
  layer : Nat
  remaining : Nat
  sourceRoot : Nat
  responseRoot : Option Nat
  stack : List Bool
  deriving DecidableEq, Repr

/-- Validate the response leaf reached by one complete chromogram. -/
def responseLeafBoolean
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (layer : Nat) : Option Nat → Bool
  | none => false
  | some root =>
      match ClassicalCertificateResponseDag.nodeAt
          certificate.responseCode root with
      | .leaf index =>
          if index < ClassicalCertificateResponseDag.valueBound
              certificate.responseCode then
            match ClassicalCertificateResponseDag.valueAt?
                certificate.responseCode index with
            | some value => value.rank < layer
            | none => false
          else false
      | _ => false

def terminalBoolean
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (state : State) : Bool :=
  match ClassicalCertificateTraceDag.nodeAt certificate.traceCode
      state.sourceRoot with
  | .leaf =>
      if state.stack = [] then
        responseLeafBoolean certificate state.layer state.responseRoot
      else true
  | _ => true

def successorStates (certificate :
    ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (state : State) (remaining red blue purple : Nat) : List State :=
  let next (sourceRoot : Nat) (step : ChromogramStep)
      (stack : List Bool) : State :=
    ⟨state.layer, remaining, sourceRoot,
      responseChild? certificate.responseCode state.responseRoot step, stack⟩
  let base :=
    [next red .skip state.stack,
      next blue .push (false :: state.stack),
      next purple .push (true :: state.stack)]
  match state.stack with
  | [] => base
  | false :: rest =>
      base ++ [next blue .popSame rest, next purple .popOpposite rest]
  | true :: rest =>
      base ++ [next blue .popOpposite rest, next purple .popSame rest]

/-- A one-step view of the product recursion.  A result state is terminal or
vacuous; a child state always has strictly smaller remaining length. -/
def unfoldState
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (state : State) : Sum Bool (List State) :=
  match state.remaining with
  | 0 => .inl (terminalBoolean certificate state)
  | remaining + 1 =>
      if state.stack.length > remaining + 1 then .inl true
      else
        match ClassicalCertificateTraceDag.nodeAt certificate.traceCode
            state.sourceRoot with
        | .node red blue purple =>
            .inr (successorStates certificate state remaining red blue purple)
        | _ => .inl true

/-- Product traversal of a source trace language and the shared response
dictionary.  Every source/chromogram path is followed once; incomplete stack
paths are discarded at the terminal depth. -/
def productBoolean
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (layer : Nat) : Nat → Nat → Option Nat → List Bool → Bool
  | 0, sourceRoot, responseRoot, stack =>
      match ClassicalCertificateTraceDag.nodeAt certificate.traceCode
          sourceRoot with
      | .leaf =>
          if stack = [] then
            responseLeafBoolean certificate layer responseRoot
          else true
      | _ => true
  | remaining + 1, sourceRoot, responseRoot, stack =>
      if stack.length > remaining + 1 then true
      else
        match ClassicalCertificateTraceDag.nodeAt certificate.traceCode
            sourceRoot with
        | .node red blue purple =>
            let recurse (sourceChild : Nat) (step : ChromogramStep)
                (nextStack : List Bool) :=
              productBoolean certificate layer remaining sourceChild
                (responseChild? certificate.responseCode responseRoot step)
                nextStack
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

def layerBoolean
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (layer : Nat) : Bool :=
  productBoolean certificate layer length (certificate.rootAt layer)
    (some certificate.responseRoot) []

def evaluate
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (state : State) : Bool :=
  productBoolean certificate state.layer state.remaining state.sourceRoot
    state.responseRoot state.stack

/-- Finite proof trees for successful product states.  Proof-DAG checking
constructs these trees by well-founded sharing of smaller states. -/
inductive Derivation
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length) :
    State → Prop where
  | result {state : State} {value : Bool}
      (hunfold : unfoldState certificate state = .inl value)
      (hvalue : value = true) : Derivation certificate state
  | children {state : State} {children : List State}
      (hunfold : unfoldState certificate state = .inr children)
      (hchildren : ∀ child ∈ children, Derivation certificate child) :
      Derivation certificate state

theorem evaluate_eq_of_unfoldState_eq_inl
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (state : State) (value : Bool)
    (hunfold : unfoldState certificate state = .inl value) :
    evaluate certificate state = value := by
  rcases state with ⟨layer, remaining, sourceRoot, responseRoot, stack⟩
  cases remaining with
  | zero =>
      simpa [unfoldState, evaluate, productBoolean, terminalBoolean] using
        congrArg (fun result => Sum.getLeft? result) hunfold
  | succ remaining =>
      simp only [unfoldState] at hunfold
      by_cases hstack : stack.length > remaining + 1
      · simp [hstack] at hunfold
        simpa [evaluate, productBoolean, hstack] using hunfold
      · simp [hstack] at hunfold
        cases hnode : ClassicalCertificateTraceDag.nodeAt
            certificate.traceCode sourceRoot with
        | empty =>
            simp [hnode] at hunfold
            simpa [evaluate, productBoolean, hstack, hnode] using hunfold
        | leaf =>
            simp [hnode] at hunfold
            simpa [evaluate, productBoolean, hstack, hnode] using hunfold
        | node red blue purple => simp [hnode] at hunfold

theorem evaluate_eq_true_of_unfoldState_eq_inr
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (state : State) (children : List State)
    (hunfold : unfoldState certificate state = .inr children)
    (hchildren : children.all (evaluate certificate) = true) :
    evaluate certificate state = true := by
  rcases state with ⟨layer, remaining, sourceRoot, responseRoot, stack⟩
  cases remaining with
  | zero => simp [unfoldState] at hunfold
  | succ remaining =>
      simp only [unfoldState] at hunfold
      by_cases hstack : stack.length > remaining + 1
      · simp [hstack] at hunfold
      · simp [hstack] at hunfold
        cases hnode : ClassicalCertificateTraceDag.nodeAt
            certificate.traceCode sourceRoot with
        | empty => simp [hnode] at hunfold
        | leaf => simp [hnode] at hunfold
        | node red blue purple =>
            have hchildrenEq : children = successorStates certificate
                ⟨layer, remaining + 1, sourceRoot, responseRoot, stack⟩
                  remaining red blue purple := by
              simpa [hnode] using hunfold.symm
            subst children
            cases stack with
            | nil =>
                have hall := List.all_eq_true.1 hchildren
                have hred := hall
                  ⟨layer, remaining, red,
                    responseChild? certificate.responseCode responseRoot .skip,
                    []⟩ (by simp [successorStates])
                have hblue := hall
                  ⟨layer, remaining, blue,
                    responseChild? certificate.responseCode responseRoot .push,
                    [false]⟩ (by simp [successorStates])
                have hpurple := hall
                  ⟨layer, remaining, purple,
                    responseChild? certificate.responseCode responseRoot .push,
                    [true]⟩ (by simp [successorStates])
                simpa [evaluate, productBoolean, hnode] using
                  And.intro (And.intro hred hblue) hpurple
            | cons head rest =>
                have hstack' : ¬remaining < rest.length := by
                  simp only [List.length_cons] at hstack
                  omega
                have hall := List.all_eq_true.1 hchildren
                have hred := hall
                  ⟨layer, remaining, red,
                    responseChild? certificate.responseCode responseRoot .skip,
                    head :: rest⟩ (by cases head <;> simp [successorStates])
                have hbluePush := hall
                  ⟨layer, remaining, blue,
                    responseChild? certificate.responseCode responseRoot .push,
                    false :: head :: rest⟩
                  (by cases head <;> simp [successorStates])
                have hpurplePush := hall
                  ⟨layer, remaining, purple,
                    responseChild? certificate.responseCode responseRoot .push,
                    true :: head :: rest⟩
                  (by cases head <;> simp [successorStates])
                cases head with
                | false =>
                    have hbluePop := hall
                      ⟨layer, remaining, blue,
                        responseChild? certificate.responseCode responseRoot
                          .popSame, rest⟩ (by simp [successorStates])
                    have hpurplePop := hall
                      ⟨layer, remaining, purple,
                        responseChild? certificate.responseCode responseRoot
                          .popOpposite, rest⟩ (by simp [successorStates])
                    simpa [evaluate, productBoolean, hnode, hstack'] using
                      And.intro
                        (And.intro
                          (And.intro (And.intro hred hbluePush) hbluePop)
                          hpurplePush)
                        hpurplePop
                | true =>
                    have hbluePop := hall
                      ⟨layer, remaining, blue,
                        responseChild? certificate.responseCode responseRoot
                          .popOpposite, rest⟩ (by simp [successorStates])
                    have hpurplePop := hall
                      ⟨layer, remaining, purple,
                        responseChild? certificate.responseCode responseRoot
                          .popSame, rest⟩ (by simp [successorStates])
                    simpa [evaluate, productBoolean, hnode, hstack'] using
                      And.intro
                        (And.intro
                          (And.intro (And.intro hred hbluePush) hbluePop)
                          hpurplePush)
                        hpurplePop

theorem Derivation.evaluate_eq_true
    (derivation : Derivation certificate state) :
    evaluate certificate state = true := by
  induction derivation with
  | result hunfold hvalue =>
      rw [evaluate_eq_of_unfoldState_eq_inl certificate _ _ hunfold, hvalue]
  | children hunfold hchildren ih =>
      apply evaluate_eq_true_of_unfoldState_eq_inr certificate _ _ hunfold
      apply List.all_eq_true.2
      intro child hchild
      exact ih child hchild

end ClassicalCertificateTraceResponseProduct

end Mettapedia.GraphTheory.FourColor
