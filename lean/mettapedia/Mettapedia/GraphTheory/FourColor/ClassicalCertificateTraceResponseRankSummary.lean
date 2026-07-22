import Mettapedia.GraphTheory.FourColor.ClassicalCertificateTraceResponseProduct

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateTraceResponseRankSummary

open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateKempeClosure
open ClassicalCertificateRankedKempe
open ClassicalCertificateResponseDag
open ClassicalCertificateTraceDag
open ClassicalCertificateTraceResponseProduct
open ClassicalCertificateTraceTree

variable {length : Nat}

/-- A source/response/stack product state independent of the queried rank. -/
structure State where
  remaining : Nat
  sourceRoot : Nat
  responseRoot : Option Nat
  stack : List Bool
  deriving DecidableEq, Repr

/-- `none` records a missing required response.  A successful summary stores
the least rank at which every represented response is strictly lower. -/
def combineSummaries : List (Option Nat) → Option Nat
  | [] => some 0
  | none :: _ => none
  | some head :: tail =>
      match combineSummaries tail with
      | none => none
      | some bound => some (max head bound)

def terminalSummary
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (state : State) : Option Nat :=
  match ClassicalCertificateTraceDag.nodeAt certificate.traceCode
      state.sourceRoot with
  | .leaf =>
      if state.stack = [] then
        match state.responseRoot with
        | none => none
        | some root =>
            match ClassicalCertificateResponseDag.nodeAt
                certificate.responseCode root with
            | .leaf index =>
                if index < ClassicalCertificateResponseDag.valueBound
                    certificate.responseCode then
                  match ClassicalCertificateResponseDag.valueAt?
                      certificate.responseCode index with
                  | some value => some (value.rank + 1)
                  | none => none
                else none
            | _ => none
      else some 0
  | _ => some 0

def successorStates
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (state : State) (remaining red blue purple : Nat) : List State :=
  let next (sourceRoot : Nat) (step : ChromogramStep)
      (stack : List Bool) : State :=
    ⟨remaining, sourceRoot,
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

/-- A one-step view whose terminal result is a rank summary and whose child
states do not mention a rank. -/
def unfoldState
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (state : State) : Sum (Option Nat) (List State) :=
  match state.remaining with
  | 0 => .inl (terminalSummary certificate state)
  | remaining + 1 =>
      if state.stack.length > remaining + 1 then .inl (some 0)
      else
        match ClassicalCertificateTraceDag.nodeAt certificate.traceCode
            state.sourceRoot with
        | .node red blue purple =>
            .inr (successorStates certificate state remaining red blue purple)
        | _ => .inl (some 0)

/-- Direct summary evaluator.  Unlike `productBoolean`, the result can be
reused at every layer: a successful bound `b` validates all layers `b ≤ l`. -/
def rankSummary
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length) :
    Nat → Nat → Option Nat → List Bool → Option Nat
  | 0, sourceRoot, responseRoot, stack =>
      terminalSummary certificate ⟨0, sourceRoot, responseRoot, stack⟩
  | remaining + 1, sourceRoot, responseRoot, stack =>
      if stack.length > remaining + 1 then some 0
      else
        match ClassicalCertificateTraceDag.nodeAt certificate.traceCode
            sourceRoot with
        | .node red blue purple =>
            let recurse (sourceChild : Nat) (step : ChromogramStep)
                (nextStack : List Bool) :=
              rankSummary certificate remaining sourceChild
                (responseChild? certificate.responseCode responseRoot step)
                nextStack
            let redSummary := recurse red .skip stack
            let bluePushSummary := recurse blue .push (false :: stack)
            let purplePushSummary := recurse purple .push (true :: stack)
            match stack with
            | [] => combineSummaries
                [redSummary, bluePushSummary, purplePushSummary]
            | false :: rest => combineSummaries
                [redSummary, bluePushSummary, purplePushSummary,
                  recurse blue .popSame rest,
                  recurse purple .popOpposite rest]
            | true :: rest => combineSummaries
                [redSummary, bluePushSummary, purplePushSummary,
                  recurse blue .popOpposite rest,
                  recurse purple .popSame rest]
        | _ => some 0

def evaluate
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (state : State) : Option Nat :=
  rankSummary certificate state.remaining state.sourceRoot state.responseRoot
    state.stack

theorem evaluate_eq_of_unfoldState_eq_inl
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (state : State) (result : Option Nat)
    (hunfold : unfoldState certificate state = .inl result) :
    evaluate certificate state = result := by
  rcases state with ⟨remaining, sourceRoot, responseRoot, stack⟩
  cases remaining with
  | zero =>
      simpa [unfoldState, evaluate, rankSummary] using
        congrArg (fun value => Sum.getLeft? value) hunfold
  | succ remaining =>
      simp only [unfoldState] at hunfold
      by_cases hstack : stack.length > remaining + 1
      · simp [hstack] at hunfold
        simpa [evaluate, rankSummary, hstack] using hunfold
      · simp [hstack] at hunfold
        cases hnode : ClassicalCertificateTraceDag.nodeAt
            certificate.traceCode sourceRoot with
        | empty =>
            simp [hnode] at hunfold
            simpa [evaluate, rankSummary, hstack, hnode] using hunfold
        | leaf =>
            simp [hnode] at hunfold
            simpa [evaluate, rankSummary, hstack, hnode] using hunfold
        | node red blue purple => simp [hnode] at hunfold

theorem evaluate_eq_of_unfoldState_eq_inr
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (state : State) (children : List State) (bound : Nat)
    (hunfold : unfoldState certificate state = .inr children)
    (hchildren : combineSummaries
      (children.map (evaluate certificate)) = some bound) :
    evaluate certificate state = some bound := by
  rcases state with ⟨remaining, sourceRoot, responseRoot, stack⟩
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
                ⟨remaining + 1, sourceRoot, responseRoot, stack⟩
                  remaining red blue purple := by
              simpa [hnode] using hunfold.symm
            subst children
            cases stack with
            | nil =>
                simpa [evaluate, rankSummary, successorStates, hnode] using
                  hchildren
            | cons head tail =>
                have hstack' : ¬remaining < tail.length := by
                  simp only [List.length_cons] at hstack
                  omega
                cases head <;>
                  simpa [evaluate, rankSummary, successorStates, hnode,
                    hstack'] using hchildren

theorem summary_eq_some_of_mem_of_combineSummaries_eq_some
    {summaries : List (Option Nat)} {summary : Option Nat} {bound : Nat}
    (hcombine : combineSummaries summaries = some bound)
    (hmem : summary ∈ summaries) :
    ∃ childBound, summary = some childBound ∧ childBound ≤ bound := by
  induction summaries generalizing summary bound with
  | nil => simp at hmem
  | cons head tail ih =>
      cases head with
      | none => simp [combineSummaries] at hcombine
      | some headBound =>
          cases htail : combineSummaries tail with
          | none => simp [combineSummaries, htail] at hcombine
          | some tailBound =>
              have hbound : max headBound tailBound = bound := by
                have hsome : some (max headBound tailBound) = some bound := by
                  simpa [combineSummaries, htail] using hcombine
                exact Option.some.inj hsome
              rcases List.mem_cons.1 hmem with rfl | htailMem
              · exact ⟨headBound, rfl, by omega⟩
              · obtain ⟨childBound, hchild, hle⟩ := ih htail htailMem
                exact ⟨childBound, hchild, by omega⟩

private theorem productBoolean_zero_eq_true_of_rankSummary_eq_some
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (layer sourceRoot : Nat) (responseRoot : Option Nat) (stack : List Bool)
    (bound : Nat)
    (hsummary : rankSummary certificate 0 sourceRoot responseRoot stack =
      some bound)
    (hbound : bound ≤ layer) :
    ClassicalCertificateTraceResponseProduct.productBoolean certificate layer
      0 sourceRoot responseRoot stack = true := by
  cases hsource : ClassicalCertificateTraceDag.nodeAt certificate.traceCode
      sourceRoot with
  | empty => simp [rankSummary, terminalSummary, hsource, productBoolean]
  | node red blue purple =>
      simp [rankSummary, terminalSummary, hsource, productBoolean]
  | leaf =>
      cases stack with
      | cons head tail =>
          simp [rankSummary, terminalSummary, hsource, productBoolean]
      | nil =>
          cases responseRoot with
          | none => simp [rankSummary, terminalSummary, hsource] at hsummary
          | some responseRoot =>
              cases hresponse : ClassicalCertificateResponseDag.nodeAt
                  certificate.responseCode responseRoot with
              | empty =>
                  simp [rankSummary, terminalSummary, hsource, hresponse]
                    at hsummary
              | node push skip popSame popOpposite =>
                  simp [rankSummary, terminalSummary, hsource, hresponse]
                    at hsummary
              | leaf index =>
                  by_cases hindex : index <
                      ClassicalCertificateResponseDag.valueBound
                        certificate.responseCode
                  · cases hvalue : ClassicalCertificateResponseDag.valueAt?
                        certificate.responseCode index with
                    | none =>
                        simp [rankSummary, terminalSummary, hsource, hresponse,
                          hindex, hvalue] at hsummary
                    | some value =>
                        have hboundEq : value.rank + 1 = bound := by
                          have hsome : some (value.rank + 1) = some bound := by
                            simpa [rankSummary, terminalSummary, hsource,
                              hresponse, hindex, hvalue] using hsummary
                          exact Option.some.inj hsome
                        have hrank : value.rank < layer := by omega
                        simp [productBoolean, hsource, responseLeafBoolean,
                          hresponse, hindex, hvalue, hrank]
                  · simp [rankSummary, terminalSummary, hsource, hresponse,
                      hindex] at hsummary

/-- A successful rank summary validates the original product traversal at
every layer at least as large as the stored bound. -/
theorem productBoolean_eq_true_of_rankSummary_eq_some
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (layer remaining sourceRoot : Nat) (responseRoot : Option Nat)
    (stack : List Bool) (bound : Nat)
    (hsummary : rankSummary certificate remaining sourceRoot responseRoot
      stack = some bound)
    (hbound : bound ≤ layer) :
    ClassicalCertificateTraceResponseProduct.productBoolean certificate layer
      remaining sourceRoot responseRoot stack = true := by
  induction remaining generalizing sourceRoot responseRoot stack bound with
  | zero =>
      exact productBoolean_zero_eq_true_of_rankSummary_eq_some certificate
        layer sourceRoot responseRoot stack bound hsummary hbound
  | succ remaining ih =>
      by_cases hstack : stack.length > remaining + 1
      · simp [rankSummary, hstack] at hsummary
        simp [productBoolean, hstack]
      · cases hnode : ClassicalCertificateTraceDag.nodeAt certificate.traceCode
            sourceRoot with
        | empty => simp [rankSummary, productBoolean, hstack, hnode]
        | leaf => simp [rankSummary, productBoolean, hstack, hnode]
        | node red blue purple =>
            cases stack with
            | nil =>
                let summaries : List (Option Nat) :=
                  [rankSummary certificate remaining red
                      (responseChild? certificate.responseCode responseRoot
                        .skip) [],
                    rankSummary certificate remaining blue
                      (responseChild? certificate.responseCode responseRoot
                        .push) [false],
                    rankSummary certificate remaining purple
                      (responseChild? certificate.responseCode responseRoot
                        .push) [true]]
                have hcombine : combineSummaries summaries = some bound := by
                  simpa [rankSummary, hstack, hnode, summaries] using hsummary
                have childProduct (sourceChild : Nat) (step : ChromogramStep)
                    (nextStack : List Bool)
                    (hmem : rankSummary certificate remaining sourceChild
                      (responseChild? certificate.responseCode responseRoot step)
                        nextStack ∈ summaries) :
                    productBoolean certificate layer remaining sourceChild
                      (responseChild? certificate.responseCode responseRoot step)
                        nextStack = true := by
                  obtain ⟨childBound, hchild, hchildLe⟩ :=
                    summary_eq_some_of_mem_of_combineSummaries_eq_some hcombine
                      hmem
                  exact ih sourceChild
                    (responseChild? certificate.responseCode responseRoot step)
                      nextStack childBound hchild
                        (Nat.le_trans hchildLe hbound)
                have hred := childProduct red .skip [] (by simp [summaries])
                have hblue := childProduct blue .push [false]
                  (by simp [summaries])
                have hpurple := childProduct purple .push [true]
                  (by simp [summaries])
                simp [productBoolean, hstack, hnode, hred, hblue, hpurple]
            | cons head rest =>
                have hstack' : ¬remaining < rest.length := by
                  simp only [List.length_cons] at hstack
                  omega
                cases head with
                | false =>
                    let summaries : List (Option Nat) :=
                      [rankSummary certificate remaining red
                          (responseChild? certificate.responseCode responseRoot
                            .skip) (false :: rest),
                        rankSummary certificate remaining blue
                          (responseChild? certificate.responseCode responseRoot
                            .push) (false :: false :: rest),
                        rankSummary certificate remaining purple
                          (responseChild? certificate.responseCode responseRoot
                            .push) (true :: false :: rest),
                        rankSummary certificate remaining blue
                          (responseChild? certificate.responseCode responseRoot
                            .popSame) rest,
                        rankSummary certificate remaining purple
                          (responseChild? certificate.responseCode responseRoot
                            .popOpposite) rest]
                    have hcombine : combineSummaries summaries = some bound := by
                      simpa [rankSummary, hstack, hstack', hnode, summaries]
                        using hsummary
                    have childProduct (sourceChild : Nat)
                        (step : ChromogramStep) (nextStack : List Bool)
                        (hmem : rankSummary certificate remaining sourceChild
                          (responseChild? certificate.responseCode responseRoot
                            step) nextStack ∈ summaries) :
                        productBoolean certificate layer remaining sourceChild
                          (responseChild? certificate.responseCode responseRoot
                            step) nextStack = true := by
                      obtain ⟨childBound, hchild, hchildLe⟩ :=
                        summary_eq_some_of_mem_of_combineSummaries_eq_some
                          hcombine hmem
                      exact ih sourceChild
                        (responseChild? certificate.responseCode responseRoot
                          step) nextStack childBound hchild
                            (Nat.le_trans hchildLe hbound)
                    have hred := childProduct red .skip (false :: rest)
                      (by simp [summaries])
                    have hbluePush := childProduct blue .push
                      (false :: false :: rest) (by simp [summaries])
                    have hpurplePush := childProduct purple .push
                      (true :: false :: rest) (by simp [summaries])
                    have hbluePop := childProduct blue .popSame rest
                      (by simp [summaries])
                    have hpurplePop := childProduct purple .popOpposite rest
                      (by simp [summaries])
                    simp [productBoolean, hstack, hnode, hred, hbluePush,
                      hpurplePush, hbluePop, hpurplePop]
                | true =>
                    let summaries : List (Option Nat) :=
                      [rankSummary certificate remaining red
                          (responseChild? certificate.responseCode responseRoot
                            .skip) (true :: rest),
                        rankSummary certificate remaining blue
                          (responseChild? certificate.responseCode responseRoot
                            .push) (false :: true :: rest),
                        rankSummary certificate remaining purple
                          (responseChild? certificate.responseCode responseRoot
                            .push) (true :: true :: rest),
                        rankSummary certificate remaining blue
                          (responseChild? certificate.responseCode responseRoot
                            .popOpposite) rest,
                        rankSummary certificate remaining purple
                          (responseChild? certificate.responseCode responseRoot
                            .popSame) rest]
                    have hcombine : combineSummaries summaries = some bound := by
                      simpa [rankSummary, hstack, hstack', hnode, summaries]
                        using hsummary
                    have childProduct (sourceChild : Nat)
                        (step : ChromogramStep) (nextStack : List Bool)
                        (hmem : rankSummary certificate remaining sourceChild
                          (responseChild? certificate.responseCode responseRoot
                            step) nextStack ∈ summaries) :
                        productBoolean certificate layer remaining sourceChild
                          (responseChild? certificate.responseCode responseRoot
                            step) nextStack = true := by
                      obtain ⟨childBound, hchild, hchildLe⟩ :=
                        summary_eq_some_of_mem_of_combineSummaries_eq_some
                          hcombine hmem
                      exact ih sourceChild
                        (responseChild? certificate.responseCode responseRoot
                          step) nextStack childBound hchild
                            (Nat.le_trans hchildLe hbound)
                    have hred := childProduct red .skip (true :: rest)
                      (by simp [summaries])
                    have hbluePush := childProduct blue .push
                      (false :: true :: rest) (by simp [summaries])
                    have hpurplePush := childProduct purple .push
                      (true :: true :: rest) (by simp [summaries])
                    have hbluePop := childProduct blue .popOpposite rest
                      (by simp [summaries])
                    have hpurplePop := childProduct purple .popSame rest
                      (by simp [summaries])
                    simp [productBoolean, hstack, hnode, hred, hbluePush,
                      hpurplePush, hbluePop, hpurplePop]

end ClassicalCertificateTraceResponseRankSummary

end Mettapedia.GraphTheory.FourColor
