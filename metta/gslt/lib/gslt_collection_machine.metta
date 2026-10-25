; Collection jobs retain allocation evidence around the shared scoped machine.
(: gslt:collection-machine:allocation-state (-> Atom Atom %Undefined%))
(= (gslt:collection-machine:allocation-state $request $allocation)
  (case $request
    (((CollectionRequest
        (ScopedMatcherRequest $rule $spec $ambient $site $path $depth $initial
          (PCollection $kind $schemas $rest) $target) $index)
      (case $allocation
        (((CollectionAllocation $values $residual $decisions)
          (let $arguments (ScopedMatcherArguments $path $depth $index $schemas $values)
            (case $rest
              ((RNone
                (case $residual
                  ((LNil
                    (ScopedMatcherState
                      (LCons (ScopedMatcherWork $initial (LCons $arguments LNil) LNil) LNil) LNil))
                   ((LCons $head $tail) (ScopedMatcherState LNil LNil)))))
               ((RSome $name)
                (let* (($count (gslt:automata:length $schemas))
                       ($next (+ $index $count))
                       ($rest-path (gslt:automata:append $path (LCons $next LNil))))
                  (ScopedMatcherState
                    (LCons (ScopedMatcherWork $initial
                      (LCons $arguments
                        (LCons (ScopedMatcherRestCapture $rest-path $depth $name $kind $residual) LNil))
                      LNil) LNil) LNil)))))))))))))

(: gslt:collection-machine:jobs (-> Atom Atom %Undefined%))
(= (gslt:collection-machine:jobs $request $allocations)
  (case $allocations
    ((LNil LNil)
     ((LCons $allocation $tail)
      (let* (($state (gslt:collection-machine:allocation-state $request $allocation))
             ($later (gslt:collection-machine:jobs $request $tail)))
        (LCons (CollectionJob $allocation $state) $later))))))

(: gslt:collection-machine:start (-> Atom %Undefined%))
(= (gslt:collection-machine:start $request)
  (case $request
    (((CollectionRequest
        (ScopedMatcherRequest $rule $spec $ambient $site $path $depth $initial
          (PCollection $kind $schemas $rest)
          (PCollection $target-kind $targets $target-rest)) $index)
      (let* (($count (gslt:automata:length $schemas))
             ($idempotent (if (== $kind "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashSet") 1 0))
             ($allocations (gslt:collection:allocate $idempotent $count $targets)))
        (gslt:collection-machine:jobs $request $allocations))))))

(: gslt:collection-machine:resume (-> Atom Atom Atom %Undefined%))
(= (gslt:collection-machine:resume $request $fuel $jobs)
  (case $request
    (((CollectionRequest $machine $index)
      (case $jobs
        ((LNil LNil)
         ((LCons (CollectionJob $allocation $state) $tail)
          (let* (($next (gslt:rule:scope-matcher-run $machine $fuel $state))
                 ($later (gslt:collection-machine:resume $request $fuel $tail)))
            (LCons (CollectionJob $allocation $next) $later)))))))))

(: gslt:collection-machine:complete (-> Atom %Undefined%))
(= (gslt:collection-machine:complete $jobs)
  (case $jobs
    ((LNil 1)
     ((LCons (CollectionJob $allocation $state) $tail)
      (if (gslt:rule:scope-matcher-complete $state)
        (gslt:collection-machine:complete $tail) 0)))))

(: gslt:collection-machine:receipts (-> Atom Atom %Undefined%))
(= (gslt:collection-machine:receipts $allocation $answers)
  (case $answers
    ((LNil LNil)
     ((LCons $answer $tail)
      (let $later (gslt:collection-machine:receipts $allocation $tail)
        (LCons (CollectionReceipt $allocation $answer) $later))))))

(: gslt:collection-machine:publication (-> Atom %Undefined%))
(= (gslt:collection-machine:publication $jobs)
  (case $jobs
    ((LNil LNil)
     ((LCons (CollectionJob $allocation (ScopedMatcherState $agenda $answers)) $tail)
      (let* (($first (gslt:collection-machine:receipts $allocation $answers))
             ($later (gslt:collection-machine:publication $tail)))
        (gslt:automata:append $first $later))))))

; Instantiate the authored right side while retaining the complete source receipt.
(: gslt:collection-machine:firing (-> Atom Atom %Undefined%))
(= (gslt:collection-machine:firing $request $receipt)
  (case $request
    (((CollectionRequest
        (ScopedMatcherRequest $rule $spec $ambient $site $path $depth $initial $schema $target)
        $index)
      (case $receipt
        (((CollectionReceipt $allocation (ScopedMatcherAnswer $assignment $trace))
          (case (gslt:rule:scope-reduct None $rule $spec $ambient $assignment)
            (((Some $result)
              (Some (CollectionFiring $receipt $result)))
             ($failed None))))
         ($invalid None))))
     ($invalid None))))

(: gslt:collection-machine:firings (-> Atom Atom %Undefined%))
(= (gslt:collection-machine:firings $request $receipts)
  (case $receipts
    ((LNil LNil)
     ((LCons $receipt $tail)
      (let $later (gslt:collection-machine:firings $request $tail)
        (case (gslt:collection-machine:firing $request $receipt)
          (((Some $firing) (LCons $firing $later))
           ($failed $later))))))))

; Run every source-derived root-collection request in plan order.
(: gslt:collection-plan:start (-> Atom %Undefined%))
(= (gslt:collection-plan:start $requests)
  (case $requests
    ((LNil LNil)
     ((LCons (CollectionPlanRequest $ordinal $request) $tail)
      (let* (($state (gslt:collection-machine:start $request))
             ($later (gslt:collection-plan:start $tail)))
        (LCons (CollectionPlanJob $ordinal $request $state) $later))))))

(: gslt:collection-plan:resume (-> Atom Atom %Undefined%))
(= (gslt:collection-plan:resume $fuel $jobs)
  (case $jobs
    ((LNil LNil)
     ((LCons (CollectionPlanJob $ordinal $request $state) $tail)
      (let* (($next (gslt:collection-machine:resume $request $fuel $state))
             ($later (gslt:collection-plan:resume $fuel $tail)))
        (LCons (CollectionPlanJob $ordinal $request $next) $later))))))

(: gslt:collection-plan:complete (-> Atom %Undefined%))
(= (gslt:collection-plan:complete $jobs)
  (case $jobs
    ((LNil 1)
     ((LCons (CollectionPlanJob $ordinal $request $state) $tail)
      (case (gslt:collection-machine:complete $state)
        ((1 (gslt:collection-plan:complete $tail))
         (0 0)))))))

(: gslt:collection-plan:firings (-> Atom %Undefined%))
(= (gslt:collection-plan:firings $jobs)
  (case $jobs
    ((LNil LNil)
     ((LCons (CollectionPlanJob $ordinal $request $state) $tail)
      (let* (($receipts (gslt:collection-machine:publication $state))
             ($first (gslt:collection-machine:firings $request $receipts))
             ($tagged (gslt:collection-plan:tag $ordinal $request $first))
             ($later (gslt:collection-plan:firings $tail)))
        (gslt:automata:append $tagged $later))))))

(: gslt:collection-plan:tag (-> Atom Atom Atom %Undefined%))
(= (gslt:collection-plan:tag $ordinal $request $firings)
  (case $firings
    ((LNil LNil)
     ((LCons $firing $tail)
      (let $later (gslt:collection-plan:tag $ordinal $request $tail)
        (LCons (CollectionPlanFiring $ordinal $request $firing) $later))))))
