; Recursive collection matching retains scoped tasks and allocation histories.
(: gslt:recursive-collection:arrange (-> Atom Atom Atom %Undefined%))
(= (gslt:recursive-collection:arrange $names $kind $items)
  (if (== $kind "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec") $items
    (let $sorted (gslt:canon:sort $names $items)
      (if (== $kind "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashSet")
        (gslt:canon:dedup-sorted $sorted) $sorted))))

(: gslt:recursive-collection:inherit (-> Atom %Undefined%))
(= (gslt:recursive-collection:inherit $works)
  (case $works
    ((LNil LNil)
     ((LCons (ScopedMatcherWork $assignment $tasks $unused) $tail)
       (let $later (gslt:recursive-collection:inherit $tail)
         (LCons (RecursiveCollectionWork $assignment $tasks LNil) $later))))))

(: gslt:recursive-collection:allocation (-> Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:recursive-collection:allocation $names $path $depth $initial $kind $schemas $rest $allocation)
  (case $allocation
    (((CollectionAllocation $values $residual $decisions)
      (let* (($remaining (gslt:recursive-collection:arrange $names $kind $residual))
             ($arguments (ScopedMatcherArguments $path $depth 0 $schemas $values))
             ($trace (LCons (CollectionEvent $path $kind $decisions) LNil)))
        (case $rest
          ((RNone
            (case $remaining
              ((LNil (Some (RecursiveCollectionWork $initial (LCons $arguments LNil) $trace)))
               ((LCons $head $tail) None))))
           ((RSome $name)
             (let* (($count (gslt:automata:length $schemas))
                    ($next (gslt:automata:append $path (LCons $count LNil))))
               (Some (RecursiveCollectionWork $initial
                 (LCons $arguments (LCons (ScopedMatcherRestCapture $next $depth $name $kind $remaining) LNil))
                 $trace)))))))))))

(: gslt:recursive-collection:allocations (-> Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:recursive-collection:allocations $names $path $depth $initial $kind $schemas $rest $allocations)
  (case $allocations
    ((LNil LNil)
     ((LCons $allocation $tail)
       (let* (($head (gslt:recursive-collection:allocation $names $path $depth $initial $kind $schemas $rest $allocation))
              ($later (gslt:recursive-collection:allocations $names $path $depth $initial $kind $schemas $rest $tail)))
         (case $head
           ((None $later)
            ((Some $work) (LCons $work $later)))))))))

(: gslt:recursive-collection:ordinary (-> Atom Atom Atom %Undefined%))
(= (gslt:recursive-collection:ordinary $request $initial $task)
  (let $works (gslt:rule:scope-matcher-expand $request $initial $task)
    (gslt:recursive-collection:inherit $works)))

(: gslt:recursive-collection:expand (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:recursive-collection:expand $names $request $initial $task)
  (case $task
    (((ScopedMatcherTree $path $depth $schema $target)
       (case (RecursiveMatchPair $schema $target)
         (((RecursiveMatchPair (PCollection $kind $schemas $rest) (PCollection $actual $targets RNone))
           (if (== $kind $actual)
             (if (== $kind "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec")
               (gslt:recursive-collection:ordinary $request $initial $task)
               (let* (($items (gslt:recursive-collection:arrange $names $kind $targets))
                      ($count (gslt:automata:length $schemas))
                      ($idempotent (if (== $kind "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashSet") 1 0))
                      ($allocations (gslt:collection:allocate $idempotent $count $items)))
                 (gslt:recursive-collection:allocations $names $path $depth $initial $kind $schemas $rest $allocations)))
             LNil))
          ($other (gslt:recursive-collection:ordinary $request $initial $task)))))
     ((ScopedMatcherArguments $path $depth $index $schemas $targets)
       (gslt:recursive-collection:ordinary $request $initial $task))
     ((ScopedMatcherRestCapture $path $depth $name $kind $targets)
       (gslt:recursive-collection:ordinary $request $initial $task))
     ((ScopedMatcherBag $path $depth $index $schemas $rest $kind $targets) LNil)
     ((ScopedMatcherBagSelect $path $depth $index $schema $schemas $rest $kind $targets $selected) LNil))))

(: gslt:recursive-collection:branches (-> Atom Atom Atom %Undefined%))
(= (gslt:recursive-collection:branches $branches $tasks $trace)
  (case $branches
    ((LNil LNil)
     ((LCons (RecursiveCollectionWork $assignment $headTasks $headTrace) $tail)
       (let* (($nextTasks (gslt:automata:append $headTasks $tasks))
              ($nextTrace (gslt:automata:append $trace $headTrace))
              ($later (gslt:recursive-collection:branches $tail $tasks $trace)))
         (LCons (RecursiveCollectionWork $assignment $nextTasks $nextTrace) $later))))))

(: gslt:recursive-collection:advance (-> Atom Atom Atom %Undefined%))
(= (gslt:recursive-collection:advance $names $request $work)
  (case $work
    (((RecursiveCollectionWork $assignment $tasks $trace)
      (case $tasks
        ((LNil LNil)
         ((LCons $task $tail)
           (let $branches (gslt:recursive-collection:expand $names $request $assignment $task)
             (gslt:recursive-collection:branches $branches $tail $trace)))))))))

(: gslt:recursive-collection:tick (-> Atom Atom Atom %Undefined%))
(= (gslt:recursive-collection:tick $names $request $state)
  (case $state
    (((RecursiveCollectionState $agenda $answers)
      (case $agenda
        ((LNil $state)
         ((LCons (RecursiveCollectionWork $assignment $tasks $trace) $tail)
           (case $tasks
             ((LNil
               (let $nextAnswers (gslt:automata:append $answers
                      (LCons (RecursiveCollectionAnswer $assignment $trace) LNil))
                 (RecursiveCollectionState $tail $nextAnswers)))
              ((LCons $task $rest)
                (let* (($branches (gslt:recursive-collection:advance $names $request
                          (RecursiveCollectionWork $assignment $tasks $trace)))
                       ($nextAgenda (gslt:automata:append $branches $tail)))
                  (RecursiveCollectionState $nextAgenda $answers))))))))))))

(: gslt:recursive-collection:run (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:recursive-collection:run $names $request $fuel $state)
  (if (== $fuel 0) $state
    (let* (($next (gslt:recursive-collection:tick $names $request $state))
           ($remaining (- $fuel 1)))
      (gslt:recursive-collection:run $names $request $remaining $next))))

(: gslt:recursive-collection:start (-> Atom %Undefined%))
(= (gslt:recursive-collection:start $request)
  (case $request
    (((ScopedMatcherRequest $rule $spec $ambient $site $path $depth $initial $schema $target)
      (RecursiveCollectionState
        (LCons (RecursiveCollectionWork $initial
          (LCons (ScopedMatcherTree $path $depth $schema $target) LNil) LNil) LNil) LNil)))))

(: gslt:recursive-collection:complete (-> Atom %Undefined%))
(= (gslt:recursive-collection:complete $state)
  (case $state
    (((RecursiveCollectionState $agenda $answers)
      (case $agenda ((LNil True) ((LCons $head $tail) False)))))))

; Canonical targets enter the same retained allocation machine. The normalized
; request is stored once and reused while its allocation histories are drained.
(: gslt:recursive-collection:canonical-request (-> Atom Atom %Undefined%))
(= (gslt:recursive-collection:canonical-request $names $request)
  (case $request
    (((ScopedMatcherRequest $rule $spec $ambient $site $path $depth $initial $schema $target)
      (let $canonical (gslt:canon:canon $names $target)
        (ScopedMatcherRequest $rule $spec $ambient $site $path $depth $initial $schema $canonical))))))

(: gslt:recursive-collection:canonical-start (-> Atom Atom %Undefined%))
(= (gslt:recursive-collection:canonical-start $names $request)
  (let* (($canonical (gslt:recursive-collection:canonical-request $names $request))
         ($state (gslt:recursive-collection:start $canonical)))
    (CanonicalMatchingState $canonical $state)))

(: gslt:recursive-collection:canonical-tick (-> Atom Atom %Undefined%))
(= (gslt:recursive-collection:canonical-tick $names $state)
  (case $state
    (((CanonicalMatchingState $request $machine)
      (let $next (gslt:recursive-collection:tick $names $request $machine)
        (CanonicalMatchingState $request $next))))))

(: gslt:recursive-collection:canonical-complete (-> Atom %Undefined%))
(= (gslt:recursive-collection:canonical-complete $state)
  (case $state
    (((CanonicalMatchingState $request $machine)
      (gslt:recursive-collection:complete $machine)))))

(: gslt:recursive-collection:canonical-answer-at (-> Atom Atom %Undefined%))
(= (gslt:recursive-collection:canonical-answer-at $state $cursor)
  (case $state
    (((CanonicalMatchingState $request (RecursiveCollectionState $agenda $answers))
      (case (gslt:rule:row-at $cursor $answers)
        ((None None)
         ((Some (RecursiveCollectionAnswer $assignment $trace))
          (Some (ScopedMatcherAnswer $assignment $trace)))))))))

(: gslt:recursive-collection:canonical-input (-> Atom Atom Atom %Undefined%))
(= (gslt:recursive-collection:canonical-input $names $actual $expected)
  (let* (($left (gslt:canon:canon $names $actual))
         ($right (gslt:canon:canon $names $expected)))
    (== $left $right)))
