; A prepared recursive allocation owns one retained typed/premise state.
(: gslt:collection-continuation:begin
  (-> Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:collection-continuation:begin
     $environment $depth $bound $type $index $rule $spec $prepared)
  (case $prepared
    (((PreparedCollectionMatch $source $answer $history)
      (let* (($next-depth (+ $depth 1))
             ($goal (DescentRootGoal $next-depth $bound $type $source $index))
             ($tail (DescentDone $goal))
             ($expanded (gslt:descent:continue-root-answer
               $environment $depth $bound $type $source $index $rule $spec
               $answer $tail LNil))
             ($state (gslt:collection-backend:expansion-state $expanded)))
        (RecursiveCollectionContinuation $prepared $state))))))

(: gslt:collection-continuation:run (-> Atom Atom Atom %Undefined%))
(= (gslt:collection-continuation:run $environment $work $frame)
  (case $frame
    (((RecursiveCollectionContinuation $prepared $state)
      (let $next (gslt:descent:run $environment $work $state)
        (RecursiveCollectionContinuation $prepared $next))))))

(: gslt:collection-continuation:results (-> Atom Atom Atom %Undefined%))
(= (gslt:collection-continuation:results $prepared $expected $answers)
  (case $answers
    ((LNil LNil)
     ((LCons (PremiseResult $goal (RootAnswer $trace $captured $completed $history $target)) $rest)
      (let $later (gslt:collection-continuation:results $prepared $expected $rest)
        (if (== $captured $expected)
          (LCons (RecursiveCollectionContinued $prepared
                   (RootAnswer $trace $captured $completed $history $target)) $later)
          $later))))))

(: gslt:collection-continuation:publication (-> Atom %Undefined%))
(= (gslt:collection-continuation:publication $frame)
  (case $frame
    (((RecursiveCollectionContinuation
        (PreparedCollectionMatch $source (ScopedMatcherAnswer $captured $trace) $allocation-history)
        (PremiseState $tasks $answers $unresolved $work))
      (gslt:collection-continuation:results
        (PreparedCollectionMatch $source (ScopedMatcherAnswer $captured $trace) $allocation-history)
        $captured $answers)))))
