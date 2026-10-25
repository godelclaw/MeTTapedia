; Retained occurrence execution behind the shared search interface.
(: gslt:occurrence-search:run (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:occurrence-search:run $names $depth $plan $source $work)
  (case $plan
    (((CompletePlan
        (PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free)
        $permissions $bound $expected $rules $equations $admitted)
      (let* (($canonical (gslt:canon:canon $names $source))
             ($initial (gslt:occurrence-discovery:begin
               $declarations $free $permissions $bound $expected $canonical $rules))
             ($state (gslt:occurrence-machine:run $names
               (PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free)
               $depth $work $initial)))
        (gslt:occurrence-search:with-state $plan $source $state))))))

(: gslt:occurrence-search:resume (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:occurrence-search:resume $names $depth $run $work)
  (case $run
    (((RecursiveOccurrenceRun
        (CompletePlan $environment $permissions $bound $expected $rules $equations $admitted)
        $source $state $published)
      (let $next (gslt:occurrence-machine:run $names $environment $depth $work $state)
        (gslt:occurrence-search:with-state
          (CompletePlan $environment $permissions $bound $expected $rules $equations $admitted)
          $source $next))))))

(: gslt:occurrence-search:lanes-complete (-> Atom %Undefined%))
(= (gslt:occurrence-search:lanes-complete $lanes)
  (case $lanes
    ((LNil True)
     ((LCons (RecursiveOccurrenceLane $origin $request $state $spent) $rest)
      (if (gslt:recursive-collection:complete $state)
        (gslt:occurrence-search:lanes-complete $rest) False)))))

(: gslt:occurrence-search:frames-idle (-> Atom %Undefined%))
(= (gslt:occurrence-search:frames-idle $frames)
  (case $frames
    ((LNil True)
     ((LCons (RecursiveOccurrenceFrame $origin
        (RecursiveCollectionContinuation $prepared
          (PremiseState $agenda $answers $unresolved $work))) $rest)
      (case $agenda
        ((LNil (gslt:occurrence-search:frames-idle $rest))
         ((LCons $task $tasks) False)))))))

(: gslt:occurrence-search:frames-resolved (-> Atom %Undefined%))
(= (gslt:occurrence-search:frames-resolved $frames)
  (case $frames
    ((LNil True)
     ((LCons (RecursiveOccurrenceFrame $origin
        (RecursiveCollectionContinuation $prepared
          (PremiseState $agenda $answers $unresolved $work))) $rest)
      (case $unresolved
        ((LNil (gslt:occurrence-search:frames-resolved $rest))
         ((LCons $obligation $obligations) False)))))))

(: gslt:occurrence-search:status (-> Atom %Undefined%))
(= (gslt:occurrence-search:status $run)
  (case $run
    (((RecursiveOccurrenceRun $plan $source
        (RecursiveOccurrenceState $lanes (RecursiveOccurrenceBatch $frames $log)) $published)
      (if (gslt:occurrence-search:lanes-complete $lanes)
        (if (gslt:occurrence-search:frames-idle $frames)
          (if (gslt:occurrence-search:frames-resolved $frames)
            SearchComplete SearchBlocked)
          SearchPending)
        SearchPending)))))

(: gslt:occurrence-search:finish (-> Atom Atom %Undefined%))
(= (gslt:occurrence-search:finish $plan $packet)
  (case (OccurrenceFinishInput $plan $packet)
    (((OccurrenceFinishInput
        (CompletePlan $environment $permissions $bound $expected $rules $equations $admitted)
        (RecursiveOccurrencePublication
          (RecursiveCollectionOrigin
            (RuleJob $ordinal $declaration $originalSite)
            (CollectionSiteVariant $original
              (RuleJobSite $address $context $focus $focusBound $focusType $frames))
            $allocation)
          (RecursiveCollectionContinued
            (PreparedCollectionMatch $preparedSource
              (ScopedMatcherAnswer $captured $trace) $allocationHistory)
            (RootAnswer $outcomeTrace $outcomeCaptured $completed $history $target))))
      (let* (($presented (gslt:rule:scope-fill $context $preparedSource))
             ($job (RuleJob $ordinal $declaration
               (RuleJobSite $address $context $preparedSource $focusBound $focusType $frames)))
             ($request (RuleJobRequestProjection
               $environment $permissions $bound $expected $presented $job))
             ($result (PremiseResult (RootGoal $focusBound $focusType $preparedSource $ordinal)
               (RootAnswer $trace $captured $completed $history $target))))
        (gslt:rule:job-finish-root $request $result))))))

(: gslt:occurrence-search:read-log (-> Atom Atom %Undefined%))
(= (gslt:occurrence-search:read-log $plan $packets)
  (case $packets
    ((LNil LNil)
     ((LCons $packet $rest)
      (let* (($finished (gslt:occurrence-search:finish $plan $packet))
             ($later (gslt:occurrence-search:read-log $plan $rest)))
        (case $finished
          (((Some $receipt) (LCons $receipt $later))
           (None $later))))))))

(: gslt:occurrence-search:with-state (-> Atom Atom Atom %Undefined%))
(= (gslt:occurrence-search:with-state $plan $source $state)
  (case $state
    (((RecursiveOccurrenceState $lanes (RecursiveOccurrenceBatch $frames $log))
      (let $published (gslt:occurrence-search:read-log $plan $log)
        (RecursiveOccurrenceRun $plan $source $state $published))))))

(: gslt:occurrence-search:publication (-> Atom %Undefined%))
(= (gslt:occurrence-search:publication $run)
  (case $run
    (((RecursiveOccurrenceRun $plan $source $state $published) $published))))

(: gslt:occurrence-search:target (-> Atom Atom %Undefined%))
(= (gslt:occurrence-search:target $names $receipt)
  (case $receipt
    (((RuleJobReceipt $job $trace $captured $completed $history $local $target)
      (gslt:canon:canon $names $target)))))
