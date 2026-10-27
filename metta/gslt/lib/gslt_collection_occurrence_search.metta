; Retained occurrence execution behind the shared search interface.
(: gslt:occurrence-search:run (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:occurrence-search:run $names $depth $plan $source $work)
  (case $plan
    (((CompletePlan $environment $permissions $bound $expected $rules $equations $admitted)
      (case (gslt:premise:matching-environment $environment)
        (((PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free)
          (let* (($canonical (gslt:canon:canon $names $source))
                 ($initial (gslt:occurrence-discovery:begin
                   $declarations $free $permissions $bound $expected $canonical $rules))
                 ($state (gslt:occurrence-machine:run $names $environment $depth $work $initial)))
            (gslt:occurrence-search:with-state $plan $source $state)))))))))

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
             ($core (gslt:premise:matching-environment $environment))
             ($seed
               (case $environment
                 (((InterpretedPremiseEnvironment $names $environmentCore)
                   (case $allocation
                     (((RecursiveCollectionAnswer $originalCaptured $originalTrace)
                       (ScopedMatcherAnswer $originalCaptured $originalTrace)))))
                  ($ordinary (ScopedMatcherAnswer $captured $trace)))))
             ($request (RuleJobRequestProjection
               $core $permissions $bound $expected $presented $job))
             ($result
               (case $seed
                 (((ScopedMatcherAnswer $seedCaptured $seedTrace)
                   (PremiseResult (RootGoal $focusBound $focusType $preparedSource $ordinal)
                     (RootAnswer $seedTrace $seedCaptured $completed $history $target)))))))
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

(: gslt:occurrence-search:read-committed (-> Atom Atom %Undefined%))
(= (gslt:occurrence-search:read-committed $plan $packets)
  (case $packets
    ((LNil LNil)
     ((LCons $packet $rest)
      (let* (($finished (gslt:occurrence-search:finish $plan $packet))
             ($later (gslt:occurrence-search:read-committed $plan $rest)))
        (case $finished
          (((Some $receipt) (LCons (CommittedOccurrence $packet $receipt) $later))
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

; Ordered readout of declared one-step firing evidence.
(: gslt:occurrence-search:key-event (-> Atom %Undefined%))
(= (gslt:occurrence-search:key-event $event)
   (case $event
     (((PremiseQueryEvent $p $q $row $origins) None)
      ((PremiseFreshnessEvent $p $q $atom $subject) None)
      ((PremiseQuantifiedEvent $p $q $kind $elements)
       (let $normalized (gslt:occurrence-search:key-elements $elements)
         (Some (PremiseQuantifiedEvent $p $q $kind $normalized))))
      ((PremiseChildEvent $p $q $declaration $bound $source $target $trace $target-trace $captured $completed $history)
       (let $normalized (gslt:occurrence-search:key-history $history)
         (Some (PremiseChildEvent $p $q $declaration $bound $source $target $trace $target-trace $captured $completed $normalized)))))))
(: gslt:occurrence-search:key-history (-> Atom %Undefined%))
(= (gslt:occurrence-search:key-history $history)
   (case $history
     ((LNil LNil)
      ((LCons $event $rest)
       (let* (($first (gslt:occurrence-search:key-event $event))
              ($later (gslt:occurrence-search:key-history $rest)))
         (case $first
           ((None $later)
            ((Some $evidence) (LCons $evidence $later)))))))))
(: gslt:occurrence-search:key-elements (-> Atom %Undefined%))
(= (gslt:occurrence-search:key-elements $elements)
   (case $elements
     ((LNil LNil)
      ((LCons (QuantifiedElement $index $element $history) $rest)
       (let* (($normalized (gslt:occurrence-search:key-history $history))
              ($later (gslt:occurrence-search:key-elements $rest)))
         (LCons (QuantifiedElement $index $element $normalized) $later))))))

(: gslt:occurrence-search:key-binding (-> Atom Atom Atom %Undefined%))
(= (gslt:occurrence-search:key-binding $table $name $assignment)
   (case (gslt:automata:binding $name $assignment)
     ((None None)
      ((Some (ContextualValue $dependencies $ambient $body))
       (let $canonical (gslt:canon:canon $table $body)
         (Some (ContextualValue $dependencies $ambient $canonical)))))))
(: gslt:occurrence-search:key-values (-> Atom Atom Atom %Undefined%))
(= (gslt:occurrence-search:key-values $table $names $assignment)
   (case $names
     ((LNil LNil)
      ((LCons $name $rest)
       (let* (($first (gslt:occurrence-search:key-binding $table $name $assignment))
              ($later (gslt:occurrence-search:key-values $table $rest $assignment)))
         (LCons $first $later))))))
(: gslt:occurrence-search:key-extract (-> Atom Atom Atom %Undefined%))
(= (gslt:occurrence-search:key-extract $table $names $committed)
   (case $committed
     (((CommittedOccurrence
         (RecursiveOccurrencePublication
           (RecursiveCollectionOrigin
             (RuleJob $ordinal (RuleJobDeclaration $authored $rule $binding-plan)
               (RuleJobSite $address $context $focus $bound $type $typing-frames))
             $variant $answer) $continued)
         (RuleJobReceipt $job $trace $captured $completed $history $local $target))
       (let* (($values (gslt:occurrence-search:key-values $table $names $completed))
              ($evidence (gslt:occurrence-search:key-history $history)))
         (DeclaredFiringKey $ordinal $authored
           (LogicalSiteShape $address $bound $type $typing-frames) $values $evidence))))))
(: gslt:occurrence-search:key-project (-> Atom Atom Atom %Undefined%))
(= (gslt:occurrence-search:key-project $table $names $committed)
   (case $committed
     ((LNil LNil)
      ((LCons $pair $rest)
       (let* (($first (gslt:occurrence-search:key-extract $table $names $pair))
              ($later (gslt:occurrence-search:key-project $table $names $rest)))
         (LCons $first $later))))))
(: gslt:occurrence-search:key-unique (-> Atom Atom Atom %Undefined%))
(= (gslt:occurrence-search:key-unique $table $names $committed)
   (let $keys (gslt:occurrence-search:key-project $table $names $committed)
     (gslt:automata:unique $keys)))
(: gslt:occurrence-search:key-binary (-> Atom Atom %Undefined%))
(= (gslt:occurrence-search:key-binary $head $key)
   (case $key
     (((DeclaredFiringKey $selected $authored $site
         (LCons (Some (ContextualValue $first-dependencies $first-ambient $first))
           (LCons $intermediate
             (LCons (Some (ContextualValue $last-dependencies $last-ambient $last)) LNil))) $history)
       (Some (PApp $head (LCons $first (LCons $last LNil)))))
      ($missing None))))
(: gslt:occurrence-search:key-conclusions (-> Atom Atom %Undefined%))
(= (gslt:occurrence-search:key-conclusions $head $keys)
   (case $keys
     ((LNil LNil)
      ((LCons $key $rest)
       (let* (($first (gslt:occurrence-search:key-binary $head $key))
              ($later (gslt:occurrence-search:key-conclusions $head $rest)))
         (case $first
           ((None $later)
            ((Some $conclusion) (LCons $conclusion $later)))))))))
(: gslt:occurrence-search:key-bag (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:occurrence-search:key-bag $table $names $head $committed)
   (let $keys (gslt:occurrence-search:key-unique $table $names $committed)
     (gslt:occurrence-search:key-conclusions $head $keys)))
(: gslt:occurrence-search:key-facts (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:occurrence-search:key-facts $table $names $head $committed)
   (let $bag (gslt:occurrence-search:key-bag $table $names $head $committed)
     (gslt:automata:unique $bag)))
