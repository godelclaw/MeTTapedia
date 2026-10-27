; Prepare one newly published recursive match and start its shared continuation.
(: gslt:occurrence-collector:allocate (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:occurrence-collector:allocate $names $environment $depth $origin $query $answer)
  (let $metadata (gslt:premise:matching-environment $environment)
    (case (OccurrenceAllocationInput $origin $query $metadata)
    (((OccurrenceAllocationInput
        (RecursiveOccurrenceJob
          (RuleJob $index $declaration $original-site)
          (CollectionSiteVariant $origin-site
            (RuleJobSite $address $context $focus $bound $type $frames)))
        (ScopedMatcherRequest $rule $spec $ambient $side $path $match-depth $initial $schema $target)
        (PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free))
      (if (gslt:premise:binding-admitted $rule $spec)
        (if (gslt:premise:open-well-sorted $declarations $free $bound $type $focus)
          (case (gslt:collection-handoff:prepare $names $query $answer)
            ((None None)
             ((Some $prepared)
              (let* (($allocated-origin
                        (RecursiveCollectionOrigin
                          (RuleJob $index $declaration $original-site)
                          (CollectionSiteVariant $origin-site
                            (RuleJobSite $address $context $focus $bound $type $frames))
                          $answer))
                     ($frame (gslt:occurrence-batch:frame-begin
                       $allocated-origin $environment $depth $bound $type $index $rule $spec $prepared)))
                (Some $frame)))))
          None)
        None))))))

(: gslt:occurrence-collector:collect (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:occurrence-collector:collect $names $environment $depth $origin $query $answers)
  (case $answers
    ((LNil LNil)
     ((LCons $answer $rest)
      (let* (($first (gslt:occurrence-collector:allocate
                       $names $environment $depth $origin $query $answer))
             ($later (gslt:occurrence-collector:collect
                       $names $environment $depth $origin $query $rest)))
        (case $first
          ((None $later)
           ((Some $frame) (LCons $frame $later)))))))))

; Advance one retained matcher and prepare only its fresh answer suffix.
(: gslt:occurrence-collector:advance-lane (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:occurrence-collector:advance-lane $names $environment $depth $lane)
  (case $lane
    (((RecursiveOccurrenceLane $origin $query $state $spent)
      (case (gslt:occurrence-matcher:advance $names $lane)
        (((RecursiveOccurrenceMatches $next $answers)
          (let $frames (gslt:occurrence-collector:collect
                         $names $environment $depth $origin $query $answers)
            (RecursiveOccurrenceLaneAllocations $next $frames)))))))))

(: gslt:occurrence-collector:advance-lanes (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:occurrence-collector:advance-lanes $names $environment $depth $lanes)
  (case $lanes
    ((LNil (RecursiveOccurrenceLanesAllocations LNil LNil))
     ((LCons $lane $rest)
      (case (gslt:occurrence-collector:advance-lane $names $environment $depth $lane)
        (((RecursiveOccurrenceLaneAllocations $next $fresh)
          (case (gslt:occurrence-collector:advance-lanes $names $environment $depth $rest)
            (((RecursiveOccurrenceLanesAllocations $next-rest $later)
              (let $all (gslt:automata:append $fresh $later)
                (RecursiveOccurrenceLanesAllocations (LCons $next $next-rest) $all))))))))))))
