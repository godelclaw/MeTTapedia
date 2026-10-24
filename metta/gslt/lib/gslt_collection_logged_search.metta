; Append-only resumable search over source-derived collection requests.
;
; Lane:  (CollectionLoggedLane ordinal request matcher-state spent consumed)
; State: (CollectionLoggedState lanes chronological-log)
; Run:   (CollectionLoggedRun source state)

; Build the source-local matcher requests from an admitted complete plan.
; Admission is what authorizes this backend; the native builder only reads the
; retained rule declarations.  The caller supplies a canonical root source, so
; its outer targets are already arranged for their collection kind.
(: gslt:collection-search:elaborated-types (-> Atom Atom %Undefined%))
(= (gslt:collection-search:elaborated-types $types $origin)
   (case $origin
     (((BindingInferredGrammar $implicit)
       (gslt:automata:append $types $implicit))
      ($other $types))))

(: gslt:collection-search:request-from-rule (-> Atom Atom Atom %Undefined%))
(= (gslt:collection-search:request-from-rule $actual-kind $targets $entry)
   (case $entry
     (((RuleJobDeclaration $declared-ordinal $rule (RuleBindingPlan $spec $origin))
       (case $rule
         (((ScopedRewriteRuleV1 $label $types $premises $left $right $binding)
           (case $left
             (((PCollection $kind $schemas $rest)
               (if (== $kind "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec") None
                 (if (== $kind $actual-kind)
                   (let $elaborated-types
                     (gslt:collection-search:elaborated-types $types $origin)
                     (Some (CollectionRequest
                     (ScopedMatcherRequest
                       (ScopedRewriteRuleV1 $label
                         $elaborated-types
                         $premises $left $right
                         (RuleBindingSome $spec))
                       $spec 0 RuleLeft LNil 0 LNil
                       (PCollection $kind $schemas $rest)
                       (PCollection $kind $targets RNone))
                     0)))
                   None)))
              ($not-collection None))))
          ($not-rule None)))))))

(: gslt:collection-search:requests-from-rules (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:collection-search:requests-from-rules $ordinal $actual-kind $targets $rules)
   (case $rules
     ((LNil LNil)
      ((LCons $entry $rest)
       (let* (($made (gslt:collection-search:request-from-rule
                       $actual-kind $targets $entry))
              ($next (+ $ordinal 1))
              ($later (gslt:collection-search:requests-from-rules
                        $next $actual-kind $targets $rest)))
         (case $made
           (((Some $request)
             (LCons (CollectionPlanRequest $ordinal $request) $later))
            (None $later))))))))

(: gslt:collection-search:requests-for-source (-> Atom Atom %Undefined%))
(= (gslt:collection-search:requests-for-source $plan $source)
   (case $plan
     (((CompletePlan $environment $permissions $bound $expected $rules $equations $admitted)
       (case $source
         (((PCollection $kind $targets RNone)
           (gslt:collection-search:requests-from-rules 0 $kind $targets $rules))
          ($not-source LNil)))))))

(: gslt:collection-search:drop (-> Atom Atom %Undefined%))
(= (gslt:collection-search:drop $count $items)
   (if (== $count 0) $items
     (case $items
       ((LNil LNil)
        ((LCons $item $rest)
         (let $remaining (- $count 1)
           (gslt:collection-search:drop $remaining $rest)))))))

(: gslt:collection-search:lane-begin (-> Atom %Undefined%))
(= (gslt:collection-search:lane-begin $entry)
   (case $entry
     (((CollectionPlanRequest $ordinal $request)
       (let $state (gslt:collection-machine:start $request)
         (CollectionLoggedLane $ordinal $request $state 0 0))))))

(: gslt:collection-search:lanes-begin (-> Atom %Undefined%))
(= (gslt:collection-search:lanes-begin $requests)
   (case $requests
     ((LNil LNil)
      ((LCons $entry $rest)
       (let* (($lane (gslt:collection-search:lane-begin $entry))
              ($later (gslt:collection-search:lanes-begin $rest)))
         (LCons $lane $later))))))

(: gslt:collection-search:begin (-> Atom %Undefined%))
(= (gslt:collection-search:begin $requests)
   (let $lanes (gslt:collection-search:lanes-begin $requests)
     (CollectionLoggedState $lanes LNil)))

; Split a flattened cursor over a single previous allocation publication.
(: gslt:collection-search:split-cursor (-> Atom Atom %Undefined%))
(= (gslt:collection-search:split-cursor $count $items)
   (if (== $count 0) (CollectionLoggedCursor 0 0)
     (case $items
       ((LNil (CollectionLoggedCursor 0 $count))
        ((LCons $item $rest)
         (let* (($previous (- $count 1))
                ($split (gslt:collection-search:split-cursor $previous $rest)))
           (case $split
             (((CollectionLoggedCursor $paid $remaining)
               (let $next (+ $paid 1)
                 (CollectionLoggedCursor $next $remaining)))))))))))

; Each allocation retains its own append-only matcher answers. A global drop
; on the flattened publication is invalid when allocations finish out of order.
(: gslt:collection-search:advance-jobs (-> Atom Atom Atom %Undefined%))
(= (gslt:collection-search:advance-jobs $request $consumed $jobs)
   (case $jobs
     ((LNil (CollectionLoggedJobsAdvanced LNil LNil))
      ((LCons $job $rest)
       (let* (($next-first (gslt:collection-machine:resume $request 1 (LCons $job LNil)))
              ($old-receipts (gslt:collection-machine:publication (LCons $job LNil)))
              ($previous (gslt:collection-machine:firings $request $old-receipts))
              ($split (gslt:collection-search:split-cursor $consumed $previous)))
         (case $split
           (((CollectionLoggedCursor $paid $remaining)
             (let* (($next-receipts (gslt:collection-machine:publication $next-first))
                    ($published (gslt:collection-machine:firings $request $next-receipts))
                    ($fresh (gslt:collection-search:drop $paid $published))
                    ($later (gslt:collection-search:advance-jobs $request $remaining $rest)))
               (case $later
                 (((CollectionLoggedJobsAdvanced $next-rest $more)
                   (case $next-first
                     (((LCons $next LNil)
                       (let $all (gslt:automata:append $fresh $more)
                         (CollectionLoggedJobsAdvanced (LCons $next $next-rest) $all)))))))))))))))))

(: gslt:collection-search:advance-lane (-> Atom %Undefined%))
(= (gslt:collection-search:advance-lane $lane)
   (case $lane
     (((CollectionLoggedLane $ordinal $request $state $spent $consumed)
       (let $advanced (gslt:collection-search:advance-jobs $request $consumed $state)
         (case $advanced
           (((CollectionLoggedJobsAdvanced $next-state $fresh)
             (let* (($receipts (gslt:collection-machine:publication $next-state))
              ($firings (gslt:collection-machine:firings $request $receipts))
              ($tagged (gslt:collection-plan:tag $ordinal $request $fresh))
              ($next-spent (+ $spent 1))
              ($next-consumed (gslt:automata:length $firings)))
         (CollectionLoggedAdvanced
           (CollectionLoggedLane $ordinal $request $next-state $next-spent $next-consumed)
           $tagged))))))))))

(: gslt:collection-search:advance-lanes (-> Atom %Undefined%))
(= (gslt:collection-search:advance-lanes $lanes)
   (case $lanes
     ((LNil (CollectionLoggedAdvanced LNil LNil))
      ((LCons $lane $rest)
       (let* (($first (gslt:collection-search:advance-lane $lane))
              ($later (gslt:collection-search:advance-lanes $rest)))
         (case $first
           (((CollectionLoggedAdvanced $next-lane $fresh)
             (case $later
               (((CollectionLoggedAdvanced $next-lanes $more)
                 (let $all (gslt:automata:append $fresh $more)
                   (CollectionLoggedAdvanced (LCons $next-lane $next-lanes) $all)))))))))))))

(: gslt:collection-search:round (-> Atom Atom %Undefined%))
(= (gslt:collection-search:round $lanes $log)
   (let $advanced (gslt:collection-search:advance-lanes $lanes)
     (case $advanced
       (((CollectionLoggedAdvanced $next-lanes $fresh)
         (let $next-log (gslt:automata:append $log $fresh)
           (CollectionLoggedState $next-lanes $next-log)))))))

(: gslt:collection-search:resume (-> Atom Atom Atom %Undefined%))
(= (gslt:collection-search:resume $fuel $lanes $log)
   (if (== $fuel 0) (CollectionLoggedState $lanes $log)
     (let $advanced (gslt:collection-search:advance-lanes $lanes)
       (case $advanced
         (((CollectionLoggedAdvanced $next-lanes $fresh)
           (let* (($next-log (gslt:automata:append $log $fresh))
                  ($remaining (- $fuel 1)))
             (gslt:collection-search:resume $remaining $next-lanes $next-log))))))))

(: gslt:collection-search:lanes-complete (-> Atom %Undefined%))
(= (gslt:collection-search:lanes-complete $lanes)
   (case $lanes
     ((LNil 1)
      ((LCons (CollectionLoggedLane $ordinal $request $state $spent $consumed) $rest)
       (case (gslt:collection-machine:complete $state)
         ((1
           (let* (($receipts (gslt:collection-machine:publication $state))
                  ($firings (gslt:collection-machine:firings $request $receipts))
                  ($available (gslt:automata:length $firings)))
             (if (== $consumed $available)
               (gslt:collection-search:lanes-complete $rest)
               0)))
          (0 0)))))))

(: gslt:collection-search:complete (-> Atom %Undefined%))
(= (gslt:collection-search:complete $state)
   (case $state
     (((CollectionLoggedState $lanes $log)
       (gslt:collection-search:lanes-complete $lanes)))))

(: gslt:collection-search:status-lanes (-> Atom %Undefined%))
(= (gslt:collection-search:status-lanes $lanes)
   (case (gslt:collection-search:lanes-complete $lanes)
     ((1 SearchComplete)
      (0 SearchPending))))

(: gslt:collection-search:publication-log (-> Atom %Undefined%))
(= (gslt:collection-search:publication-log $log) $log)

(: gslt:collection-search:publication (-> Atom %Undefined%))
(= (gslt:collection-search:publication $run)
   (case $run
     (((CollectionLoggedRun $source (CollectionLoggedState $lanes $log))
       (gslt:collection-search:publication-log $log)))))

(: gslt:collection-search:status (-> Atom %Undefined%))
(= (gslt:collection-search:status $run)
   (case $run
     (((CollectionLoggedRun $source $state)
       (case $state
         (((CollectionLoggedState $lanes $log)
           (gslt:collection-search:status-lanes $lanes))))))))

(: gslt:collection-search:run (-> Atom Atom Atom %Undefined%))
(= (gslt:collection-search:run $requests $source $work)
   (let* (($lanes (gslt:collection-search:lanes-begin $requests))
          ($state (gslt:collection-search:resume $work $lanes LNil)))
     (CollectionLoggedRun $source $state)))

(: gslt:collection-search:run-plan (-> Atom Atom Atom %Undefined%))
(= (gslt:collection-search:run-plan $plan $source $work)
   (let $requests (gslt:collection-search:requests-for-source $plan $source)
     (gslt:collection-search:run $requests $source $work)))

(: gslt:collection-search:resume-run (-> Atom Atom %Undefined%))
(= (gslt:collection-search:resume-run $run $extra)
   (case $run
     (((CollectionLoggedRun $source $state)
       (case $state
         (((CollectionLoggedState $lanes $log)
           (let $next (gslt:collection-search:resume $extra $lanes $log)
             (CollectionLoggedRun $source $next)))))))))
