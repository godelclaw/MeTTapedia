; Whole runs and fair exploration over steps modulo equations, in standard or canonical
; form (Machines.ResumableSearchRunner and Complete.Explore over Complete.Normalized.search).
;
; The commit data is (Standard laws extrusions), the language's declared collection
; laws and scope-extrusion laws, (Canonical laws extrusions table), which also sorts
; every unordered collection by the plan's name table (gslt_canonical.metta),
; (Reflective quote drop laws extrusions table), which first takes the quote-drop normal
; form of a reflective presentation (gslt:rule:scope-reflective-normalize), or
; (Model quote drop laws extrusions table), which first takes the model normal form: the
; declared collection algebra completed by its wrapper laws, with the name equation
; (gslt:canon:model-normal). A run starts at the source's committed form, and a committed
; receipt's target is its firing's target in committed form. With no laws the standard
; form is the pattern itself.
;
; Machine: (ClassMachine phase state program states receipts); phase ClassRunning,
; ClassDone or ClassBlocked; states and receipts newest first.
;
; A search backend implements the operational part of
; Machines.ResumableSearchRunner.Search.  The plan remains explicit source data;
; the backend selects how that plan is searched and how its retained run and
; receipts are read.  Generic runners do not inspect those representations.

(: gslt:runner:standard (-> Atom Atom %Undefined%))
(= (gslt:runner:standard $standard $pattern)
   (case $standard
     (((Standard $laws $extrusions) (gslt:laws:standard $laws $extrusions $pattern))
      ((Canonical $laws $extrusions $table) (gslt:canon:canonical $table $laws $extrusions $pattern))
      ((Reflective $quote $drop $laws $extrusions $table)
       (let $normal (gslt:rule:scope-reflective-normalize $quote $drop $pattern)
         (gslt:canon:canonical $table $laws $extrusions $normal)))
      ((Model $quote $drop $laws $extrusions $table)
       (let $normal (gslt:canon:model-normal $table $quote $drop $laws $pattern)
         (gslt:canon:canonical $table $laws $extrusions $normal))))))

; Search descriptors are explicit data.  ClassSearch uses the complete-class
; machine.  (CollectionSearch names) derives fresh collection requests from
; the plan and each source; names fixes the canonical target order.
; (CollectionOccurrenceSearch names depth) retains nested matcher and premise
; work, with its original receipt readout and explicit continuation depth.
(: gslt:search:run (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:search:run $backend $plan $source $work)
   (case $backend
     ((ClassSearch
       (let $initial (gslt:classes:begin $plan $source)
         (gslt:classes:rounds $plan $work $initial)))
      ((CollectionSearch $names)
       (gslt:collection-search:run-plan $plan $source $work))
      ((CollectionOccurrenceSearch $names $depth)
       (gslt:occurrence-search:run $names $depth $plan $source $work))
      ((CollectionRootSearch $names)
       (gslt:collection-root:run $plan $source $work)))))

(: gslt:search:resume (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:search:resume $backend $plan $run $work)
   (case $backend
     ((ClassSearch (gslt:classes:rounds $plan $work $run))
      ((CollectionSearch $names)
       (gslt:collection-search:resume-run $run $work))
      ((CollectionOccurrenceSearch $names $depth)
       (gslt:occurrence-search:resume $names $depth $run $work))
      ((CollectionRootSearch $names)
       (gslt:collection-root:rounds $plan $work $run)))))

(: gslt:search:publication (-> Atom Atom %Undefined%))
(= (gslt:search:publication $backend $run)
   (case $backend
     ((ClassSearch
       (case $run
         (((ClassState $round $reps $entries $log) $log))))
      ((CollectionSearch $names)
       (gslt:collection-search:publication $run))
      ((CollectionOccurrenceSearch $names $depth)
       (gslt:occurrence-search:publication $run))
      ((CollectionRootSearch $names)
       (gslt:collection-root:publication $run)))))

(: gslt:search:status (-> Atom Atom Atom %Undefined%))
(= (gslt:search:status $backend $plan $run)
   (case $backend
     ((ClassSearch
       (case $run
         (((ClassState $round $reps $entries $log)
           (if (gslt:classes:entries-complete $plan $entries) SearchComplete SearchPending)))))
      ((CollectionSearch $names)
       (gslt:collection-search:status $run))
      ((CollectionOccurrenceSearch $names $depth)
       (gslt:occurrence-search:status $run))
      ((CollectionRootSearch $names)
       (gslt:collection-root:status $run)))))

(: gslt:search:target (-> Atom Atom Atom %Undefined%))
(= (gslt:search:target $backend $standard $receipt)
   (case $backend
     ((ClassSearch
       (case $receipt
         (((ClassReceipt $pattern $conversions
              (RuleJobReceipt $job $trace $captured $completed $history $local $target))
           (gslt:runner:standard $standard $target)))))
      ((CollectionSearch $names)
       (case $receipt
         (((CollectionPlanFiring $ordinal $request
              (CollectionFiring $source-receipt $target))
           (gslt:canon:canon $names $target)))))
      ((CollectionOccurrenceSearch $names $depth)
       (gslt:occurrence-search:target $names $receipt))
      ((CollectionRootSearch $names)
       (case $receipt
         (((CollectionRootReceipt $ordinal $request $source-receipt $completed $history $target)
           (gslt:canon:canon $names $target))))))))

(: gslt:runner:target (-> Atom Atom Atom %Undefined%))
(= (gslt:runner:target $backend $standard $receipt)
   (gslt:search:target $backend $standard $receipt))

; A run starts at the source's standard form.
(: gslt:runner:begin (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:runner:begin $backend $plan $standard $source)
   (let* (($start (gslt:runner:standard $standard $source))
          ($program (gslt:search:run $backend $plan $start 0)))
     (ClassMachine ClassRunning $start $program (LCons $start LNil) LNil)))

(: gslt:runner:tick (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:runner:tick $backend $plan $standard $machine $quantum)
   (case $machine
     (((ClassMachine ClassRunning $state $program $states $receipts)
       (let* (($resumed (gslt:search:resume $backend $plan $program $quantum))
              ($published (gslt:search:publication $backend $resumed)))
         (case $published
           ((LNil
             (let $status (gslt:search:status $backend $plan $resumed)
               (case $status
                 ((SearchComplete (ClassMachine ClassDone $state $resumed $states $receipts))
                  (SearchBlocked (ClassMachine ClassBlocked $state $resumed $states $receipts))
                  (SearchPending (ClassMachine ClassRunning $state $resumed $states $receipts))))))
            ((LCons $receipt $rest)
             (let* (($target (gslt:search:target $backend $standard $receipt))
                    ($fresh (gslt:search:run $backend $plan $target 0)))
               (ClassMachine ClassRunning $target $fresh (LCons $target $states) (LCons $receipt $receipts))))))))
      ($stopped $machine))))

(: gslt:runner:advance (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:runner:advance $backend $plan $standard $ticks $quantum $machine)
   (if (== $ticks 0) $machine
     (let* (($next (gslt:runner:tick $backend $plan $standard $machine $quantum))
            ($remaining (- $ticks 1)))
       (gslt:runner:advance $backend $plan $standard $remaining $quantum $next))))

(: gslt:runner:reverse-onto (-> Atom Atom %Undefined%))
(= (gslt:runner:reverse-onto $items $tail)
   (case $items
     ((LNil $tail)
      ((LCons $item $rest) (gslt:runner:reverse-onto $rest (LCons $item $tail))))))

(: gslt:runner:trace (-> Atom %Undefined%))
(= (gslt:runner:trace $machine)
   (case $machine
     (((ClassMachine $phase $state $program $states $receipts)
       (let $ordered (gslt:runner:reverse-onto $states LNil) (RunTrace $phase $ordered))))))

; Fair exploration of every run.
;
; Node: (ExploreNode state receipts states born run consumed). Explorer: (Explorer round nodes).
; A state is explored once: a child whose state already has a node is dropped.

(: gslt:explore:begin (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:explore:begin $backend $plan $standard $source)
   (let* (($start (gslt:runner:standard $standard $source))
          ($run (gslt:search:run $backend $plan $start 0)))
     (Explorer 0 (LCons (ExploreNode $start LNil (LCons $start LNil) 0 $run 0) LNil))))

(: gslt:explore:children (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:explore:children $backend $plan $standard $born $receipts $states $published)
   (case $published
     ((LNil LNil)
      ((LCons $receipt $rest)
       (let* (($target (gslt:search:target $backend $standard $receipt))
              ($run (gslt:search:run $backend $plan $target 0))
              ($tail (gslt:explore:children $backend $plan $standard $born $receipts $states $rest)))
         (LCons (ExploreNode $target (LCons $receipt $receipts) (LCons $target $states) $born $run 0) $tail))))))

(: gslt:explore:expand (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:explore:expand $backend $plan $standard $round $node)
   (case $node
     (((ExploreNode $state $receipts $states $born $run $consumed)
       (let* (($next (gslt:search:resume $backend $plan $run 1))
              ($published (gslt:search:publication $backend $next))
              ($length (gslt:automata:length $published))
              ($new (gslt:complete:drop $consumed $published))
              ($childBorn (+ $round 1))
              ($children (gslt:explore:children $backend $plan $standard $childBorn $receipts $states $new)))
         (Expanded (ExploreNode $state $receipts $states $born $next $length) $children))))))

(: gslt:explore:expand-all (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:explore:expand-all $backend $plan $standard $round $nodes)
   (case $nodes
     ((LNil (Expanded LNil LNil))
      ((LCons $node $rest)
       (let* (($head (gslt:explore:expand $backend $plan $standard $round $node))
              ($tail (gslt:explore:expand-all $backend $plan $standard $round $rest)))
         (case $head
           (((Expanded $nextNode $children)
             (case $tail
               (((Expanded $nextNodes $moreChildren)
                 (let $all (gslt:automata:append $children $moreChildren)
                   (Expanded (LCons $nextNode $nextNodes) $all)))))))))))))

; Whether a state is among the seen states.
(: gslt:explore:seen (-> Atom Atom %Undefined%))
(= (gslt:explore:seen $state $seen)
   (case $seen
     ((LNil False)
      ((LCons $other $rest) (if (== $state $other) True (gslt:explore:seen $state $rest))))))

; The children whose states are new (Complete.Explore.fresh): a child whose state is seen, or is
; an earlier child's, is dropped.
(: gslt:explore:fresh (-> Atom Atom %Undefined%))
(= (gslt:explore:fresh $seen $children)
   (case $children
     ((LNil LNil)
      ((LCons (ExploreNode $state $receipts $states $born $run $consumed) $rest)
       (if (gslt:explore:seen $state $seen)
         (gslt:explore:fresh $seen $rest)
         (let $tail (gslt:explore:fresh (LCons $state $seen) $rest)
           (LCons (ExploreNode $state $receipts $states $born $run $consumed) $tail)))))))

(: gslt:explore:step (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:explore:step $backend $plan $standard $explorer)
   (case $explorer
     (((Explorer $round $nodes)
       (let $expanded (gslt:explore:expand-all $backend $plan $standard $round $nodes)
         (case $expanded
           (((Expanded $nextNodes $children)
             (let* (($seen (gslt:explore:node-states $nextNodes))
                    ($new (gslt:explore:fresh $seen $children))
                    ($all (gslt:automata:append $nextNodes $new))
                    ($next (+ $round 1)))
               (Explorer $next $all))))))))))

; Settled: every node's search is complete and every receipt it published has its child
; (Complete.Settled). A settled explorer's states never change again.
(: gslt:explore:settled (-> Atom Atom Atom %Undefined%))
(= (gslt:explore:settled $backend $plan $nodes)
   (case $nodes
     ((LNil True)
      ((LCons (ExploreNode $state $receipts $states $born $run $consumed) $rest)
       (case (gslt:search:status $backend $plan $run)
         ((SearchComplete
           (let* (($published (gslt:search:publication $backend $run))
                  ($length (gslt:automata:length $published)))
             (if (== $length $consumed) (gslt:explore:settled $backend $plan $rest) False)))
          (SearchBlocked False)
          (SearchPending False)))))))

; Up to `work` rounds, stopping once settled (Complete.Settled.roundsUntilSettled).
(: gslt:explore:rounds (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:explore:rounds $backend $plan $standard $work $explorer)
   (if (== $work 0) $explorer
     (case $explorer
       (((Explorer $round $nodes)
         (if (gslt:explore:settled $backend $plan $nodes) $explorer
           (let* (($next (gslt:explore:step $backend $plan $standard $explorer))
                  ($remaining (- $work 1)))
             (gslt:explore:rounds $backend $plan $standard $remaining $next))))))))

(: gslt:explore:states (-> Atom %Undefined%))
(= (gslt:explore:states $explorer)
   (case $explorer
     (((Explorer $round $nodes) (gslt:explore:node-states $nodes)))))

(: gslt:explore:node-states (-> Atom %Undefined%))
(= (gslt:explore:node-states $nodes)
   (case $nodes
     ((LNil LNil)
      ((LCons (ExploreNode $state $receipts $states $born $run $consumed) $rest)
       (let $tail (gslt:explore:node-states $rest) (LCons $state $tail))))))


; The explored transition graph (Complete.Graph.edges): every node's published receipts with
; their standard-form targets, as (Edge state receipt target). With states explored once, an
; edge may end at a node found along another path.
(: gslt:explore:edges (-> Atom Atom Atom %Undefined%))
(= (gslt:explore:edges $backend $standard $explorer)
   (case $explorer
     (((Explorer $round $nodes) (gslt:explore:node-edges $backend $standard $nodes)))))

(: gslt:explore:node-edges (-> Atom Atom Atom %Undefined%))
(= (gslt:explore:node-edges $backend $standard $nodes)
   (case $nodes
     ((LNil LNil)
      ((LCons (ExploreNode $state $receipts $states $born $run $consumed) $rest)
       (let* (($published (gslt:search:publication $backend $run))
              ($mine (gslt:explore:receipt-edges $backend $standard $state $published))
              ($tail (gslt:explore:node-edges $backend $standard $rest)))
         (gslt:automata:append $mine $tail))))))

(: gslt:explore:receipt-edges (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:explore:receipt-edges $backend $standard $state $receipts)
   (case $receipts
     ((LNil LNil)
      ((LCons $receipt $rest)
       (let* (($target (gslt:search:target $backend $standard $receipt))
              ($tail (gslt:explore:receipt-edges $backend $standard $state $rest)))
         (LCons (Edge $state $receipt $target) $tail))))))

; Root-collection backend. The generic runner and explorer use only the
; five gslt:search operations; this backend owns the representations below.
(: gslt:collection-root:raw-tag (-> Atom Atom Atom %Undefined%))
(= (gslt:collection-root:raw-tag $index $query $receipts)
   (case $receipts
     ((LNil LNil)
      ((LCons $receipt $rest)
       (let $later (gslt:collection-root:raw-tag $index $query $rest)
         (LCons (CollectionPlanMatch $index $query $receipt) $later))))))

(: gslt:collection-root:raw-publication (-> Atom %Undefined%))
(= (gslt:collection-root:raw-publication $jobs)
   (case $jobs
     ((LNil LNil)
      ((LCons (CollectionPlanJob $index $query $state) $rest)
       (let* (($receipts (gslt:collection-machine:publication $state))
              ($first (gslt:collection-root:raw-tag $index $query $receipts))
              ($later (gslt:collection-root:raw-publication $rest)))
         (gslt:automata:append $first $later))))))

(: gslt:collection-root:frames-begin (-> Atom Atom Atom %Undefined%))
(= (gslt:collection-root:frames-begin $environment $type $matches)
   (case $matches
     ((LNil LNil)
      ((LCons (CollectionPlanMatch $index $query $receipt) $rest)
       (case $query
         (((CollectionRequest
             (ScopedMatcherRequest $rule $spec $ambient $site $path $match-depth $initial
               (PCollection $kind $schemas $tail) $target) $schema-index)
           (case $receipt
             (((CollectionReceipt (CollectionAllocation $values $residual $decisions) $answer)
               (let* (($presented (gslt:collection-backend:ordinary-target $kind $values $residual))
                      ($depth (gslt:deep:nodes $presented))
                      ($frame (gslt:collection-backend:frame-begin
                                $environment $depth $type $index $query $receipt))
                      ($later (gslt:collection-root:frames-begin $environment $type $rest)))
                 (LCons $frame $later))))))))))))

(: gslt:collection-root:begin (-> Atom Atom %Undefined%))
(= (gslt:collection-root:begin $plan $source)
   (case $plan
     (((CompletePlan
         (PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free)
         $permissions $bound $expected $rules $equations $admitted)
       (if (gslt:premise:open-well-sorted $declarations $free $bound $expected $source)
         (let* (($requests (gslt:collection-search:requests-for-source $plan $source))
                ($state (gslt:collection-plan:start $requests)))
           (CollectionRootMatching $source 0 $state))
         (CollectionRootRejected $source))))))

(: gslt:collection-root:tick (-> Atom Atom %Undefined%))
(= (gslt:collection-root:tick $plan $run)
   (case $plan
     (((CompletePlan $environment $permissions $bound $expected $rules $equations $admitted)
       (case $run
         (((CollectionRootRejected $source) $run)
          ((CollectionRootMatching $source $spent $state)
           (case (gslt:collection-plan:complete $state)
             ((1
               (let* (($matches (gslt:collection-root:raw-publication $state))
                      ($frames (gslt:collection-root:frames-begin $environment $expected $matches))
                      ($started (gslt:collection-backend:state-begin $frames)))
                 (CollectionRootContinuing $source $started)))
              (0
               (let* (($next (gslt:collection-plan:resume 1 $state))
                      ($next-spent (+ $spent 1)))
                 (CollectionRootMatching $source $next-spent $next))))))
          ((CollectionRootContinuing $source $state)
           (let $next (gslt:collection-backend:state-run $environment 1 $state)
             (CollectionRootContinuing $source $next)))))))))

(: gslt:collection-root:rounds (-> Atom Atom Atom %Undefined%))
(= (gslt:collection-root:rounds $plan $work $run)
   (if (== $work 0) $run
     (let* (($next (gslt:collection-root:tick $plan $run))
            ($remaining (- $work 1)))
       (gslt:collection-root:rounds $plan $remaining $next))))

(: gslt:collection-root:run (-> Atom Atom Atom %Undefined%))
(= (gslt:collection-root:run $plan $source $work)
   (let $started (gslt:collection-root:begin $plan $source)
     (gslt:collection-root:rounds $plan $work $started)))

; Erasing the auxiliary ordinary validation trace maps each log occurrence
; to one source packet. It never deduplicates equal outcomes or origins.
(: gslt:collection-root:observations (-> Atom %Undefined%))
(= (gslt:collection-root:observations $log)
   (case $log
     ((LNil LNil)
      ((LCons (CollectionContinued $index $query $receipt
                 (RootAnswer $validation $captured $completed $history $target)) $rest)
       (let $later (gslt:collection-root:observations $rest)
         (LCons (CollectionRootReceipt $index $query $receipt $completed $history $target) $later))))))

(: gslt:collection-root:publication (-> Atom %Undefined%))
(= (gslt:collection-root:publication $run)
   (case $run
     (((CollectionRootRejected $source) LNil)
      ((CollectionRootMatching $source $spent $state) LNil)
      ((CollectionRootContinuing $source (CollectionContinuedState $frames $log))
       (gslt:collection-root:observations $log)))))

(: gslt:collection-root:status (-> Atom %Undefined%))
(= (gslt:collection-root:status $run)
   (case $run
     (((CollectionRootRejected $source) SearchBlocked)
      ((CollectionRootMatching $source $spent $state) SearchPending)
      ((CollectionRootContinuing $source $state)
       (case (gslt:collection-backend:state-settled $state)
         ((1 SearchComplete) (0 SearchPending)))))))
