; Whole runs and fair exploration over steps modulo equations, in standard form
; (Machines.ResumableSearchRunner and Complete.Explore over Complete.Normalized.search).
;
; The standard-form data is (Standard laws extrusions), the language's declared
; collection laws and scope-extrusion laws. A run starts at the source's standard
; form, and a committed receipt's target is its firing's target in standard form.
; With no laws the standard form is the pattern itself.
;
; Machine: (ClassMachine phase state program states receipts); phase ClassRunning,
; ClassDone or ClassBlocked; states and receipts newest first.

(: gslt:runner:standard (-> Atom Atom %Undefined%))
(= (gslt:runner:standard $standard $pattern)
   (case $standard
     (((Standard $laws $extrusions) (gslt:laws:standard $laws $extrusions $pattern)))))

(: gslt:runner:target (-> Atom Atom %Undefined%))
(= (gslt:runner:target $standard $receipt)
   (case $receipt
     (((ClassReceipt $pattern $conversions (RuleJobReceipt $job $trace $captured $completed $history $local $target))
       (gslt:runner:standard $standard $target)))))

; A run starts at the source's standard form.
(: gslt:runner:begin (-> Atom Atom Atom %Undefined%))
(= (gslt:runner:begin $plan $standard $source)
   (let* (($start (gslt:runner:standard $standard $source))
          ($program (gslt:classes:begin $plan $start)))
     (ClassMachine ClassRunning $start $program (LCons $start LNil) LNil)))

(: gslt:runner:tick (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:runner:tick $plan $standard $machine $quantum)
   (case $machine
     (((ClassMachine ClassRunning $state $program $states $receipts)
       (let $resumed (gslt:classes:rounds $plan $quantum $program)
         (case $resumed
           (((ClassState $round $reps $entries $log)
             (case $log
               (((LCons $receipt $rest)
                 (let* (($target (gslt:runner:target $standard $receipt))
                        ($fresh (gslt:classes:begin $plan $target)))
                   (ClassMachine ClassRunning $target $fresh (LCons $target $states) (LCons $receipt $receipts))))
                (LNil
                 (if (gslt:classes:entries-complete $plan $entries)
                   (ClassMachine ClassDone $state $resumed $states $receipts)
                   (ClassMachine ClassRunning $state $resumed $states $receipts))))))))))
      ($stopped $machine))))

(: gslt:runner:advance (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:runner:advance $plan $standard $ticks $quantum $machine)
   (if (== $ticks 0) $machine
     (let* (($next (gslt:runner:tick $plan $standard $machine $quantum))
            ($remaining (- $ticks 1)))
       (gslt:runner:advance $plan $standard $remaining $quantum $next))))

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

(: gslt:explore:begin (-> Atom Atom Atom %Undefined%))
(= (gslt:explore:begin $plan $standard $source)
   (let* (($start (gslt:runner:standard $standard $source))
          ($run (gslt:classes:begin $plan $start)))
     (Explorer 0 (LCons (ExploreNode $start LNil (LCons $start LNil) 0 $run 0) LNil))))

(: gslt:explore:children (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:explore:children $plan $standard $born $receipts $states $published)
   (case $published
     ((LNil LNil)
      ((LCons $receipt $rest)
       (let* (($target (gslt:runner:target $standard $receipt))
              ($run (gslt:classes:begin $plan $target))
              ($tail (gslt:explore:children $plan $standard $born $receipts $states $rest)))
         (LCons (ExploreNode $target (LCons $receipt $receipts) (LCons $target $states) $born $run 0) $tail))))))

(: gslt:explore:expand (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:explore:expand $plan $standard $round $node)
   (case $node
     (((ExploreNode $state $receipts $states $born $run $consumed)
       (let $next (gslt:classes:rounds $plan 1 $run)
         (case $next
           (((ClassState $nextRound $reps $entries $log)
             (let* (($length (gslt:automata:length $log))
                    ($new (gslt:complete:drop $consumed $log))
                    ($childBorn (+ $round 1))
                    ($children (gslt:explore:children $plan $standard $childBorn $receipts $states $new)))
               (Expanded (ExploreNode $state $receipts $states $born $next $length) $children))))))))))

(: gslt:explore:expand-all (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:explore:expand-all $plan $standard $round $nodes)
   (case $nodes
     ((LNil (Expanded LNil LNil))
      ((LCons $node $rest)
       (let* (($head (gslt:explore:expand $plan $standard $round $node))
              ($tail (gslt:explore:expand-all $plan $standard $round $rest)))
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

(: gslt:explore:step (-> Atom Atom Atom %Undefined%))
(= (gslt:explore:step $plan $standard $explorer)
   (case $explorer
     (((Explorer $round $nodes)
       (let $expanded (gslt:explore:expand-all $plan $standard $round $nodes)
         (case $expanded
           (((Expanded $nextNodes $children)
             (let* (($seen (gslt:explore:node-states $nextNodes))
                    ($new (gslt:explore:fresh $seen $children))
                    ($all (gslt:automata:append $nextNodes $new))
                    ($next (+ $round 1)))
               (Explorer $next $all))))))))))

; Settled: every node's search is complete and every receipt it published has its child
; (Complete.Settled). A settled explorer's states never change again.
(: gslt:explore:settled (-> Atom Atom %Undefined%))
(= (gslt:explore:settled $plan $nodes)
   (case $nodes
     ((LNil True)
      ((LCons (ExploreNode $state $receipts $states $born $run $consumed) $rest)
       (case $run
         (((ClassState $round $reps $entries $log)
           (if (gslt:classes:entries-complete $plan $entries)
             (let $length (gslt:automata:length $log)
               (if (== $length $consumed) (gslt:explore:settled $plan $rest) False))
             False))))))))

; Up to `work` rounds, stopping once settled (Complete.Settled.roundsUntilSettled).
(: gslt:explore:rounds (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:explore:rounds $plan $standard $work $explorer)
   (if (== $work 0) $explorer
     (case $explorer
       (((Explorer $round $nodes)
         (if (gslt:explore:settled $plan $nodes) $explorer
           (let* (($next (gslt:explore:step $plan $standard $explorer))
                  ($remaining (- $work 1)))
             (gslt:explore:rounds $plan $standard $remaining $next))))))))

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

