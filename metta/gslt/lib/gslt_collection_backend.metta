; Adapter from proof-relevant collection allocation to the ordinary scoped
; matcher payload consumed by the complete root service. Load after
; gslt_complete.metta and gslt_collection_machine.metta.

(: gslt:collection-backend:ordinary-target (-> Atom Atom Atom %Undefined%))
(= (gslt:collection-backend:ordinary-target $kind $values $residual)
   (let $presented (gslt:automata:append $values $residual)
     (PCollection $kind $presented RNone)))

(: gslt:collection-backend:ordinary-request
  (-> Atom Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:collection-backend:ordinary-request
     $rule $spec $ambient $site $path $depth $initial $schema $target)
   (ScopedMatcherRequest $rule $spec $ambient $site $path $depth $initial $schema $target))

(: gslt:collection-backend:filter-assignment (-> Atom Atom %Undefined%))
(= (gslt:collection-backend:filter-assignment $assignment $answers)
   (case $answers
     ((LNil LNil)
      ((LCons (ScopedMatcherAnswer $actual $trace) $tail)
       (let $later (gslt:collection-backend:filter-assignment $assignment $tail)
         (if (== $actual $assignment)
           (LCons (ScopedMatcherAnswer $actual $trace) $later)
           $later))))))

(: gslt:collection-backend:answers (-> Atom Atom %Undefined%))
(= (gslt:collection-backend:answers $request $assignment)
   (let $answers (gslt:complete:matcher-answers $request)
     (gslt:collection-backend:filter-assignment $assignment $answers)))

; Feed a finite certified answer frontier through the generic post-match
; continuation.  The recursion only schedules answers; typing, premises and
; reduct construction remain owned by gslt:descent:continue-root-answer.
(: gslt:collection-backend:continue-answers
  (-> Atom Atom Atom Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:collection-backend:continue-answers
     $environment $depth $bound $type $source $index $rule $spec $answers $tail $next)
   (case $answers
     ((LNil (Some (PremiseExpansion $next LNil LNil)))
      ((LCons $answer $rest)
       (case (gslt:collection-backend:continue-answers
               $environment $depth $bound $type $source $index $rule $spec $rest $tail $next)
         (((Some (PremiseExpansion $later LNil LNil))
           (gslt:descent:continue-root-answer $environment $depth $bound $type $source
             $index $rule $spec $answer $tail $later))
          ($bad None)))))))

(: gslt:collection-backend:expansion-state (-> Atom %Undefined%))
(= (gslt:collection-backend:expansion-state $expanded)
   (case $expanded
     (((Some (PremiseExpansion $tasks $answers $unresolved))
       (PremiseState $tasks $answers $unresolved 0))
      ($bad (PremiseState LNil LNil LNil 0)))))

; Start the shared typed and premise continuation from a raw match. Premises
; may supply variables needed by the right-hand side.
(: gslt:collection-backend:begin-match
  (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:collection-backend:begin-match
     $environment $depth $type $index $query $receipt)
   (case $query
     (((CollectionRequest
           (ScopedMatcherRequest $rule $spec $ambient $site $path $match-depth $initial
             (PCollection $kind $schemas $rest) $target) $schema-index)
       (case $receipt
         (((CollectionReceipt (CollectionAllocation $values $residual $decisions)
             (ScopedMatcherAnswer $assignment $trace))
       (let* (($presented (gslt:collection-backend:ordinary-target $kind $values $residual))
              ($request (gslt:collection-backend:ordinary-request
                $rule $spec $ambient $site $path $match-depth $initial
                (PCollection $kind $schemas $rest) $presented))
              ($answers (gslt:collection-backend:answers $request $assignment))
              ($selected (gslt:complete:take 1 $answers))
              ($next-depth (+ $depth 1))
              ($goal (DescentRootGoal $next-depth LNil $type $presented $index))
              ($tail (DescentDone $goal))
              ($expanded (gslt:collection-backend:continue-answers
                $environment $depth LNil $type $presented $index $rule $spec
                $selected $tail LNil)))
         (gslt:collection-backend:expansion-state $expanded)))))))))

; Existing firing callers use the same continuation without inspecting or
; publishing the provisional target.
(: gslt:collection-backend:begin (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:collection-backend:begin $environment $depth $type $firing)
   (case $firing
     (((CollectionPlanFiring $index $query (CollectionFiring $receipt $raw-target))
       (gslt:collection-backend:begin-match
         $environment $depth $type $index $query $receipt)))))

; One raw origin owns one retained typed/premise state.
(: gslt:collection-backend:frame-begin
  (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:collection-backend:frame-begin
     $environment $depth $type $index $query $receipt)
   (let $state (gslt:collection-backend:begin-match
                 $environment $depth $type $index $query $receipt)
     (CollectionContinuation $index $query $receipt $depth $state)))

(: gslt:collection-backend:frame-run (-> Atom Atom Atom %Undefined%))
(= (gslt:collection-backend:frame-run $environment $work $frame)
   (case $frame
     (((CollectionContinuation $index $query $receipt $depth $state)
       (let $next (gslt:descent:run $environment $work $state)
         (CollectionContinuation $index $query $receipt $depth $next))))))

; A published result must retain the captures of this raw origin. The RHS
; and complete premise history are produced by the shared continuation.
(: gslt:collection-backend:frame-results
  (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:collection-backend:frame-results $index $query $receipt $expected $answers)
   (case $answers
     ((LNil LNil)
      ((LCons (PremiseResult $goal (RootAnswer $trace $captured $completed $history $target)) $rest)
       (let $later (gslt:collection-backend:frame-results $index $query $receipt $expected $rest)
         (if (== $captured $expected)
           (LCons (CollectionContinued $index $query $receipt
                    (RootAnswer $trace $captured $completed $history $target)) $later)
           $later))))))

(: gslt:collection-backend:frame-publication (-> Atom %Undefined%))
(= (gslt:collection-backend:frame-publication $frame)
   (case $frame
     (((CollectionContinuation $index $query
         (CollectionReceipt $allocation (ScopedMatcherAnswer $captured $trace)) $depth
         (PremiseState $tasks $answers $unresolved $work))
       (gslt:collection-backend:frame-results $index $query
         (CollectionReceipt $allocation (ScopedMatcherAnswer $captured $trace))
         $captured $answers)))))

(: gslt:collection-backend:frame-settled (-> Atom %Undefined%))
(= (gslt:collection-backend:frame-settled $frame)
   (case $frame
     (((CollectionContinuation $index $query $receipt $depth
         (PremiseState $tasks $answers $unresolved $work))
       (case $tasks ((LNil 1) ($pending 0)))))))

(: gslt:collection-backend:frames-publication (-> Atom %Undefined%))
(= (gslt:collection-backend:frames-publication $frames)
   (case $frames
     ((LNil LNil)
      ((LCons $frame $rest)
       (let* (($first (gslt:collection-backend:frame-publication $frame))
              ($later (gslt:collection-backend:frames-publication $rest)))
         (gslt:automata:append $first $later))))))

; Drain each origin's own suffix before interleaving the publications.
(: gslt:collection-backend:advance-frames (-> Atom Atom %Undefined%))
(= (gslt:collection-backend:advance-frames $environment $frames)
   (case $frames
     ((LNil (CollectionContinuedAdvanced LNil LNil))
      ((LCons $frame $rest)
       (let* (($previous (gslt:collection-backend:frame-publication $frame))
              ($consumed (gslt:automata:length $previous))
              ($next (gslt:collection-backend:frame-run $environment 1 $frame))
              ($published (gslt:collection-backend:frame-publication $next))
              ($fresh (gslt:complete:drop $consumed $published))
              ($later (gslt:collection-backend:advance-frames $environment $rest)))
         (case $later
           (((CollectionContinuedAdvanced $next-rest $more)
             (let $all (gslt:automata:append $fresh $more)
               (CollectionContinuedAdvanced (LCons $next $next-rest) $all))))))))))

(: gslt:collection-backend:state-begin (-> Atom %Undefined%))
(= (gslt:collection-backend:state-begin $frames)
   (let $log (gslt:collection-backend:frames-publication $frames)
     (CollectionContinuedState $frames $log)))

(: gslt:collection-backend:state-resume (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:collection-backend:state-resume $environment $work $frames $log)
   (if (== $work 0) (CollectionContinuedState $frames $log)
     (let $advanced (gslt:collection-backend:advance-frames $environment $frames)
       (case $advanced
         (((CollectionContinuedAdvanced $next $fresh)
           (let* (($next-log (gslt:automata:append $log $fresh))
                  ($remaining (- $work 1)))
             (gslt:collection-backend:state-resume $environment $remaining $next $next-log))))))))

(: gslt:collection-backend:state-run (-> Atom Atom Atom %Undefined%))
(= (gslt:collection-backend:state-run $environment $work $state)
   (case $state
     (((CollectionContinuedState $frames $log)
       (gslt:collection-backend:state-resume $environment $work $frames $log)))))

(: gslt:collection-backend:frames-settled (-> Atom %Undefined%))
(= (gslt:collection-backend:frames-settled $frames)
   (case $frames
     ((LNil 1)
      ((LCons $frame $rest)
       (case (gslt:collection-backend:frame-settled $frame)
         ((1 (gslt:collection-backend:frames-settled $rest))
          (0 0)))))))

(: gslt:collection-backend:state-settled (-> Atom %Undefined%))
(= (gslt:collection-backend:state-settled $state)
   (case $state
     (((CollectionContinuedState $frames $log)
       (gslt:collection-backend:frames-settled $frames)))))
