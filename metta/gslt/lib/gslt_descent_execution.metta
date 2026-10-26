; Scheduled structural-descent execution of authored rules and premises.
; Load after gslt_scoped_execution (matcher, query machine, checks, instantiation).
;
; This is the machine of StructuralDescentScheduledExecution. It differs from the
; ordered premise machine (gslt:premise:machine-*) in two ways: a recursive step
; searches every declaration, not only earlier ones, and every goal, continuation
; and frame carries a recursion depth. A root at depth d+1 runs its premises at
; depth d; a root at depth 0 records (DescentDepthExhausted index) and is not searched.
;
; Goals:
;   (DescentPremiseGoal d context premise initial)
;   (DescentPremisesGoal d context premises initial)
;   (DescentQuantifiedGoal d context parameter body index elements initial)
;   (DescentRootGoal d bound type source index)
;   (DescentStepsGoal d bound type source limit)
; Results reuse (PremiseResult goal answer) with the ordered machine's answers.
; The state reuses (PremiseState agenda answers unresolved work) and gslt:premise:machine-commit.

(: gslt:descent:deliver (-> Atom Atom Atom %Undefined%))
(= (gslt:descent:deliver $environment $result $continuation)
   (case $continuation
     (((DescentDone $outer)
       (Some (PremiseExpansion LNil (LCons $result LNil) LNil)))
      ((DescentNext $depth $context $premise $premises $initial $tail)
       (case $result
         (((PremiseResult $goal (PremiseAnswer $assignment $event))
           (let $next (gslt:premise:context-next $context)
             (Some (PremiseExpansion
               (LCons (DescentEvaluate (DescentPremisesGoal $depth $next $premises $assignment)
                 (DescentPrepend $depth $context $premise $premises $initial $assignment $event $tail)) LNil)
               LNil LNil))))
          ($badResult None))))
      ((DescentPrepend $depth $context $premise $premises $initial $middle $event $tail)
       (case $result
         (((PremiseResult $goal (PremisesAnswer $assignment $events))
           (Some (PremiseExpansion
             (LCons (DescentDeliver
               (PremiseResult (DescentPremisesGoal $depth $context (LCons $premise $premises) $initial)
                 (PremisesAnswer $assignment (LCons $event $events))) $tail) LNil)
             LNil LNil)))
          ($badResult None))))
      ((DescentQuantifier $depth $context $collection $parameter $body $initial $kind $elements $tail)
       (case $result
         (((PremiseResult $goal (QuantifiedAnswer $assignment $events))
           (case $context
             (((PremiseContext $index $rule $spec $bound $premise $quantifiers)
               (Some (PremiseExpansion
                 (LCons (DescentDeliver
                   (PremiseResult (DescentPremiseGoal $depth $context (ForAll $collection $parameter $body) $initial)
                     (PremiseAnswer $assignment (PremiseQuantifiedEvent $premise $quantifiers $kind $events)))
                   $tail) LNil) LNil LNil)))
              ($badContext None))))
          ($badResult None))))
      ((DescentElement $depth $context $parameter $body $index $element $elements $initial $tail)
       (case $result
         (((PremiseResult $goal (PremiseAnswer $assignment $event))
           (let* (($restored $initial)
                  ($next (+ $index 1)))
             (Some (PremiseExpansion
               (LCons (DescentEvaluate
                 (DescentQuantifiedGoal $depth $context $parameter $body $next $elements $restored)
                 (DescentPrependElement $depth $context $parameter $body $index $element $elements
                   $initial $assignment $event $tail)) LNil) LNil LNil))))
          ($badResult None))))
      ((DescentPrependElement $depth $context $parameter $body $index $element $elements $initial $middle $event $tail)
       (case $result
         (((PremiseResult $goal (QuantifiedAnswer $assignment $events))
           (Some (PremiseExpansion
             (LCons (DescentDeliver
               (PremiseResult (DescentQuantifiedGoal $depth $context $parameter $body $index (LCons $element $elements) $initial)
                 (QuantifiedAnswer $assignment
                   (LCons (QuantifiedElement $index $element (LCons $event LNil)) $events)))
               $tail) LNil) LNil LNil)))
          ($badResult None))))
      ((DescentRootBody $depth $bound $type $source $index $rule $spec $trace $captured $tail)
       (gslt:descent:root-body-deliver $environment $result $continuation))
      ((DescentSearchedRoot $depth $bound $type $source $index $limit $tail)
       (case $result
         (((PremiseResult $goal (RootAnswer $trace $captured $completed $events $target))
           (Some (PremiseExpansion
             (LCons (DescentDeliver
               (PremiseResult (DescentStepsGoal $depth $bound $type $source $limit)
                 (StepsAnswer $index $trace $captured $completed $events $target)) $tail) LNil)
             LNil LNil)))
          ($badResult None))))
      ((DescentStepped $depth $call $tail)
       (gslt:descent:stepped-deliver $environment $result $continuation))
      ($unsupported None))))

(: gslt:descent:root-body-deliver (-> Atom Atom Atom %Undefined%))
(= (gslt:descent:root-body-deliver $environment $result $continuation) (case (gslt:premise:matching-environment $environment) (((PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free) (case $continuation (((DescentRootBody $depth $bound $type $source $index $rule $spec $trace $captured $tail) (case $result (((PremiseResult $goal (PremisesAnswer $completed $history)) (let* (($operation (gslt:premise:substitution-presentation $reflection $rule)) ($ambient (gslt:automata:length $bound)) ($outer (+ $depth 1))) (case (gslt:rule:scope-reduct $operation $rule $spec $ambient $completed) ((None (Some (PremiseExpansion LNil LNil (LCons (PremiseTargetProjection $index) LNil)))) ((Some $target) (if (gslt:premise:open-well-sorted $declarations $free $bound $type $target) (Some (PremiseExpansion (LCons (DescentDeliver (PremiseResult (DescentRootGoal $outer $bound $type $source $index) (RootAnswer $trace $captured $completed $history $target)) $tail) LNil) LNil LNil)) (Some (PremiseExpansion LNil LNil LNil)))) ($badTarget None))))) ($badResult None)))) ($badContinuation None)))) ($badEnvironment None))))

(: gslt:descent:stepped-deliver (-> Atom Atom Atom %Undefined%))
(= (gslt:descent:stepped-deliver $environment $result $continuation) (case $continuation (((DescentStepped $depth $call $tail) (case $call (((PremiseStepCall $context $premise $initial $binders $type $source $target-schema) (case $context (((PremiseContext $rule-index $rule $spec $bound $premise-index $quantifiers) (case $result (((PremiseResult $goal (StepsAnswer $index $trace $captured $completed $history $target)) (let* (($ambient (gslt:automata:length $bound)) ($local (gslt:automata:length $binders)) ($request (ScopedMatcherRequest $rule $spec $ambient (RulePremise $premise-index $quantifiers 1) LNil $local $initial $target-schema $target)) ($matcher (gslt:premise:matching-start $environment $request))) (Some (PremiseExpansion (LCons (DescentTargetMatch $depth $call $index $trace $captured $completed $history $target $matcher 0 $tail) LNil) LNil LNil)))) ($badResult None)))) ($badContext None)))) ($badCall None)))) ($badContinuation None))))

(: gslt:descent:evaluate (-> Atom Atom Atom %Undefined%))
(= (gslt:descent:evaluate $environment $goal $continuation) (case (gslt:premise:matching-environment $environment) (((PremiseEnvironment $declarations $rewrites $specifications (PremiseProvider $signatures $rows) $reflection $free) (let $all (gslt:automata:length $rewrites) (case $goal (((DescentPremiseGoal $depth $context $premise $initial) (case $context (((PremiseContext $ruleIndex $rule $spec $bound $premiseIndex $quantifiers) (case $premise (((RelationQuery $relation $arguments) (let $request (PremiseQueryRequest $context $relation $arguments $initial) (Some (PremiseExpansion (LCons (DescentQuery $depth $request (PremiseState (LCons PremiseQueryStart LNil) LNil LNil 0) 0 $continuation) LNil) LNil LNil)))) ((Freshness $name $subjectSchema) (let* (($ambient (gslt:automata:length $bound)) ($nameOption (case (gslt:automata:binding $name $initial) ((None (Some $name)) ((Some $stored) (case (gslt:rule:scope-instantiate-value $stored $ambient 0 LNil) (((Some (FVar $atom)) (Some $atom)) ($nonName None)))) ($badLookup None))))) (case $nameOption ((None (Some (PremiseExpansion LNil LNil (LCons (PremiseFreshnessProjection $premiseIndex $quantifiers) LNil)))) ((Some $atom) (case (gslt:rule:scope-instantiate-at None $rule $spec $ambient (RulePremise $premiseIndex $quantifiers 0) LNil 0 $initial $subjectSchema) ((None (Some (PremiseExpansion LNil LNil (LCons (PremiseFreshnessProjection $premiseIndex $quantifiers) LNil)))) ((Some $subject) (if (gslt:premise:fresh $atom $subject) (Some (PremiseExpansion (LCons (DescentDeliver (PremiseResult $goal (PremiseAnswer $initial (PremiseFreshnessEvent $premiseIndex $quantifiers $atom $subject))) $continuation) LNil) LNil LNil)) (Some (PremiseExpansion LNil LNil LNil)))) ($badSubject None)))) ($badName None))))) ((ForAll $collection $parameter $body) (let $ambient (gslt:automata:length $bound) (case (gslt:premise:scope-collection $ambient $initial $collection) ((None (Some (PremiseExpansion LNil LNil (LCons (PremiseCollectionProjection $premiseIndex $quantifiers $collection) LNil)))) ((Some (FiniteCollection $kind $elements)) (Some (PremiseExpansion (LCons (DescentEvaluate (DescentQuantifiedGoal $depth $context $parameter $body 0 $elements $initial) (DescentQuantifier $depth $context $collection $parameter $body $initial $kind $elements $continuation)) LNil) LNil LNil))))))) ((Congruence $sourceSchema $targetSchema) (case (gslt:premise:source-type $declarations $rule $sourceSchema) ((None (Some (PremiseExpansion LNil LNil (LCons (PremiseStepSort $premiseIndex $quantifiers) LNil)))) ((Some $type) (let $ambient (gslt:automata:length $bound) (case (gslt:rule:scope-instantiate-at None $rule $spec $ambient (RulePremise $premiseIndex $quantifiers 0) LNil 0 $initial $sourceSchema) ((None (Some (PremiseExpansion LNil LNil (LCons (PremiseStepProjection $premiseIndex $quantifiers) LNil)))) ((Some $actualSource) (Some (PremiseExpansion (LCons (DescentEvaluate (DescentStepsGoal $depth $bound $type $actualSource $all) (DescentStepped $depth (PremiseStepCall $context $premise $initial LNil $type $actualSource $targetSchema) $continuation)) LNil) LNil LNil))) ($badProjection None))))) ($badType None)))) ((ScopedStep $binders $type $sourceSchema $targetSchema) (let* (($ambient (gslt:automata:length $bound)) ($local (gslt:automata:length $binders)) ($effectiveBound (gslt:automata:append $binders $bound))) (case (gslt:rule:scope-instantiate-at None $rule $spec $ambient (RulePremise $premiseIndex $quantifiers 0) LNil $local $initial $sourceSchema) ((None (Some (PremiseExpansion LNil LNil (LCons (PremiseStepProjection $premiseIndex $quantifiers) LNil)))) ((Some $actualSource) (Some (PremiseExpansion (LCons (DescentEvaluate (DescentStepsGoal $depth $effectiveBound $type $actualSource $all) (DescentStepped $depth (PremiseStepCall $context $premise $initial $binders $type $actualSource $targetSchema) $continuation)) LNil) LNil LNil))) ($badProjection None))))) ($badPremise None)))) ($badContext None)))) ((DescentPremisesGoal $depth $context $premises $initial) (case $premises ((LNil (Some (PremiseExpansion (LCons (DescentDeliver (PremiseResult $goal (PremisesAnswer $initial LNil)) $continuation) LNil) LNil LNil))) ((LCons $premise $rest) (Some (PremiseExpansion (LCons (DescentEvaluate (DescentPremiseGoal $depth $context $premise $initial) (DescentNext $depth $context $premise $rest $initial $continuation)) LNil) LNil LNil))) ($badPremises None)))) ((DescentQuantifiedGoal $depth $context $parameter $body $index $elements $initial) (case $elements ((LNil (Some (PremiseExpansion (LCons (DescentDeliver (PremiseResult $goal (QuantifiedAnswer $initial LNil)) $continuation) LNil) LNil LNil))) ((LCons $element $rest) (case $context (((PremiseContext $ruleIndex $rule $spec $bound $premise $quantifiers) (let* (($ambient (gslt:automata:length $bound)) ($local (gslt:premise:scope-local-value $ambient $element)) ($assignment (gslt:premise:scope-bind $parameter $local $initial)) ($quantified (gslt:premise:context-quantified $context))) (if (gslt:premise:check-assignment $declarations $free $bound $rule $spec $assignment) (Some (PremiseExpansion (LCons (DescentEvaluate (DescentPremiseGoal $depth $quantified $body $assignment) (DescentElement $depth $context $parameter $body $index $element $rest $initial $continuation)) LNil) LNil LNil)) (Some (PremiseExpansion LNil LNil (LCons (PremiseQuantifiedAssignment $premise $quantifiers $index) LNil)))))) ($badContext None)))) ($badElements None)))) ((DescentRootGoal $depth $bound $type $source $index) (if (== $depth 0) (Some (PremiseExpansion LNil LNil (LCons (DescentDepthExhausted $index) LNil))) (let $inner (- $depth 1) (case (gslt:rule:row-at $index $rewrites) ((None (Some (PremiseExpansion LNil LNil (LCons (PremiseRuleUnavailable $index) LNil)))) ((Some $rule) (case $rule (((ScopedRewriteRuleV1 $ruleName $ruleTypes $premises $left $right $bindings) (case (gslt:premise:specification $index $specifications) ((None (Some (PremiseExpansion LNil LNil (LCons (PremiseBindingUnavailable $index) LNil)))) ((Some $spec) (if (gslt:premise:binding-admitted $rule $spec) (if (gslt:premise:open-well-sorted $declarations $free $bound $type $source) (let* (($ambient (gslt:automata:length $bound)) ($query (ScopedMatcherRequest $rule $spec $ambient RuleLeft LNil 0 LNil $left $source)) ($matcher (gslt:premise:matching-start $environment $query))) (Some (PremiseExpansion (LCons (DescentRootMatch $inner $bound $type $source $index $rule $spec $matcher 0 $continuation) LNil) LNil LNil))) (Some (PremiseExpansion LNil LNil (LCons (PremiseSourceRejected $index) LNil)))) (Some (PremiseExpansion LNil LNil (LCons (PremiseBindingRejected $index) LNil))))) ($badSpec None)))) ($badRule None)))) ($badLookup None)))))) ((DescentStepsGoal $depth $bound $type $source $limit) (Some (PremiseExpansion (LCons (DescentScanChildren $depth $bound $type $source $limit 0 $continuation) LNil) LNil LNil))) ($badGoal None))))) ($badEnvironment None))))

; Shared continuation after any certified root matcher backend publishes one
; answer.  Ordinary incremental matching and collection matching both enter
; here, so typing, premise replay and reduct construction have one owner.
(: gslt:descent:continue-root-answer
  (-> Atom Atom Atom Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:descent:continue-root-answer $environment $depth $bound $type $source $index $rule $spec $answer $tail $next) (case (gslt:premise:matching-environment $environment) (((PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free) (case $rule (((ScopedRewriteRuleV1 $name $types $premises $left $right $bindings) (case $answer (((ScopedMatcherAnswer $assignment $trace) (if (gslt:premise:check-assignment $declarations $free $bound $rule $spec $assignment) (Some (PremiseExpansion (LCons (DescentEvaluate (DescentPremisesGoal $depth (PremiseContext $index $rule $spec $bound 0 0) $premises $assignment) (DescentRootBody $depth $bound $type $source $index $rule $spec $trace $assignment $tail)) $next) LNil LNil)) (Some (PremiseExpansion $next LNil LNil)))) ($badAnswer None)))) ($badRule None)))) ($badEnvironment None))))

(: gslt:descent:root-match (-> Atom Atom %Undefined%))
(= (gslt:descent:root-match $environment $task) (case (gslt:premise:matching-environment $environment) (((PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free) (case $task (((DescentRootMatch $depth $bound $type $source $index $rule $spec $matcher $cursor $tail) (case $rule (((ScopedRewriteRuleV1 $name $types $premises $left $right $bindings) (case (gslt:premise:matching-answer-at $environment $matcher $cursor) (((Some (ScopedMatcherAnswer $assignment $trace)) (let* (($next (+ $cursor 1)) ($later (DescentRootMatch $depth $bound $type $source $index $rule $spec $matcher $next $tail))) (gslt:descent:continue-root-answer $environment $depth $bound $type $source $index $rule $spec (ScopedMatcherAnswer $assignment $trace) $tail (LCons $later LNil)))) (None (if (gslt:premise:matching-complete $environment $matcher) (Some (PremiseExpansion LNil LNil LNil)) (let* (($ambient (gslt:automata:length $bound)) ($request (ScopedMatcherRequest $rule $spec $ambient RuleLeft LNil 0 LNil $left $source)) ($advanced (gslt:premise:matching-tick $environment $request $matcher))) (Some (PremiseExpansion (LCons (DescentRootMatch $depth $bound $type $source $index $rule $spec $advanced $cursor $tail) LNil) LNil LNil))))) ($badAnswer None)))) ($badRule None)))) ($badTask None)))) ($badEnvironment None))))

(: gslt:descent:target-match (-> Atom Atom %Undefined%))
(= (gslt:descent:target-match $environment $task) (case (gslt:premise:matching-environment $environment) (((PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free) (case $task (((DescentTargetMatch $depth $call $index $trace $captured $completed $history $target $matcher $cursor $tail) (case $call (((PremiseStepCall $context $premise $initial $binders $type $source $target-schema) (case $context (((PremiseContext $rule-index $rule $spec $bound $premise-index $quantifiers) (case (gslt:premise:matching-answer-at $environment $matcher $cursor) (((Some (ScopedMatcherAnswer $assignment $target-trace)) (let* (($next (+ $cursor 1)) ($later (DescentTargetMatch $depth $call $index $trace $captured $completed $history $target $matcher $next $tail))) (if (gslt:premise:check-assignment $declarations $free $bound $rule $spec $assignment) (let $child-bound (gslt:automata:append $binders $bound) (Some (PremiseExpansion (LCons (DescentDeliver (PremiseResult (DescentPremiseGoal $depth $context $premise $initial) (PremiseAnswer $assignment (PremiseChildEvent $premise-index $quantifiers $index $child-bound $source $target $trace $target-trace $captured $completed $history))) $tail) (LCons $later LNil)) LNil LNil))) (Some (PremiseExpansion (LCons $later LNil) LNil LNil))))) (None (if (gslt:premise:matching-complete $environment $matcher) (Some (PremiseExpansion LNil LNil LNil)) (let* (($ambient (gslt:automata:length $bound)) ($local (gslt:automata:length $binders)) ($request (ScopedMatcherRequest $rule $spec $ambient (RulePremise $premise-index $quantifiers 1) LNil $local $initial $target-schema $target)) ($advanced (gslt:premise:matching-tick $environment $request $matcher))) (Some (PremiseExpansion (LCons (DescentTargetMatch $depth $call $index $trace $captured $completed $history $target $advanced $cursor $tail) LNil) LNil LNil))))) ($badAnswer None)))) ($badContext None)))) ($badCall None)))) ($badTask None)))) ($badEnvironment None))))

(: gslt:descent:query (-> Atom Atom %Undefined%))
(= (gslt:descent:query $environment $task)
   (case $task
     (((DescentQuery $depth $request $queryState $cursor $continuation)
       (case $request
         (((PremiseQueryRequest $context $relation $arguments $initial)
           (case $context
             (((PremiseContext $ruleIndex $rule $spec $bound $premiseIndex $quantifiers)
               (case $queryState
                 (((PremiseState $agenda $answers $unresolved $work)
                   (case (gslt:rule:row-at $cursor $answers)
                     (((Some (PremiseQueryAnswer $rowIndex $assignment $origins))
                       (let $next (+ $cursor 1)
                         (Some (PremiseExpansion
                           (LCons (DescentDeliver
                             (PremiseResult (DescentPremiseGoal $depth $context (RelationQuery $relation $arguments) $initial)
                               (PremiseAnswer $assignment (PremiseQueryEvent $premiseIndex $quantifiers $rowIndex $origins)))
                             $continuation)
                             (LCons (DescentQuery $depth $request $queryState $next $continuation) LNil))
                           LNil LNil))))
                      (None
                       (case $agenda
                         ((LNil
                           (let $reasons (gslt:premise:query-obligations $unresolved)
                             (Some (PremiseExpansion LNil LNil $reasons))))
                          ((LCons $queryTask $queryRest)
                           (let $expanded (gslt:premise:query-expand-in $environment $request $queryTask)
                             (case (gslt:premise:machine-commit $queryState $expanded)
                               (((Some $nextState)
                                 (Some (PremiseExpansion
                                   (LCons (DescentQuery $depth $request $nextState $cursor $continuation) LNil) LNil LNil)))
                                ($badCommit None)))))
                          ($badAgenda None))))
                      ($badAnswer None))))
                  ($badState None))))
              ($badContext None))))
          ($badRequest None))))
      ($badTask None))))

(: gslt:descent:expand (-> Atom Atom %Undefined%))
(= (gslt:descent:expand $environment $task)
   (case $task
     (((DescentEvaluate $goal $continuation) (gslt:descent:evaluate $environment $goal $continuation))
      ((DescentDeliver $result $continuation) (gslt:descent:deliver $environment $result $continuation))
      ((DescentQuery $depth $request $queryState $cursor $continuation) (gslt:descent:query $environment $task))
      ((DescentRootMatch $depth $bound $type $source $index $rule $spec $matcher $cursor $tail)
       (gslt:descent:root-match $environment $task))
      ((DescentTargetMatch $depth $call $index $trace $captured $completed $history $target $matcher $cursor $tail)
       (gslt:descent:target-match $environment $task))
      ((DescentScanChildren $depth $bound $type $source $limit $cursor $continuation)
       (if (< $cursor $limit)
         (let $next (+ $cursor 1)
           (Some (PremiseExpansion
             (LCons (DescentEvaluate (DescentRootGoal $depth $bound $type $source $cursor)
               (DescentSearchedRoot $depth $bound $type $source $cursor $limit $continuation))
               (LCons (DescentScanChildren $depth $bound $type $source $limit $next $continuation) LNil))
             LNil LNil)))
         (Some (PremiseExpansion LNil LNil LNil))))
      ($badTask None))))

(: gslt:descent:start (-> Atom %Undefined%))
(= (gslt:descent:start $goal)
   (PremiseState (LCons (DescentEvaluate $goal (DescentDone $goal)) LNil) LNil LNil 0))

(: gslt:descent:tick (-> Atom Atom %Undefined%))
(= (gslt:descent:tick $environment $state)
   (case $state
     (((PremiseState LNil $answers $unresolved $work) $state)
      ((PremiseState (LCons $task $rest) $answers $unresolved $work)
       (let $expanded (gslt:descent:expand $environment $task)
         (case (gslt:premise:machine-commit $state $expanded)
           (((Some $next) $next)
            ($failed $state))))))))

(: gslt:descent:run (-> Atom Atom Atom %Undefined%))
(= (gslt:descent:run $environment $fuel $state)
   (if (== $fuel 0) $state
     (let* (($next (gslt:descent:tick $environment $state))
            ($remaining (- $fuel 1)))
       (gslt:descent:run $environment $remaining $next))))

; A drained search with no depth cut holds every derivation of its goal.
(: gslt:descent:cut (-> Atom %Undefined%))
(= (gslt:descent:cut $unresolved)
   (case $unresolved
     ((LNil False)
      ((LCons (DescentDepthExhausted $index) $rest) True)
      ((LCons $other $rest) (gslt:descent:cut $rest)))))

; The answers of a state, without their goals.
(: gslt:descent:payloads (-> Atom %Undefined%))
(= (gslt:descent:payloads $results)
   (case $results
     ((LNil LNil)
      ((LCons (PremiseResult $goal $answer) $rest)
       (let $tail (gslt:descent:payloads $rest) (LCons $answer $tail))))))

(: gslt:descent:readout (-> Atom %Undefined%))
(= (gslt:descent:readout $state)
   (case $state
     (((PremiseState $agenda $answers $unresolved $work)
       (let* (($payloads (gslt:descent:payloads $answers))
              ($cut (gslt:descent:cut $unresolved)))
         (DescentReadout $payloads $cut))))))
