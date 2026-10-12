; Resumable scoped rule jobs. Every cursor selects a physical result occurrence.

(: gslt:driver:job-obligations (-> Atom %Undefined%))
(= (gslt:driver:job-obligations $obligations)
   (case $obligations
     ((LNil LNil)
      ((LCons $reason $rest)
       (let $tail (gslt:driver:job-obligations $rest)
         (LCons (RuleJobPremise $reason) $tail))))))

(: gslt:driver:job-start (-> Atom %Undefined%))
(= (gslt:driver:job-start $request)
   (case $request
     (((RuleJobRequestProjection $environment $permissions $bound $expected $source
         (RuleJob $ordinal $declaration
           (RuleJobSite $address $context $focus $focusBound $focusType $frames)))
       (case (gslt:premise:machine-start (RootGoal $focusBound $focusType $focus $ordinal))
         (((Some $inner)
           (Some (PremiseState (LCons (RuleJobFrame $inner 0) LNil) LNil LNil 0)))
          ($_ None))))
      ($_ None))))

(: gslt:driver:job-expand (-> Atom Atom %Undefined%))
(= (gslt:driver:job-expand $request $task)
   (case (RuleJobExpansionInput $request $task)
     (((RuleJobExpansionInput
         (RuleJobRequestProjection $environment $permissions $bound $expected $source $job)
         (RuleJobFrame (PremiseState $agenda $answers $unresolved $work) $cursor))
       (case (gslt:rule:row-at $cursor $answers)
         (((Some $result)
           (let $next (+ $cursor 1)
             (let $tail (LCons (RuleJobFrame (PremiseState $agenda $answers $unresolved $work) $next) LNil)
               (case (gslt:rule:job-finish-root $request $result)
                 (((Some $receipt) (Some (PremiseExpansion $tail (LCons $receipt LNil) LNil)))
                  (None (Some (PremiseExpansion $tail LNil LNil))))))))
          (None
           (case $agenda
             ((LNil
               (let $pending (gslt:driver:job-obligations $unresolved)
                 (Some (PremiseExpansion LNil LNil $pending))))
              ((LCons $current $remaining)
               (case (gslt:premise:machine-tick $environment
                       (PremiseState $agenda $answers $unresolved $work))
                 (((Some $advanced)
                   (Some (PremiseExpansion (LCons (RuleJobFrame $advanced $cursor) LNil) LNil LNil)))
                  ($_ None))))))))))
      ($_ None))))

(: gslt:driver:job-tick (-> Atom Atom %Undefined%))
(= (gslt:driver:job-tick $request $state)
   (case $state
     (((PremiseState LNil $answers $unresolved $work) (Some $state))
      ((PremiseState (LCons $task $rest) $answers $unresolved $work)
       (let $expanded (gslt:driver:job-expand $request $task)
         (gslt:premise:machine-commit $state $expanded)))
      ($_ None))))

(: gslt:driver:job-run (-> Atom Atom Atom %Undefined%))
(= (gslt:driver:job-run $request $fuel $state)
   (if (== $fuel 0)
     (Some $state)
     (case (gslt:driver:job-tick $request $state)
       (((Some $next)
         (let $remaining (- $fuel 1)
           (gslt:driver:job-run $request $remaining $next)))
        ($_ None)))))

(: gslt:driver:job-begin (-> Atom Atom %Undefined%))
(= (gslt:driver:job-begin $request $fuel)
   (case (gslt:driver:job-start $request)
     (((Some $state) (gslt:driver:job-run $request $fuel $state))
      ($_ None))))
