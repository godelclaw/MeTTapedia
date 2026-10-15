; Ordered execution of scoped rule jobs with explicit per-job work budgets.
; Every observation retains the complete inner state, including pending work.

(: gslt:program:receipts (-> Atom %Undefined%))
(= (gslt:program:receipts $readouts)
   (case $readouts
     ((LNil LNil)
      ((LCons (Some $receipt) $rest)
       (let $tail (gslt:program:receipts $rest)
         (LCons $receipt $tail)))
      ((LCons None $rest) (gslt:program:receipts $rest)))))

(: gslt:program:job (-> Atom Atom %Undefined%))
(= (gslt:program:job $request $budget)
   (case $request
     (((RuleJobRequestProjection $environment $permissions $bound $expected $source
         (RuleJob $ordinal $declaration
           (RuleJobSite $address $context $focus $focusBound $focusType $frames)))
       (let (Some $initial)
         (gslt:premise:machine-start (RootGoal $focusBound $focusType $focus $ordinal))
         (let (Some (PremiseState $agenda $answers $unresolved $work))
           (gslt:premise:machine-run $environment $budget $initial)
           (let $readouts (gslt:rule:job-readouts $request $answers)
             (let $receipts (gslt:program:receipts $readouts)
               (ProgramJobObservation $request
                 (PremiseState $agenda $answers $unresolved $work) $receipts)))))))))

(: gslt:program:run (-> Atom %Undefined%))
(= (gslt:program:run $jobs)
   (case $jobs
     ((LNil (ProgramObservation LNil LNil))
      ((LCons (ProgramJob $request $budget) $rest)
       (let (ProgramJobObservation $jobRequest $state $receipts)
         (gslt:program:job $request $budget)
         (let (ProgramObservation $observations $later)
           (gslt:program:run $rest)
           (let $all (gslt:automata:append $receipts $later)
             (ProgramObservation
               (LCons (ProgramJobObservation $jobRequest $state $receipts) $observations)
               $all))))))))

(: gslt:program:requests (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:program:requests $environment $permissions $bound $expected $source $budget $jobs)
   (case $jobs
     ((LNil LNil)
      ((LCons $job $rest)
       (let $tail
         (gslt:program:requests $environment $permissions $bound $expected $source $budget $rest)
         (LCons
           (ProgramJob
             (RuleJobRequestProjection $environment $permissions $bound $expected $source $job)
             $budget)
           $tail))))))

(: gslt:program:execute (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:program:execute $environment $permissions $bound $expected $source $rules $budget)
   (case $environment
     (((PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free)
       (let $jobs
         (gslt:sites:jobs $declarations $free $permissions $bound $expected $source $rules)
         (let $requests
           (gslt:program:requests $environment $permissions $bound $expected $source $budget $jobs)
           (gslt:program:run $requests)))))))
