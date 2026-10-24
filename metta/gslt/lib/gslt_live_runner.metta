; Whole runs of an admitted plan through the program driver.
; Load after gslt_scoped_execution, gslt_typed_sites, gslt_execution_driver,
; gslt_rule_readout_cache, gslt_program_driver and gslt_program_resumption.
;
; A plan is
;   (LivePlan (PremiseEnvironment declarations rewrites specifications provider
;     reflection table) names permissions bound expected rules),
; where table lists the entries of the free context and names lists the free
; names of the provider rows. Each state gets its own environment: the table
; entries of the state's free names, then of the provider's, in that order.
;
; A LiveRunning machine keeps the whole program observation of its state.
; A tick gives every job the quantum as extra work and resumes it; no search is
; restarted. When the publication releases a receipt, the first released
; receipt is committed whole and a new search begins at its target. Publication
; grows by prefix under more work, so that first receipt does not change. This
; follows one path, the one publication order selects.
; LiveDone: the publication is complete and empty, so the state has no step.
; LiveBlocked: a drained job left obligations unresolved.
; A pending publication keeps the machine running; it is a checkpoint.
; States and receipts are kept newest first; gslt:live:trace lists them in order.

(: gslt:live:append (-> Atom Atom %Undefined%))
(= (gslt:live:append $left $right)
   (case $left
     ((LNil $right)
      ((LCons $first $rest)
       (let $tail (gslt:live:append $rest $right) (LCons $first $tail))))))

(: gslt:live:rest-names (-> Atom %Undefined%))
(= (gslt:live:rest-names $rest)
   (case $rest
     ((RNone LNil)
      ((RSome $name) (LCons $name LNil)))))

(: gslt:live:free-names (-> Atom %Undefined%))
(= (gslt:live:free-names $pattern)
   (case $pattern
     (((Var $index) LNil)
      ((FVar $name) (LCons $name LNil))
      ((PApp $label $arguments) (gslt:live:free-names-list $arguments))
      ((PLam $binder $body) (gslt:live:free-names $body))
      ((PMultiLam $arity $binders $body) (gslt:live:free-names $body))
      ((PSubst $body $replacement)
       (let $left (gslt:live:free-names $body)
         (let $right (gslt:live:free-names $replacement)
           (gslt:live:append $left $right))))
      ((PCollection $kind $elements $rest)
       (let $inner (gslt:live:free-names-list $elements)
         (let $tail (gslt:live:rest-names $rest)
           (gslt:live:append $inner $tail)))))))

(: gslt:live:free-names-list (-> Atom %Undefined%))
(= (gslt:live:free-names-list $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $pattern $rest)
       (let $head (gslt:live:free-names $pattern)
         (let $tail (gslt:live:free-names-list $rest)
           (gslt:live:append $head $tail)))))))

(: gslt:live:lookup (-> Atom Atom %Undefined%))
(= (gslt:live:lookup $name $table)
   (case $table
     ((LNil None)
      ((LCons (Binding $key $type) $rest)
       (if (== $key $name) (Some $type) (gslt:live:lookup $name $rest))))))

(: gslt:live:entries-on (-> Atom Atom %Undefined%))
(= (gslt:live:entries-on $table $names)
   (case $names
     ((LNil LNil)
      ((LCons $name $rest)
       (let $tail (gslt:live:entries-on $table $rest)
         (let $found (gslt:live:lookup $name $table)
           (case $found
             ((None $tail)
              ((Some $type) (LCons (Binding $name $type) $tail))))))))))

(: gslt:live:execute (-> Atom Atom Atom %Undefined%))
(= (gslt:live:execute $plan $source $budget)
   (case $plan
     (((LivePlan
         (PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $table)
         $names $permissions $bound $expected $rules)
       (let $own (gslt:live:free-names $source)
         (let $footprint (gslt:live:append $own $names)
           (let $free (gslt:live:entries-on $table $footprint)
             (gslt:program:execute
               (PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free)
               $permissions $bound $expected $source $rules $budget))))))))

(: gslt:live:begin (-> Atom Atom %Undefined%))
(= (gslt:live:begin $plan $source)
   (let $observation (gslt:live:execute $plan $source 0)
     (LiveRunning $plan $source $observation (LCons $source LNil) LNil)))

(: gslt:live:tick (-> Atom Atom %Undefined%))
(= (gslt:live:tick $machine $quantum)
   (case $machine
     (((LiveRunning $plan $source $observation $states $receipts)
       (let $resumed (gslt:program:resume $observation $quantum)
         (let $published (gslt:program:publication $resumed)
           (case $published
             (((ProgramPublication
                 (LCons (RuleJobReceipt $job $trace $captured $completed $history $local $target) $others)
                 $status)
               (let $next (gslt:live:execute $plan $target 0)
                 (LiveRunning $plan $target $next (LCons $target $states)
                   (LCons (RuleJobReceipt $job $trace $captured $completed $history $local $target)
                     $receipts))))
              ((ProgramPublication LNil ProgramPublicationComplete)
               (LiveDone $plan $source $resumed $states $receipts))
              ((ProgramPublication LNil ProgramPublicationBlocked)
               (LiveBlocked $plan $source $resumed $states $receipts))
              ((ProgramPublication LNil ProgramPublicationPending)
               (LiveRunning $plan $source $resumed $states $receipts)))))))
      ($finished $finished))))

(: gslt:live:advance (-> Atom Atom Atom %Undefined%))
(= (gslt:live:advance $machine $ticks $quantum)
   (if (== $ticks 0) $machine
     (let $next (gslt:live:tick $machine $quantum)
       (let $remaining (- $ticks 1)
         (gslt:live:advance $next $remaining $quantum)))))

(: gslt:live:reverse-onto (-> Atom Atom %Undefined%))
(= (gslt:live:reverse-onto $items $tail)
   (case $items
     ((LNil $tail)
      ((LCons $first $rest)
       (let $longer (LCons $first $tail) (gslt:live:reverse-onto $rest $longer))))))

(: gslt:live:trace (-> Atom %Undefined%))
(= (gslt:live:trace $machine)
   (case $machine
     (((LiveRunning $plan $source $observation $states $receipts)
       (let $ordered (gslt:live:reverse-onto $states LNil)
         (let $committed (gslt:live:reverse-onto $receipts LNil)
           (LiveTrace LivePending $ordered $committed))))
      ((LiveDone $plan $source $observation $states $receipts)
       (let $ordered (gslt:live:reverse-onto $states LNil)
         (let $committed (gslt:live:reverse-onto $receipts LNil)
           (LiveTrace LiveNormal $ordered $committed))))
      ((LiveBlocked $plan $source $observation $states $receipts)
       (let $ordered (gslt:live:reverse-onto $states LNil)
         (let $committed (gslt:live:reverse-onto $receipts LNil)
           (LiveTrace LiveUnresolved $ordered $committed)))))))
