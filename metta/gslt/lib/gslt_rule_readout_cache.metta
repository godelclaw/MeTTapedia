; Ordered readout with one retained replacement decision. Every result keeps
; its own matching and premise history. A miss executes the original readout;
; only its target-or-refusal projection is retained for a following equal key.

(: gslt:rule:job-readout-key (-> Atom Atom %Undefined%))
(= (gslt:rule:job-readout-key $request $result)
   (case $result
     (((PremiseResult $goal (RootAnswer $trace $captured $completed $history $localTarget))
       (ReadoutKey $request $goal $localTarget))
      ($_ (ReadoutUncacheable $request $result)))))

(: gslt:rule:job-readout-target (-> Atom %Undefined%))
(= (gslt:rule:job-readout-target $readout)
   (case $readout
     (((Some (RuleJobReceipt $job $trace $captured $completed $history $localTarget $target))
       (Some $target))
      ($_ None))))

(: gslt:rule:job-readout-rebuild (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:job-readout-rebuild $request $result $endpoint)
   (case (ReadoutRebuild $request $result $endpoint)
     (((ReadoutRebuild
         (RuleJobRequestProjection $environment $permissions $bound $expected $source $job)
         (PremiseResult $goal (RootAnswer $trace $captured $completed $history $localTarget))
         (Some $target))
       (Some (RuleJobReceipt $job $trace $captured $completed $history $localTarget $target)))
      ($_ None))))

(: gslt:rule:job-readout-cache-miss (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:job-readout-cache-miss $request $result $key)
   (let $readout (gslt:rule:job-finish-root $request $result)
     (let $endpoint (gslt:rule:job-readout-target $readout)
       (ReadoutCached $readout (ReadoutCache $key $endpoint) 1))))

(: gslt:rule:job-readout-cache-step (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:job-readout-cache-step $request $result $cache)
   (let $key (gslt:rule:job-readout-key $request $result)
     (case $cache
       (((ReadoutCache $oldKey $endpoint)
         (if (== $key $oldKey)
           (let $readout (gslt:rule:job-readout-rebuild $request $result $endpoint)
             (ReadoutCached $readout $cache 0))
           (gslt:rule:job-readout-cache-miss $request $result $key)))
        ($_ (gslt:rule:job-readout-cache-miss $request $result $key))))))

(: gslt:rule:job-readouts-loop (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:job-readouts-loop $request $results $cache)
   (case $results
     ((LNil (ReadoutBatch LNil 0))
      ((LCons $result $rest)
       (let (ReadoutCached $readout $next $miss)
         (gslt:rule:job-readout-cache-step $request $result $cache)
         (let (ReadoutBatch $tail $later)
           (gslt:rule:job-readouts-loop $request $rest $next)
           (let $calls (+ $miss $later)
             (ReadoutBatch (LCons $readout $tail) $calls))))))))

(: gslt:rule:job-readouts-accounted (-> Atom Atom %Undefined%))
(= (gslt:rule:job-readouts-accounted $request $results)
   (gslt:rule:job-readouts-loop $request $results None))

(: gslt:rule:job-readouts (-> Atom Atom %Undefined%))
(= (gslt:rule:job-readouts $request $results)
   (let (ReadoutBatch $readouts $calls)
     (gslt:rule:job-readouts-accounted $request $results)
     $readouts))
