; Shared retained matching, allocation installation and conditional work.
(: gslt:occurrence-machine:from-lanes (-> Atom %Undefined%))
(= (gslt:occurrence-machine:from-lanes $lanes)
  (let $batch (gslt:occurrence-batch:begin LNil)
    (RecursiveOccurrenceState $lanes $batch)))

(: gslt:occurrence-machine:round (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:occurrence-machine:round $names $environment $depth $state)
  (case $state
    (((RecursiveOccurrenceState $lanes $batch)
      (case (gslt:occurrence-collector:advance-lanes $names $environment $depth $lanes)
        (((RecursiveOccurrenceLanesAllocations $next $fresh)
          (let* (($installed (gslt:occurrence-install:append $fresh $batch))
                 ($advanced (gslt:occurrence-batch:run $environment 1 $installed)))
            (RecursiveOccurrenceState $next $advanced)))))))))

(: gslt:occurrence-machine:run (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:occurrence-machine:run $names $environment $depth $work $state)
  (if (== $work 0) $state
    (let* (($next (gslt:occurrence-machine:round $names $environment $depth $state))
           ($remaining (- $work 1)))
      (gslt:occurrence-machine:run $names $environment $depth $remaining $next))))

(: gslt:occurrence-machine:publication (-> Atom %Undefined%))
(= (gslt:occurrence-machine:publication $state)
  (case $state
    (((RecursiveOccurrenceState $lanes $batch)
      (gslt:occurrence-batch:publication $batch)))))
