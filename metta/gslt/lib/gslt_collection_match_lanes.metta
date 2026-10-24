; A licensed source job owns a retained recursive matcher and its work count.
(: gslt:occurrence-matcher:begin (-> Atom Atom %Undefined%))
(= (gslt:occurrence-matcher:begin $origin $query)
  (let $state (gslt:recursive-collection:start $query)
    (RecursiveOccurrenceLane $origin $query $state 0)))

(: gslt:occurrence-matcher:resume (-> Atom Atom Atom %Undefined%))
(= (gslt:occurrence-matcher:resume $names $work $lane)
  (case $lane
    (((RecursiveOccurrenceLane $origin $query $state $spent)
      (let* (($next (gslt:recursive-collection:run $names $query $work $state))
             ($total (+ $spent $work)))
        (RecursiveOccurrenceLane $origin $query $next $total))))))

; Only the new chronological suffix is offered to allocation preparation.
(: gslt:occurrence-matcher:advance (-> Atom Atom %Undefined%))
(= (gslt:occurrence-matcher:advance $names $lane)
  (case $lane
    (((RecursiveOccurrenceLane $origin $query
        (RecursiveCollectionState $pending $answers) $spent)
      (let* (($consumed (gslt:automata:length $answers))
             ($next (gslt:occurrence-matcher:resume $names 1 $lane)))
        (case $next
          (((RecursiveOccurrenceLane $next-origin $next-query
              (RecursiveCollectionState $next-pending $next-answers) $next-spent)
            (let $fresh (gslt:complete:drop $consumed $next-answers)
              (RecursiveOccurrenceMatches $next $fresh))))))))))
