(: gslt:collection-presentation:view-allocation-advance (-> Atom %Undefined%))
(= (gslt:collection-presentation:view-allocation-advance $task)
  (case $task
    (((ViewAllocations $schema-bound $path $focus $schemas $rest $cursor $published $next)
      (let* (($advanced (gslt:collection-presentation:group-tick $cursor))
             ($answers (gslt:collection-presentation:group-answers $advanced))
             ($fresh (gslt:complete:drop $published $answers))
             ($next-published (gslt:automata:length $answers))
             ($finished (gslt:collection-presentation:group-complete $advanced)))
        (if $finished
          (ViewAllocationProgress $advanced $fresh $next-published LNil)
          (ViewAllocationProgress $advanced $fresh $next-published
            (LCons (ViewAllocations $schema-bound $path $focus $schemas $rest
              $advanced $next-published $next) LNil))))))))
