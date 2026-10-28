; Construct requests from allocations whose residual records have already
; been ordered by the caller's selected normalizer.

(: gslt:collection-presentation:view-allocation-child
  (-> Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:collection-presentation:view-allocation-child
     $category $schema-bound $path $focus $schemas $rest $next $allocation)
  (let $typing (gslt:collection-presentation:view-scan-focus $category $focus)
    (case $typing
      (((ViewFocusTyping $bound $expected)
        (case $allocation
          (((GroupingAllocation $groups $residual)
            (let $children
              (LCons
                (ViewRequest ViewChildrenKind
                  (ViewGroups $schema-bound $path $bound 0 $schemas $groups)
                  (ViewCollection
                    (ViewFrame $path $schema-bound $focus None
                      (Some (GroupingAllocation $groups $residual)))
                    $residual $next))
                LNil)
              (case $rest
                ((RNone (case $residual
                  ((LNil $children)
                   ((LCons $first $later) LNil))))
                 ((RSome $name) $children))))))))))))

(: gslt:collection-presentation:view-allocation-children
  (-> Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:collection-presentation:view-allocation-children
     $category $schema-bound $path $focus $schemas $rest $next $allocations)
  (case $allocations
    ((LNil LNil)
     ((LCons $first $later)
       (let* (($children (gslt:collection-presentation:view-allocation-child
                        $category $schema-bound $path $focus $schemas $rest $next $first))
              ($following (gslt:collection-presentation:view-allocation-children
                          $category $schema-bound $path $focus $schemas $rest $next $later)))
         (gslt:automata:append $children $following))))))
