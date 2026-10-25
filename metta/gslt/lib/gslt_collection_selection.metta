; Collection allocation preserves physical bag origins and explicit set retention.
(: gslt:collection:choices-from (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:collection:choices-from $idempotent $original $items $index)
  (case $items
    ((LNil LNil)
     ((LCons $value $tail)
      (let* (($residual (gslt:rule:scope-match-erase-at $index $original))
             ($next (+ $index 1))
             ($later (gslt:collection:choices-from $idempotent $original $tail $next)))
        (if (== $idempotent 1)
          (LCons (CollectionChoice $index $value $residual 0)
            (LCons (CollectionChoice $index $value $original 1) $later))
          (LCons (CollectionChoice $index $value $residual 0) $later)))))))

(: gslt:collection:choices (-> Atom Atom %Undefined%))
(= (gslt:collection:choices $idempotent $items)
  (gslt:collection:choices-from $idempotent $items $items 0))

(: gslt:collection:prepend (-> Atom Atom %Undefined%))
(= (gslt:collection:prepend $choice $allocations)
  (case $choice
    (((CollectionChoice $index $value $unused $retained)
      (case $allocations
        ((LNil LNil)
         ((LCons (CollectionAllocation $values $residual $decisions) $tail)
          (let $later (gslt:collection:prepend $choice $tail)
            (LCons
              (CollectionAllocation (LCons $value $values) $residual
                (LCons (CollectionDecision $index $retained) $decisions))
              $later)))))))))

(: gslt:collection:allocate-choices (-> Atom Atom Atom %Undefined%))
(= (gslt:collection:allocate-choices $idempotent $remaining $choices)
  (case $choices
    ((LNil LNil)
     ((LCons (CollectionChoice $index $value $residual $retained) $tail)
      (let* (($children (gslt:collection:allocate $idempotent $remaining $residual))
             ($first (gslt:collection:prepend
               (CollectionChoice $index $value $residual $retained) $children))
             ($later (gslt:collection:allocate-choices $idempotent $remaining $tail)))
        (gslt:automata:append $first $later))))))

(: gslt:collection:allocate (-> Atom Atom Atom %Undefined%))
(= (gslt:collection:allocate $idempotent $count $items)
  (if (== $count 0)
    (LCons (CollectionAllocation LNil $items LNil) LNil)
    (let* (($remaining (- $count 1))
           ($choices (gslt:collection:choices $idempotent $items)))
      (gslt:collection:allocate-choices $idempotent $remaining $choices))))

(: gslt:collection:replay (-> Atom Atom Atom %Undefined%))
(= (gslt:collection:replay $idempotent $items $decisions)
  (case $decisions
    ((LNil (Some (CollectionPair LNil $items)))
     ((LCons (CollectionDecision $index $retained) $tail)
      (case (gslt:rule:row-at $index $items)
        ((None None)
         ((Some $value)
          (if (if (== $retained 1) (if (== $idempotent 1) False True) False)
            None
            (let $residual (if (== $retained 1) $items
              (gslt:rule:scope-match-erase-at $index $items))
              (case (gslt:collection:replay $idempotent $residual $tail)
                ((None None)
                 ((Some (CollectionPair $values $final))
                  (Some (CollectionPair (LCons $value $values) $final))))))))))))))
