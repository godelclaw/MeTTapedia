; Retain each typed occurrence and recursive allocation beside its continuation.
(: gslt:occurrence-batch:frame-begin
  (-> Atom Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:occurrence-batch:frame-begin
     $origin $environment $depth $bound $type $index $rule $spec $prepared)
  (let $continued (gslt:collection-continuation:begin
        $environment $depth $bound $type $index $rule $spec $prepared)
    (RecursiveOccurrenceFrame $origin $continued)))

(: gslt:occurrence-batch:frame-run (-> Atom Atom Atom %Undefined%))
(= (gslt:occurrence-batch:frame-run $environment $work $frame)
  (case $frame
    (((RecursiveOccurrenceFrame $origin $continued)
      (let $next (gslt:collection-continuation:run $environment $work $continued)
        (RecursiveOccurrenceFrame $origin $next))))))

(: gslt:occurrence-batch:tag (-> Atom Atom %Undefined%))
(= (gslt:occurrence-batch:tag $origin $packets)
  (case $packets
    ((LNil LNil)
     ((LCons $packet $rest)
      (let $later (gslt:occurrence-batch:tag $origin $rest)
        (LCons (RecursiveOccurrencePublication $origin $packet) $later))))))

(: gslt:occurrence-batch:frame-publication (-> Atom %Undefined%))
(= (gslt:occurrence-batch:frame-publication $frame)
  (case $frame
    (((RecursiveOccurrenceFrame $origin $continued)
      (let $packets (gslt:collection-continuation:publication $continued)
        (gslt:occurrence-batch:tag $origin $packets))))))

; Every allocation drains its own suffix, even when another finishes first.
(: gslt:occurrence-batch:advance-frames (-> Atom Atom %Undefined%))
(= (gslt:occurrence-batch:advance-frames $environment $frames)
  (case $frames
    ((LNil (RecursiveOccurrenceAdvanced LNil LNil))
     ((LCons $frame $rest)
      (let* (($previous (gslt:occurrence-batch:frame-publication $frame))
             ($consumed (gslt:automata:length $previous))
             ($next (gslt:occurrence-batch:frame-run $environment 1 $frame))
             ($published (gslt:occurrence-batch:frame-publication $next))
             ($fresh (gslt:complete:drop $consumed $published))
             ($later (gslt:occurrence-batch:advance-frames $environment $rest)))
        (case $later
          (((RecursiveOccurrenceAdvanced $next-rest $more)
            (let $all (gslt:automata:append $fresh $more)
              (RecursiveOccurrenceAdvanced (LCons $next $next-rest) $all))))))))))

; Inputs to begin are the newly prepared, unpublished allocation frames.
(: gslt:occurrence-batch:begin (-> Atom %Undefined%))
(= (gslt:occurrence-batch:begin $frames)
  (RecursiveOccurrenceBatch $frames LNil))

(: gslt:occurrence-batch:resume (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:occurrence-batch:resume $environment $work $frames $log)
  (if (== $work 0)
    (RecursiveOccurrenceBatch $frames $log)
    (let $advanced (gslt:occurrence-batch:advance-frames $environment $frames)
      (case $advanced
        (((RecursiveOccurrenceAdvanced $next $fresh)
          (let* (($next-log (gslt:automata:append $log $fresh))
                 ($remaining (- $work 1)))
            (gslt:occurrence-batch:resume $environment $remaining $next $next-log))))))))

(: gslt:occurrence-batch:run (-> Atom Atom Atom %Undefined%))
(= (gslt:occurrence-batch:run $environment $work $state)
  (case $state
    (((RecursiveOccurrenceBatch $frames $log)
      (gslt:occurrence-batch:resume $environment $work $frames $log)))))

(: gslt:occurrence-batch:publication (-> Atom %Undefined%))
(= (gslt:occurrence-batch:publication $state)
  (case $state
    (((RecursiveOccurrenceBatch $frames $log) $log))))
