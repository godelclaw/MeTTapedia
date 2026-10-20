; Length observation of captured arrays, retaining the original ordered result.
(: native:append:markers (-> Atom %Undefined%))
(= (native:append:markers $count)
  (if (== $count 0) LNil
    (let* (($remaining (- $count 1))
           ($tail (native:append:markers $remaining)))
      (LCons (PApp "Element" LNil) $tail))))

(: native:append:observe (-> Atom %Undefined%))
(= (native:append:observe $values)
  (let $count (gslt:inductive:length $values)
    (native:append:markers $count)))

(: native:append:begin (-> Atom Atom Atom %Undefined%))
(= (native:append:begin $formula $left $right)
  (let* (($values (gslt:inductive:append $left $right))
         ($bag (native:append:observe $values))
         ($cursor (native:spatial:start $formula $bag 0)))
    (NativeAppendSession $values $bag $cursor)))

(: native:append:resume (-> Atom Atom %Undefined%))
(= (native:append:resume $work $packet)
  (case $packet
    (((NativeAppendSession $values $bag $cursor)
      (let $next (native:spatial:resume $work $cursor)
        (NativeAppendSession $values $bag $next))))))

(: native:append:read (-> Atom %Undefined%))
(= (native:append:read $packet)
  (case $packet
    (((NativeAppendSession $values $bag $cursor)
      (let $answer (native:spatial:read $cursor)
        (NativeAppendObservation $values $bag $cursor $answer))))))

(: native:append:rounds (-> Atom Atom %Undefined%))
(= (native:append:rounds $rounds $packet)
  (case $rounds
    ((LNil $packet)
     ((LCons $work $rest)
      (let $next (native:append:resume $work $packet)
        (native:append:rounds $rest $next))))))

(: native:append:check (-> Atom Atom Atom Atom %Undefined%))
(= (native:append:check $formula $left $right $rounds)
  (let* (($initial (native:append:begin $formula $left $right))
         ($finished (native:append:rounds $rounds $initial)))
    (native:append:read $finished)))
