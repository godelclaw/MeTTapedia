; Optional relative-control realization of the retained subterm matcher.
; Load gslt_match_automata.metta first. Controls use its Observe/MKey wire;
; ordered instances retain their complete relative At announcement and offset.
; The derivative counter counts cache entries, excluding normalization/lookup.

(: gslt:normalized:strip-prefix (-> Atom Atom %Undefined%))
(= (gslt:normalized:strip-prefix $base $path)
   (case ($base $path)
     (((LNil $whole) (Some $whole))
      (((LCons $first $base-rest) (LCons $actual $path-rest))
       (if (== $first $actual)
         (gslt:normalized:strip-prefix $base-rest $path-rest) None))
      ($bad None))))

(: gslt:normalized:at (-> Atom Number %Undefined%))
(= (gslt:normalized:at $values $index)
   (case $values
     ((LNil None)
      ((LCons $first $rest)
       (if (== $index 0) (Some $first)
         (gslt:normalized:at $rest (- $index 1)))))))

(: gslt:normalized:activation (-> Atom %Undefined%))
(= (gslt:normalized:activation (MInstance $offset $announcement $control))
   (MActivation $control $offset))

(: gslt:normalized:activations (-> Atom %Undefined%))
(= (gslt:normalized:activations $instances)
   (case $instances
     ((LNil LNil)
      ((LCons $first $rest)
       (let* (($activation (gslt:normalized:activation $first))
              ($tail (gslt:normalized:activations $rest)))
         (LCons $activation $tail))))))

(: gslt:normalized:relative (-> Atom Atom Atom %Undefined%))
(= (gslt:normalized:relative $offset (Observe $position $key) $pending)
   (case (gslt:normalized:strip-prefix $offset $position)
     ((None (Some $pending))
      ((Some $relative)
       (gslt:automata:derive (Observe $relative $key) $pending)))))

(: gslt:normalized:cache (-> Atom Atom Atom %Undefined%))
(= (gslt:normalized:cache $controls $observation $activations)
   (case $activations
     ((LNil LNil)
      ((LCons (MActivation $index $offset) $rest)
       (let $tail (gslt:normalized:cache $controls $observation $rest)
         (case (gslt:normalized:at $controls $index)
           ((None (LCons (MCache (MActivation $index $offset) None) $tail))
            ((Some $pending)
             (let $derivative (gslt:normalized:relative $offset $observation $pending)
               (LCons (MCache (MActivation $index $offset) $derivative) $tail))))))))))

(: gslt:normalized:lookup (-> Atom Atom %Undefined%))
(= (gslt:normalized:lookup $activation $cache)
   (case $cache
     ((LNil None)
      ((LCons (MCache $key $value) $rest)
       (if (== $activation $key) $value
         (gslt:normalized:lookup $activation $rest))))))

(: gslt:normalized:restore (-> Atom Atom %Undefined%))
(= (gslt:normalized:restore (MInstance $offset (At $relative $occurrence) $index) $pending)
   (let* (($position (gslt:automata:append $offset $relative))
          ($absolute (gslt:automata:shift $offset $pending)))
     (MGoal (At $position $occurrence) $absolute)))

(: gslt:normalized:dispatch (-> Atom Atom %Undefined%))
(= (gslt:normalized:dispatch $instances $cache)
   (case $instances
     ((LNil LNil)
      ((LCons $first $rest)
       (let* (($tail (gslt:normalized:dispatch $rest $cache))
              ($activation (gslt:normalized:activation $first)))
         (case (gslt:normalized:lookup $activation $cache)
           ((None $tail)
            ((Some $pending)
             (let $restored (gslt:normalized:restore $first $pending)
               (LCons $restored $tail))))))))))

(: gslt:normalized:derive (-> Atom Atom %Undefined%))
(= (gslt:normalized:derive (MNormal $controls $instances) $observation)
   (let* (($raw (gslt:normalized:activations $instances))
          ($activations (gslt:automata:unique $raw))
          ($cache (gslt:normalized:cache $controls $observation $activations))
          ($goals (gslt:normalized:dispatch $instances $cache))
          ($count (gslt:automata:length $cache)))
     (MFinished $goals $count)))

; Transitive overlap components depend on inspection positions, not keys.
(: gslt:normalized:position-member (-> Atom Atom %Undefined%))
(= (gslt:normalized:position-member $position $pending)
   (case $pending
     ((LNil False)
      ((LCons (Observe $other $key) $rest)
       (if (== $position $other) True
         (gslt:normalized:position-member $position $rest))))))

(: gslt:normalized:overlap-pending (-> Atom Atom %Undefined%))
(= (gslt:normalized:overlap-pending $left $right)
   (case $left
     ((LNil False)
      ((LCons (Observe $position $key) $rest)
       (if (gslt:normalized:position-member $position $right) True
         (gslt:normalized:overlap-pending $rest $right))))))

(: gslt:normalized:overlaps (-> Atom Atom %Undefined%))
(= (gslt:normalized:overlaps (MGoal $first $left) (MGoal $second $right))
   (gslt:normalized:overlap-pending $left $right))

(: gslt:normalized:touches (-> Atom Atom %Undefined%))
(= (gslt:normalized:touches $goal $component)
   (case $component
     ((LNil False)
      ((LCons $first $rest)
       (if (gslt:normalized:overlaps $goal $first) True
         (gslt:normalized:touches $goal $rest))))))

(: gslt:normalized:partition (-> Atom Atom %Undefined%))
(= (gslt:normalized:partition $goal $components)
   (case $components
     ((LNil (MPartition LNil LNil))
      ((LCons $first $rest)
       (case (gslt:normalized:partition $goal $rest)
         (((MPartition $joined $independent)
           (if (gslt:normalized:touches $goal $first)
             (let $all (gslt:automata:append $first $joined)
               (MPartition $all $independent))
             (MPartition $joined (LCons $first $independent))))))))))

(: gslt:normalized:components (-> Atom %Undefined%))
(= (gslt:normalized:components $goals)
   (case $goals
     ((LNil LNil)
      ((LCons $first $rest)
       (let $previous (gslt:normalized:components $rest)
         (case (gslt:normalized:partition $first $previous)
           (((MPartition $joined $independent)
             (LCons (LCons $first $joined) $independent)))))))))

(: gslt:normalized:component-for (-> Atom Atom %Undefined%))
(= (gslt:normalized:component-for $components $goal)
   (case $components
     ((LNil (LCons $goal LNil))
      ((LCons $first $rest)
       (if (gslt:automata:member $goal $first) $first
         (gslt:normalized:component-for $rest $goal))))))

; Component announcements remain present even when their obligations empty.
(: gslt:normalized:pending-positions (-> Atom %Undefined%))
(= (gslt:normalized:pending-positions $pending)
   (case $pending
     ((LNil LNil)
      ((LCons (Observe $position $key) $rest)
       (let $tail (gslt:normalized:pending-positions $rest)
         (LCons $position $tail))))))

(: gslt:normalized:positions (-> Atom %Undefined%))
(= (gslt:normalized:positions $component)
   (case $component
     ((LNil LNil)
      ((LCons (MGoal (At $position $occurrence) $pending) $rest)
       (let* (($here (gslt:normalized:pending-positions $pending))
              ($below (gslt:normalized:positions $rest))
              ($all (gslt:automata:append $here $below)))
         (LCons $position $all))))))

(: gslt:normalized:common-prefix (-> Atom Atom %Undefined%))
(= (gslt:normalized:common-prefix $left $right)
   (case ($left $right)
     ((((LCons $first $left-rest) (LCons $actual $right-rest))
       (if (== $first $actual)
         (let $tail (gslt:normalized:common-prefix $left-rest $right-rest)
           (LCons $first $tail)) LNil))
      ($bad LNil))))

(: gslt:normalized:gcp (-> Atom %Undefined%))
(= (gslt:normalized:gcp $positions)
   (case $positions
     ((LNil LNil)
      ((LCons $first LNil) $first)
      ((LCons $first $rest)
       (let $tail (gslt:normalized:gcp $rest)
         (gslt:normalized:common-prefix $first $tail))))))

(: gslt:normalized:base (-> Atom %Undefined%))
(= (gslt:normalized:base $component)
   (let $positions (gslt:normalized:positions $component)
     (gslt:normalized:gcp $positions)))

; Drop one child index for each index of the displacement. This operation is
; total; componentBase proves the relevant paths also have that prefix.
(: gslt:normalized:drop-displacement (-> Atom Atom %Undefined%))
(= (gslt:normalized:drop-displacement $base $path)
   (case ($base $path)
     (((LNil $whole) $whole)
      (((LCons $ignored-base $base-rest) (LCons $ignored-path $path-rest))
       (gslt:normalized:drop-displacement $base-rest $path-rest))
      ($bad LNil))))

(: gslt:normalized:relative-pending (-> Atom Atom %Undefined%))
(= (gslt:normalized:relative-pending $base $pending)
   (case $pending
     ((LNil LNil)
      ((LCons (Observe $position $key) $rest)
       (let* (($relative (gslt:normalized:drop-displacement $base $position))
              ($tail (gslt:normalized:relative-pending $base $rest)))
         (LCons (Observe $relative $key) $tail))))))

(: gslt:normalized:rebase (-> Atom Atom %Undefined%))
(= (gslt:normalized:rebase $base (MGoal (At $position $occurrence) $pending))
   (let* (($relative (gslt:normalized:drop-displacement $base $position))
          ($residual (gslt:normalized:relative-pending $base $pending)))
     (MGoal (At $relative $occurrence) $residual)))

(: gslt:normalized:factors (-> Atom Atom %Undefined%))
(= (gslt:normalized:factors $components $goals)
   (case $goals
     ((LNil LNil)
      ((LCons $first $rest)
       (let* (($component (gslt:normalized:component-for $components $first))
              ($base (gslt:normalized:base $component))
              ($relative (gslt:normalized:rebase $base $first))
              ($tail (gslt:normalized:factors $components $rest)))
         (LCons (MFactor $base $relative) $tail))))))

(: gslt:normalized:controls (-> Atom %Undefined%))
(= (gslt:normalized:controls $factors)
   (case $factors
     ((LNil LNil)
      ((LCons (MFactor $base (MGoal $announcement $pending)) $rest)
       (let $tail (gslt:normalized:controls $rest) (LCons $pending $tail))))))

(: gslt:normalized:index (-> Atom Atom %Undefined%))
(= (gslt:normalized:index $value $values)
   (case $values
     ((LNil 0)
      ((LCons $first $rest)
       (if (== $value $first) 0
         (let $tail (gslt:normalized:index $value $rest) (+ 1 $tail)))))))

(: gslt:normalized:instances (-> Atom Atom %Undefined%))
(= (gslt:normalized:instances $factors $controls)
   (case $factors
     ((LNil LNil)
      ((LCons (MFactor $base (MGoal $announcement $pending)) $rest)
       (let* (($index (gslt:normalized:index $pending $controls))
              ($tail (gslt:normalized:instances $rest $controls)))
         (LCons (MInstance $base $announcement $index) $tail))))))

(: gslt:normalized:normalize (-> Atom %Undefined%))
(= (gslt:normalized:normalize $goals)
   (let* (($components (gslt:normalized:components $goals))
          ($factors (gslt:normalized:factors $components $goals))
          ($all (gslt:normalized:controls $factors))
          ($controls (gslt:automata:unique $all))
          ($instances (gslt:normalized:instances $factors $controls)))
     (MNormal $controls $instances)))

(: gslt:normalized:expand-instances (-> Atom Atom %Undefined%))
(= (gslt:normalized:expand-instances $controls $instances)
   (case $instances
     ((LNil LNil)
      ((LCons (MInstance $offset $announcement $index) $rest)
       (let $tail (gslt:normalized:expand-instances $controls $rest)
         (case (gslt:normalized:at $controls $index)
           ((None $tail)
            ((Some $pending)
             (let $goal (gslt:normalized:restore (MInstance $offset $announcement $index) $pending)
               (LCons $goal $tail))))))))))

(: gslt:normalized:expand (-> Atom %Undefined%))
(= (gslt:normalized:expand (MNormal $controls $instances))
   (gslt:normalized:expand-instances $controls $instances))

(: gslt:normalized:execute (-> Atom Atom %Undefined%))
(= (gslt:normalized:execute $observations $normal)
   (case $observations
     ((LNil (MExecuted $normal 0))
      ((LCons $observation $rest)
       (case (gslt:normalized:derive $normal $observation)
         (((MFinished $goals $count)
           (let $next (gslt:normalized:normalize $goals)
             (case (gslt:normalized:execute $rest $next)
               (((MExecuted $after $later)
                 (MExecuted $after (+ $count $later)))))))))))))

(: gslt:normalized:run (-> Atom Atom %Undefined%))
(= (gslt:normalized:run $patterns $subject)
   (let* (($programs (gslt:automata:programs $patterns))
          ($observations (gslt:automata:observe $subject LNil))
          ($initial (gslt:automata:seed-all $observations $programs))
          ($normal (gslt:normalized:normalize $initial))
          ($reads (gslt:automata:length $observations)))
     (case (gslt:normalized:execute $observations $normal)
       (((MExecuted $after $dispatches)
         (let* (($goals (gslt:normalized:expand $after))
                ($locations (gslt:automata:completed $goals)))
           (MLocations $locations $reads $dispatches)))))))

(: gslt:normalized:top (-> Atom Atom %Undefined%))
(= (gslt:normalized:top $patterns $subject)
   (let* (($shapes (gslt:automata:shapes $patterns))
          ($tree (gslt:automata:subject $subject)))
     (case (gslt:normalized:run $shapes $tree)
       (((MLocations $locations $reads $dispatches)
         (let $matches (gslt:automata:complete $locations $patterns $subject LNil)
           (MatchRun $matches $reads $dispatches)))))))

; The language matcher keeps the original physical rewrite row list.
(: gslt:normalized:language-top (-> Atom Atom %Undefined%))
(= (gslt:normalized:language-top $language $subject)
   (let $patterns (gslt:automata:language-patterns $language)
     (gslt:normalized:top $patterns $subject)))

; Only root observations authorize directed row execution. Equations remain
; outside this equation-free operational entry, and metadata is retained.
(: gslt:normalized:language-root-reducts (-> Atom Atom Atom %Undefined%))
(= (gslt:normalized:language-root-reducts $language $rows $subject)
   (case $language
     (((GSLTLanguageDefWireV1 $name $types $terms LNil $rewrites)
       (let $matched (gslt:normalized:language-top $language $subject)
         (case $matched
           (((MatchRun $matches $reads $dispatches)
             (gslt:rule:matched-root-reducts $rewrites $rows $matches)))))))))
