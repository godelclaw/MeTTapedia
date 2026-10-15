; Contextual certificates for authored equations. Load the retained matcher,
; rule helpers and gslt_equation_execution.metta first.
; Positions are physical child-index lists; EqSite is temporary zipper data.
; No source equation is inserted into the directed rewrite list.

(: gslt:equation-context:split (-> Atom Atom %Undefined%))
(= (gslt:equation-context:split $index $children)
   (case $children
     ((LNil None)
      ((LCons $head $rest)
       (if (== $index 0)
         (Some (EqSite LNil $head $rest))
         (let $previous (- $index 1)
           (case (gslt:equation-context:split $previous $rest)
             ((None None)
              ((Some (EqSite $before $focus $after))
               (Some (EqSite (LCons $head $before) $focus $after)))))))))))

(: gslt:equation-context:focus (-> Atom Atom %Undefined%))
(= (gslt:equation-context:focus $position $subject)
   (case ($position $subject)
     (((LNil $value) (Some $value))
      (((LCons $index $path) (PApp $head $children))
       (case (gslt:rule:row-at $index $children)
         ((None None)
          ((Some $child) (gslt:equation-context:focus $path $child)))))
      ($bad None))))

; Remove only the separate authored equation list from the operational view.
; Constructor metadata and every directed row remain exactly as supplied.
; Admission of generated collection/algebra laws belongs to the profile.
(: gslt:equation-context:directed-view (-> Atom %Undefined%))
(= (gslt:equation-context:directed-view $language)
   (case $language
     (((GSLTLanguageDefWireV1 $name $types $terms $equations $rewrites)
       (GSLTLanguageDefWireV1 $name $types $terms LNil $rewrites))
      ($bad None))))

; Validate this post-certificate separately at each actual directed result.
; Successful duplicate results stay duplicate, in their authored order.
(: gslt:equation-context:after-results (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:equation-context:after-results $equations $rows $receipts $results)
   (case $results
     ((LNil LNil)
      ((LCons $result $rest)
       (let* (($checked (gslt:equation-context:replay $equations $rows $result $receipts))
              ($tail (gslt:equation-context:after-results $equations $rows $receipts $rest)))
         (case $checked
           ((None $tail)
            ((Some $target) (LCons $target $tail))))))
      ($bad LNil))))

; One directed frontier between two supplied equation-route certificates.
; Refusal says nothing about other certificates or equivalent reductions.
(: gslt:equation-context:witnessed-reducts (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:equation-context:witnessed-reducts $strategy $language $rows $depth $subject $before $after)
   (case $language
     (((GSLTLanguageDefWireV1 $name $types $terms $equations $rewrites)
       (case (gslt:equation-context:replay $equations $rows $subject $before)
         ((None LNil)
          ((Some $redex)
           (let* (($view (gslt:equation-context:directed-view $language))
                  ($frontier (gslt:rule:language-contextual-reducts $strategy $view $rows $depth $redex)))
             (gslt:equation-context:after-results $equations $rows $after $frontier))))))
      ($bad LNil))))

(: gslt:equation-context:replace (-> Atom Atom Atom %Undefined%))
(= (gslt:equation-context:replace $position $subject $target)
   (case ($position $subject)
     (((LNil $value) (Some $target))
      (((LCons $index $path) (PApp $head $children))
       (case (gslt:equation-context:split $index $children)
         ((None None)
          ((Some (EqSite $before $focus $after))
           (case (gslt:equation-context:replace $path $focus $target)
             ((None None)
              ((Some $replacement)
               (let $filled (gslt:automata:append $before (LCons $replacement $after))
                 (Some (PApp $head $filled))))))))))
      ($bad None))))

; Resolve and check the local witness before reconstructing its claimed whole.
(: gslt:equation-context:validate (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:equation-context:validate $equations $rows $subject $receipt)
   (case $receipt
     (((EqAt $position $atomic $whole)
       (case (gslt:equation-context:focus $position $subject)
         ((None None)
          ((Some $focus)
           (case (gslt:equation:validate $equations $rows $focus $atomic)
             ((None None)
              ((Some $target)
               (case (gslt:equation-context:replace $position $subject $target)
                 ((None None)
                  ((Some $actual) (if (== $actual $whole) (Some $actual) None)))))))))))
      ((EqPrevious $predecessor (EqAt $position $atomic $whole))
       (case (gslt:equation-context:validate $equations $rows $predecessor
               (EqAt $position $atomic $whole))
         ((None None)
          ((Some $actual)
           (if (== $actual $subject) (Some $predecessor) None)))))
      ($bad None))))

; An empty certificate certifies reflexivity, not a search result. Each later
; receipt is checked against the actual preceding endpoint.
(: gslt:equation-context:replay (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:equation-context:replay $equations $rows $subject $receipts)
   (case $receipts
     ((LNil (Some $subject))
      ((LCons $receipt $rest)
       (case (gslt:equation-context:validate $equations $rows $subject $receipt)
         ((None None)
          ((Some $next) (gslt:equation-context:replay $equations $rows $next $rest)))))
      ($bad None))))

; Lift each authored atomic occurrence through the existing physical context.
(: gslt:equation-context:lift (-> Atom Atom Atom %Undefined%))
(= (gslt:equation-context:lift $position $subject $receipts)
   (case $receipts
     ((LNil LNil)
      ((LCons $atomic $rest)
       (let $tail (gslt:equation-context:lift $position $subject $rest)
         (case $atomic
           (((EqInstance $index $orientation $initial $choices $completed $target)
             (case (gslt:equation-context:replace $position $subject $target)
               ((None $tail)
                ((Some $whole) (LCons (EqAt $position $atomic $whole) $tail)))))
            ($bad $tail)))))
      ($bad LNil))))

; Positions come from the retained matcher's exact singleton-wildcard run.
(: gslt:equation-context:frontier-matches (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:equation-context:frontier-matches $equations $rows $subject $matches)
   (case $matches
     ((LNil LNil)
      ((LCons (Found $position $occurrence $bindings) $rest)
       (let $tail (gslt:equation-context:frontier-matches $equations $rows $subject $rest)
         (case (gslt:equation-context:focus $position $subject)
           ((None $tail)
            ((Some $focus)
             (let* (($atomic (gslt:equation:root $equations $rows $focus))
                    ($head (gslt:equation-context:lift $position $subject $atomic)))
               (gslt:automata:append $head $tail)))))))
      ($bad LNil))))

(: gslt:equation-context:frontier (-> Atom Atom Atom %Undefined%))
(= (gslt:equation-context:frontier $equations $rows $subject)
   (case (gslt:automata:top (LCons (FVar "EqFocus") LNil) $subject)
     (((MatchRun $matches $reads $dispatches)
       (gslt:equation-context:frontier-matches $equations $rows $subject $matches))
      ($bad LNil))))

; The first valid authored occurrence is selected without deduplication.
(: gslt:equation-context:find-target (-> Atom Atom %Undefined%))
(= (gslt:equation-context:find-target $receipts $target)
   (case $receipts
     ((LNil None)
      ((LCons $receipt $rest)
       (case $receipt
         (((EqAt $position $atomic $whole)
           (if (== $whole $target) (Some $receipt)
             (gslt:equation-context:find-target $rest $target)))
          ($bad (gslt:equation-context:find-target $rest $target)))))
      ($bad None))))

; Reverse acquisition checks the original oriented witness at the predecessor.
(: gslt:equation-context:find-signed (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:equation-context:find-signed $equations $rows $subject $target)
   (let $forward (gslt:equation-context:frontier $equations $rows $subject)
     (case (gslt:equation-context:find-target $forward $target)
       (((Some $receipt) (Some $receipt))
        (None
         (let $previous (gslt:equation-context:frontier $equations $rows $target)
           (case (gslt:equation-context:find-target $previous $subject)
             ((None None)
              ((Some $receipt)
               (case (gslt:equation-context:validate $equations $rows $target $receipt)
                 ((None None)
                  ((Some $actual)
                   (if (== $actual $subject)
                     (Some (EqPrevious $target $receipt)) None)))))))))))))

; The list contains successive candidate endpoints, excluding the initial one.
; A refused adjacency is not an inequivalence or global-search verdict.
(: gslt:equation-context:acquire-path (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:equation-context:acquire-path $equations $rows $subject $endpoints)
   (case $endpoints
     ((LNil (Some LNil))
      ((LCons $next $rest)
       (case (gslt:equation-context:find-signed $equations $rows $subject $next)
         ((None None)
          ((Some $receipt)
           (case (gslt:equation-context:acquire-path $equations $rows $next $rest)
             ((None None)
              ((Some $receipts) (Some (LCons $receipt $receipts)))))))))
      ($bad None))))

; Acquisition and replay use the same finite endpoint list and receipt sequence.
(: gslt:equation-context:acquired-replay (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:equation-context:acquired-replay $equations $rows $subject $endpoints)
   (case (gslt:equation-context:acquire-path $equations $rows $subject $endpoints)
     ((None None)
      ((Some $receipts)
       (gslt:equation-context:replay $equations $rows $subject $receipts)))))

; A separate checked continuation is acquired at each actual directed result.
; This stable filter retains every successful occurrence, including duplicates.
(: gslt:equation-context:acquired-after-results (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:equation-context:acquired-after-results $equations $rows $receipts $results)
   (case $results
     ((LNil LNil)
      ((LCons $result $rest)
       (let* (($checked (gslt:equation-context:acquired-replay $equations $rows $result $receipts))
              ($tail (gslt:equation-context:acquired-after-results $equations $rows $receipts $rest)))
         (case $checked
           ((None $tail)
            ((Some $target) (LCons $target $tail))))))
      ($bad LNil))))

; One original directed frontier between two acquired equation continuations.
; The before/after lists are endpoint traces, not a request to orient equations.
(: gslt:equation-context:acquired-witnessed-reducts (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:equation-context:acquired-witnessed-reducts $strategy $language $rows $depth $subject $before $after)
   (case $language
     (((GSLTLanguageDefWireV1 $name $types $terms $equations $rewrites)
       (case (gslt:equation-context:acquired-replay $equations $rows $subject $before)
         ((None LNil)
          ((Some $redex)
           (let* (($view (gslt:equation-context:directed-view $language))
                  ($frontier (gslt:rule:language-contextual-reducts $strategy $view $rows $depth $redex)))
             (gslt:equation-context:acquired-after-results $equations $rows $after $frontier))))))
      ($bad LNil))))
