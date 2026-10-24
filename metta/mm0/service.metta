; A saved proof contributes its computed conclusion only after it is checked.
; Theory, variables and assumptions remain fixed throughout the local scope.
(: mm0:shared-proof (-> Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:shared-proof $terms $defs $thms $ctx $hyps (MM0:L $saved) $root $claim)
   (let $store (mm0:vector $hyps)
     (mm0:shared-entries $terms $defs $thms $ctx $store $saved 0 $root $claim)))
(: mm0:shared-entries (-> Atom Atom Atom Atom Atom Atom Number Atom Atom %Undefined%))
(= (mm0:shared-entries $terms $defs $thms $ctx $hyps $saved $index $root $claim)
   (if (< $index (size-atom $saved))
     (let (MM0:Saved $expected $proof) (index-atom $saved $index)
       (let $answer (mm0:proof $terms $defs $thms $ctx $hyps $proof)
         (case $answer
           (((Some $actual)
             (if (case $expected ((None True) ((Some $wanted) (== $wanted $actual))))
                 (let $next (mm0:vector-snoc $hyps $actual)
                   (mm0:shared-entries $terms $defs $thms $ctx $next
                                      $saved (+ $index 1) $root $claim))
                 False))
            (None False)
            ($malformed MM0:Malformed)))))
     (mm0:check-proof $terms $defs $thms $ctx $hyps $root $claim)))

; Specification checks and declaration formation are the authored operations.
; Only the representation of a shared theorem differs from an ordinary proof.
(: mm0:service-step (-> Atom Atom %Undefined%))
(= (mm0:service-step $state $command)
   (case ($state $command)
     (((
         (MM0:L (MM0:SpecificationState
           (MM0:L (MM0:Theory $sorts $terms $defs $thms)) $pending))
         (MM0:SharedTheorem $local $index
           (MM0:L (MM0:Theorem $args $hyps $claim)) $dummies $saved $root))
       (let $shape (MM0:L (MM0:AdmitTheorem $index
                         (MM0:L (MM0:Theorem $args $hyps $claim)) $dummies $root))
         (let $next (mm0:spec-pending $local $pending $shape)
           (case $next
             (((Some $remaining)
               (if (mm0:admission-fresh $thms $index)
                 (if (mm0:form-theorem $sorts $terms
                       (MM0:L (MM0:Theorem $args $hyps $claim)))
                   (if (mm0:form-dummies $sorts $dummies)
                     (let $extra (mm0:dummy-context $dummies)
                       (let $ctx (mm0:list-append $args $extra)
                         (if (mm0:shared-proof $terms $defs $thms $ctx $hyps
                                               $saved $root $claim)
                           (let $published (mm0:admission-publish
                             (MM0:L (MM0:Theory $sorts $terms $defs $thms)) $shape)
                             (mm0:spec-admitted $published $remaining))
                           None)))
                     None)
                   None)
                 None))
              (None None)
              ($malformed MM0:Malformed))))))
      (($other $ordinary) (mm0:spec-step $other $ordinary)))))

; The session begins from the empty theory and the independently supplied spec.
; A refusal is sticky: subsequent commands cannot reopen a failed session.
(: mm0:start (-> Atom %Undefined%))
(= (mm0:start $spec)
   (let $cache (new-space)
    (let $set (change-state! mm0-inference-cache $cache)
     (let $proofs (new-space)
      (let $setProofs (change-state! mm0-proof-store $proofs)
     (let $sorts (new-space)
     (let $terms (new-space)
       (let $defs (new-space)
         (let $thms (new-space)
           (let $done (change-state! mm0-session
             (Some (MM0:L (MM0:SpecificationState
               (MM0:L (MM0:Theory (MM0:Table $sorts) (MM0:Table $terms)
                                 (MM0:Table $defs) (MM0:Table $thms))) $spec))))
             True))))))))))
(: mm0:submit (-> Atom %Undefined%))
(= (mm0:submit $command)
   (let $current (get-state mm0-session)
     (case $current
       (((Some $state)
         (let $cache (get-state mm0-inference-cache)
          (let $set (mm0:clear-space $cache ($reset0 $reset1 $reset2 $reset3))
           (let $answer (mm0:service-step $state $command)
           (let $done (change-state! mm0-session $answer)
             (case $answer (((Some $next) True) (None False)
                            ($malformed MM0:Malformed))))))))
        (None False)
        ($malformed MM0:Malformed)))))
(: mm0:finish (-> %Undefined%))
(= (mm0:finish)
   (let $current (get-state mm0-session)
     (case $current
       (((Some $state)
         (let $answer (mm0:spec-finish $current)
           (case $answer (((Some $theory) True) (None False)
                          ($malformed MM0:Malformed)))))
        (None False)
        ($malformed MM0:Malformed)))))
