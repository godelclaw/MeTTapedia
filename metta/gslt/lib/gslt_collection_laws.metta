; Declared collection laws, as a normal form (OSLF/MeTTaIL/CollectionLaws.lean).
;
; A law is (CollectionLaw kind unit): collections of `kind` flatten, and `unit` is
; UNone or (USome label), a nullary constructor dropped inside them. Inside a
; collection whose kind has a law, an element that is a collection of that kind
; without a rest is spliced in, and the unit is dropped. Normalization is bottom up.

; The law for a kind: (Some law) or None.
(: gslt:laws:law-for (-> Atom Atom %Undefined%))
(= (gslt:laws:law-for $laws $kind)
   (case $laws
     ((LNil None)
      ((LCons (CollectionLaw $lawKind $unit) $rest)
       (if (== $lawKind $kind)
         (Some (CollectionLaw $lawKind $unit))
         (gslt:laws:law-for $rest $kind))))))

; One normalized element, spliced into its parent collection (CollectionLaws.splice).
(: gslt:laws:splice (-> Atom Atom %Undefined%))
(= (gslt:laws:splice $law $item)
   (case $law
     (((CollectionLaw $lawKind $unit)
       (case $item
         (((PCollection $actual $elements RNone)
           (if (== $actual $lawKind) $elements (LCons $item LNil)))
          ((PApp $label $arguments)
           (case $arguments
             ((LNil
               (case $unit
                 ((UNone (LCons $item LNil))
                  ((USome $name) (if (== $label $name) LNil (LCons $item LNil))))))
              ($more (LCons $item LNil)))))
          ($other (LCons $item LNil))))))))

; Every element spliced, in order.
(: gslt:laws:splice-all (-> Atom Atom %Undefined%))
(= (gslt:laws:splice-all $law $items)
   (case $items
     ((LNil LNil)
      ((LCons $item $rest)
       (let* (($here (gslt:laws:splice $law $item))
              ($later (gslt:laws:splice-all $law $rest)))
         (gslt:automata:append $here $later))))))

; The normal form (CollectionLaws.normalize).
(: gslt:laws:normalize (-> Atom Atom %Undefined%))
(= (gslt:laws:normalize $laws $pattern)
   (case $pattern
     (((PApp $label $arguments)
       (let $inner (gslt:laws:normalize-list $laws $arguments) (PApp $label $inner)))
      ((PLam $binder $body)
       (let $inner (gslt:laws:normalize $laws $body) (PLam $binder $inner)))
      ((PMultiLam $arity $binders $body)
       (let $inner (gslt:laws:normalize $laws $body) (PMultiLam $arity $binders $inner)))
      ((PSubst $body $replacement)
       (let* (($innerBody (gslt:laws:normalize $laws $body))
              ($innerReplacement (gslt:laws:normalize $laws $replacement)))
         (PSubst $innerBody $innerReplacement)))
      ((PCollection $kind $elements $rest)
       (let* (($inner (gslt:laws:normalize-list $laws $elements))
              ($law (gslt:laws:law-for $laws $kind)))
         (case $law
           ((None (PCollection $kind $inner $rest))
            ((Some $found)
             (let $spliced (gslt:laws:splice-all $found $inner) (PCollection $kind $spliced $rest)))))))
      ($other $other))))

(: gslt:laws:normalize-list (-> Atom Atom %Undefined%))
(= (gslt:laws:normalize-list $laws $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $pattern $rest)
       (let* (($head (gslt:laws:normalize $laws $pattern))
              ($tail (gslt:laws:normalize-list $laws $rest)))
         (LCons $head $tail))))))

; Declared scope extrusion, run as a normalizer (CollectionLaws.extrude).
;
; An extrusion is (Extrusion kind binder): inside a collection of `kind`, each element
; (PApp binder (LCons (PLam display body) LNil)) is hoisted out; the other elements move
; under its binder with indices lifted by one, and a body of the same kind is spliced in.

; The extrusion for a kind: (Some extrusion) or None.
(: gslt:laws:extrusion-for (-> Atom Atom %Undefined%))
(= (gslt:laws:extrusion-for $extrusions $kind)
   (case $extrusions
     ((LNil None)
      ((LCons (Extrusion $extrusionKind $binder) $rest)
       (if (== $extrusionKind $kind)
         (Some (Extrusion $extrusionKind $binder))
         (gslt:laws:extrusion-for $rest $kind))))))

; A hoisted body's elements: its own elements when it is a collection of the kind.
(: gslt:laws:body-items (-> Atom Atom %Undefined%))
(= (gslt:laws:body-items $kind $body)
   (case $body
     (((PCollection $actual $elements RNone)
       (if (== $actual $kind) $elements (LCons $body LNil)))
      ($other (LCons $body LNil)))))

; Hoist every binder element, left to right (CollectionLaws.hoist).
(: gslt:laws:hoist (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:laws:hoist $extrusion $fuel $done $todo)
   (case $extrusion
     (((Extrusion $kind $binder)
       (if (== $fuel 0)
         (let $all (gslt:automata:append $done $todo) (PCollection $kind $all RNone))
         (case $todo
           ((LNil (PCollection $kind $done RNone))
            ((LCons $item $rest)
             (let $next (- $fuel 1)
               (case $item
                 (((PApp $label (LCons (PLam $display $body) LNil))
                   (if (== $label $binder)
                     (let* (($inner (gslt:laws:body-items $kind $body))
                            ($liftedDone (gslt:rule:lift-bvars-list 0 1 $done))
                            ($liftedRest (gslt:rule:lift-bvars-list 0 1 $rest))
                            ($remaining (gslt:automata:append $inner $liftedRest))
                            ($hoisted (gslt:laws:hoist $extrusion $next $liftedDone $remaining)))
                       (PApp $label (LCons (PLam $display $hoisted) LNil)))
                     (let $kept (gslt:automata:append $done (LCons $item LNil))
                       (gslt:laws:hoist $extrusion $next $kept $rest))))
                  ($other
                   (let $kept (gslt:automata:append $done (LCons $item LNil))
                     (gslt:laws:hoist $extrusion $next $kept $rest))))))))))))))

; Scope extrusion, bottom up (CollectionLaws.extrude).
(: gslt:laws:extrude (-> Atom Atom %Undefined%))
(= (gslt:laws:extrude $extrusions $pattern)
   (case $pattern
     (((PApp $label $arguments)
       (let $inner (gslt:laws:extrude-list $extrusions $arguments) (PApp $label $inner)))
      ((PLam $binder $body)
       (let $inner (gslt:laws:extrude $extrusions $body) (PLam $binder $inner)))
      ((PMultiLam $arity $binders $body)
       (let $inner (gslt:laws:extrude $extrusions $body) (PMultiLam $arity $binders $inner)))
      ((PSubst $body $replacement)
       (let* (($innerBody (gslt:laws:extrude $extrusions $body))
              ($innerReplacement (gslt:laws:extrude $extrusions $replacement)))
         (PSubst $innerBody $innerReplacement)))
      ((PCollection $kind $elements $rest)
       (let $inner (gslt:laws:extrude-list $extrusions $elements)
         (case $rest
           ((RNone
             (let $found (gslt:laws:extrusion-for $extrusions $kind)
               (case $found
                 ((None (PCollection $kind $inner RNone))
                  ((Some $extrusion)
                   (let* (($size (gslt:deep:nodes-list $inner))
                          ($count (gslt:automata:length $inner))
                          ($double (+ $size $size))
                          ($sum (+ $double $count))
                          ($fuel (+ $sum 1)))
                     (gslt:laws:hoist $extrusion $fuel LNil $inner)))))))
            ($named (PCollection $kind $inner $rest))))))
      ($other $other))))

(: gslt:laws:extrude-list (-> Atom Atom %Undefined%))
(= (gslt:laws:extrude-list $extrusions $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $pattern $rest)
       (let* (($head (gslt:laws:extrude $extrusions $pattern))
              ($tail (gslt:laws:extrude-list $extrusions $rest)))
         (LCons $head $tail))))))

; The standard form: collection laws, then scope extrusion (CollectionLaws.standardForm).
(: gslt:laws:standard (-> Atom Atom Atom %Undefined%))
(= (gslt:laws:standard $laws $extrusions $pattern)
   (let $normal (gslt:laws:normalize $laws $pattern) (gslt:laws:extrude $extrusions $normal)))
