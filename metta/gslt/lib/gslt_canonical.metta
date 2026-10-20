; Canonical forms (CanonicalBags.canon, CanonicalCompare.canonBy), loaded over the collection laws.
;
; The canonical form sorts the elements of every unordered collection (hashBag, hashSet), bottom
; up. Patterns are ordered by the lexicographic order of their prefix-free serializations
; (PatternLexOrder.ser, PatternLexOrder.lexLe), compared field by field: the first field that
; differs decides (CanonicalCompare.cmp). Names are ordered by their position in a table that
; lists them in the order of their serializations (CanonicalCompare.nameTable). The table of a
; plan lists its constructors and declared free names, which are all the names of its well-sorted
; states; a name outside the table has no answer.
;
; A run that commits canonical forms commits (gslt:canon:canonical table laws extrusions target):
; the standard form of the declared laws, then the canonical form.

(: gslt:canon:nat-cmp (-> Atom Atom %Undefined%))
(= (gslt:canon:nat-cmp $left $right)
   (if (< $left $right) LT (if (== $left $right) EQ GT)))

; Two names, by their position in the table.
(: gslt:canon:name-scan (-> Atom Atom Atom %Undefined%))
(= (gslt:canon:name-scan $names $left $right)
   (case $names
     (((LCons $name $rest)
       (if (== $name $left) LT
         (if (== $name $right) GT (gslt:canon:name-scan $rest $left $right)))))))

(: gslt:canon:name-cmp (-> Atom Atom Atom %Undefined%))
(= (gslt:canon:name-cmp $names $left $right)
   (if (== $left $right) EQ (gslt:canon:name-scan $names $left $right)))

; Lists of names, as PatternLexOrder.serStringList: the length first.
(: gslt:canon:length-cmp (-> Atom Atom %Undefined%))
(= (gslt:canon:length-cmp $left $right)
   (case $left
     ((LNil (case $right ((LNil EQ) ((LCons $item $rest) LT))))
      ((LCons $first $later)
       (case $right
         ((LNil GT)
          ((LCons $item $rest) (gslt:canon:length-cmp $later $rest))))))))

(: gslt:canon:names-pairwise (-> Atom Atom Atom %Undefined%))
(= (gslt:canon:names-pairwise $names $left $right)
   (case $left
     ((LNil EQ)
      ((LCons $first $later)
       (case $right
         (((LCons $other $rest)
           (let $here (gslt:canon:name-cmp $names $first $other)
             (case $here
               ((EQ (gslt:canon:names-pairwise $names $later $rest))
                ($decided $decided)))))))))))

(: gslt:canon:names-cmp (-> Atom Atom Atom %Undefined%))
(= (gslt:canon:names-cmp $names $left $right)
   (let $byLength (gslt:canon:length-cmp $left $right)
     (case $byLength ((EQ (gslt:canon:names-pairwise $names $left $right)) ($decided $decided)))))

; An optional name, as PatternLexOrder.serOptString: none first.
(: gslt:canon:binder-cmp (-> Atom Atom Atom %Undefined%))
(= (gslt:canon:binder-cmp $names $left $right)
   (case $left
     ((BNone (case $right ((BNone EQ) ((BSome $other) LT))))
      ((BSome $name) (case $right ((BNone GT) ((BSome $other) (gslt:canon:name-cmp $names $name $other))))))))

(: gslt:canon:rest-cmp (-> Atom Atom Atom %Undefined%))
(= (gslt:canon:rest-cmp $names $left $right)
   (case $left
     ((RNone (case $right ((RNone EQ) ((RSome $other) LT))))
      ((RSome $name) (case $right ((RNone GT) ((RSome $other) (gslt:canon:name-cmp $names $name $other))))))))

; The first number of a pattern's serialization.
(: gslt:canon:tag (-> Atom %Undefined%))
(= (gslt:canon:tag $pattern)
   (case $pattern
     (((Var $index) 0)
      ((FVar $name) 1)
      ((PApp $label $arguments) 2)
      ((PLam $binder $body) 3)
      ((PMultiLam $arity $binders $body) 4)
      ((PSubst $body $replacement) 5)
      ((PCollection $kind $elements $rest) 6))))

(: gslt:canon:kind-tag (-> Atom %Undefined%))
(= (gslt:canon:kind-tag $kind)
   (if (== $kind "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec") 0
     (if (== $kind "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag") 1
       (if (== $kind "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashSet") 2 (UnknownCollectionKind $kind)))))

(: gslt:canon:unordered (-> Atom %Undefined%))
(= (gslt:canon:unordered $kind)
   (if (== $kind "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec") False True))

; Two patterns: LT, EQ or GT.
(: gslt:canon:cmp (-> Atom Atom Atom %Undefined%))
(= (gslt:canon:cmp $names $left $right)
   (let* (($leftTag (gslt:canon:tag $left))
          ($rightTag (gslt:canon:tag $right)))
     (if (== $leftTag $rightTag)
       (gslt:canon:cmp-same $names $left $right)
       (gslt:canon:nat-cmp $leftTag $rightTag))))

; Two patterns with the same tag, field by field.
(: gslt:canon:cmp-same (-> Atom Atom Atom %Undefined%))
(= (gslt:canon:cmp-same $names $left $right)
   (case $left
     (((Var $index)
       (case $right (((Var $other) (gslt:canon:nat-cmp $index $other)))))
      ((FVar $name)
       (case $right (((FVar $other) (gslt:canon:name-cmp $names $name $other)))))
      ((PApp $label $arguments)
       (case $right
         (((PApp $otherLabel $otherArguments)
           (let $byLabel (gslt:canon:name-cmp $names $label $otherLabel)
             (case $byLabel
               ((EQ (gslt:canon:cmp-counted $names $arguments $otherArguments))
                ($decided $decided))))))))
      ((PLam $binder $body)
       (case $right
         (((PLam $otherBinder $otherBody)
           (let $byBinder (gslt:canon:binder-cmp $names $binder $otherBinder)
             (case $byBinder
               ((EQ (gslt:canon:cmp $names $body $otherBody))
                ($decided $decided))))))))
      ((PMultiLam $arity $binders $body)
       (case $right
         (((PMultiLam $otherArity $otherBinders $otherBody)
           (let $byArity (gslt:canon:nat-cmp $arity $otherArity)
             (case $byArity
               ((EQ
                 (let $byBinders (gslt:canon:names-cmp $names $binders $otherBinders)
                   (case $byBinders
                     ((EQ (gslt:canon:cmp $names $body $otherBody))
                      ($decided $decided)))))
                ($decided $decided))))))))
      ((PSubst $body $replacement)
       (case $right
         (((PSubst $otherBody $otherReplacement)
           (let $byBody (gslt:canon:cmp $names $body $otherBody)
             (case $byBody
               ((EQ (gslt:canon:cmp $names $replacement $otherReplacement))
                ($decided $decided))))))))
      ((PCollection $kind $elements $rest)
       (case $right
         (((PCollection $otherKind $otherElements $otherRest)
           (let* (($kindTag (gslt:canon:kind-tag $kind))
                  ($otherKindTag (gslt:canon:kind-tag $otherKind))
                  ($byKind (gslt:canon:nat-cmp $kindTag $otherKindTag)))
             (case $byKind
               ((EQ
                 (let $byElements (gslt:canon:cmp-counted $names $elements $otherElements)
                   (case $byElements
                     ((EQ (gslt:canon:rest-cmp $names $rest $otherRest))
                      ($decided $decided)))))
                ($decided $decided)))))))))))

; Lists of patterns with their lengths first, as in the serialization of an application or a
; collection.
(: gslt:canon:cmp-counted (-> Atom Atom Atom %Undefined%))
(= (gslt:canon:cmp-counted $names $left $right)
   (let $byLength (gslt:canon:length-cmp $left $right)
     (case $byLength ((EQ (gslt:canon:cmp-pairwise $names $left $right)) ($decided $decided)))))

(: gslt:canon:cmp-pairwise (-> Atom Atom Atom %Undefined%))
(= (gslt:canon:cmp-pairwise $names $left $right)
   (case $left
     ((LNil EQ)
      ((LCons $first $later)
       (case $right
         (((LCons $other $rest)
           (let $here (gslt:canon:cmp $names $first $other)
             (case $here
               ((EQ (gslt:canon:cmp-pairwise $names $later $rest))
                ($decided $decided)))))))))))

; Insertion sort (List.insertionSort by PatternLexOrder.PatternLe).
(: gslt:canon:insert (-> Atom Atom Atom %Undefined%))
(= (gslt:canon:insert $names $pattern $sorted)
   (case $sorted
     ((LNil (LCons $pattern LNil))
      ((LCons $first $rest)
       (let $order (gslt:canon:cmp $names $pattern $first)
         (case $order
           ((GT (let $tail (gslt:canon:insert $names $pattern $rest) (LCons $first $tail)))
            ($other (LCons $pattern (LCons $first $rest))))))))))

(: gslt:canon:sort (-> Atom Atom %Undefined%))
(= (gslt:canon:sort $names $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $first $rest)
       (let $sorted (gslt:canon:sort $names $rest) (gslt:canon:insert $names $first $sorted))))))

; The canonical form (CanonicalBags.canon): unordered collections sorted, a set's repetitions removed.
(: gslt:canon:canon (-> Atom Atom %Undefined%))
(= (gslt:canon:canon $names $pattern)
   (case $pattern
     (((PApp $label $arguments)
       (let $inner (gslt:canon:canon-list $names $arguments) (PApp $label $inner)))
      ((PLam $binder $body)
       (let $inner (gslt:canon:canon $names $body) (PLam $binder $inner)))
      ((PMultiLam $arity $binders $body)
       (let $inner (gslt:canon:canon $names $body) (PMultiLam $arity $binders $inner)))
      ((PSubst $body $replacement)
       (let* (($innerBody (gslt:canon:canon $names $body))
              ($innerReplacement (gslt:canon:canon $names $replacement)))
         (PSubst $innerBody $innerReplacement)))
      ((PCollection $kind $elements $rest)
       (let $inner (gslt:canon:canon-list $names $elements)
         (if (gslt:canon:unordered $kind)
           (let $sorted (gslt:canon:sort $names $inner)
             (if (gslt:canon:is-set $kind)
               (let $members (gslt:canon:dedup-sorted $sorted) (PCollection $kind $members $rest))
               (PCollection $kind $sorted $rest)))
           (PCollection $kind $inner $rest))))
      ($other $other))))

(: gslt:canon:is-set (-> Atom %Undefined%))
(= (gslt:canon:is-set $kind)
   (== $kind "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashSet"))

; A set's canonical elements once each: in a sorted list equal elements are adjacent, so the
; repetitions are the runs ((List.sortLex l).dedup).
(: gslt:canon:dedup-sorted (-> Atom %Undefined%))
(= (gslt:canon:dedup-sorted $sorted)
   (case $sorted
     ((LNil LNil)
      ((LCons $first $rest)
       (case $rest
         ((LNil (LCons $first LNil))
          ((LCons $second $later)
           (let $tail (gslt:canon:dedup-sorted $rest)
             (if (== $first $second) $tail (LCons $first $tail))))))))))

(: gslt:canon:canon-list (-> Atom Atom %Undefined%))
(= (gslt:canon:canon-list $names $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $pattern $rest)
       (let* (($head (gslt:canon:canon $names $pattern))
              ($tail (gslt:canon:canon-list $names $rest)))
         (LCons $head $tail))))))

; Deep splicing (Wrappers.deepSplice): a nested collection of the kind without a rest contributes its
; elements, spliced again, and the unit contributes nothing.
(: gslt:canon:deep-splice (-> Atom Atom %Undefined%))
(= (gslt:canon:deep-splice $law $item)
   (case $law
     (((CollectionLaw $lawKind $unit)
       (case $item
         (((PCollection $actual $elements RNone)
           (if (== $actual $lawKind) (gslt:canon:deep-splice-all $law $elements) (LCons $item LNil)))
          ((PApp $label $arguments)
           (case $arguments
             ((LNil
               (case $unit
                 ((UNone (LCons $item LNil))
                  ((USome $name) (if (== $label $name) LNil (LCons $item LNil))))))
              ($more (LCons $item LNil)))))
          ($other (LCons $item LNil))))))))

; Every element deeply spliced, in order.
(: gslt:canon:deep-splice-all (-> Atom Atom %Undefined%))
(= (gslt:canon:deep-splice-all $law $items)
   (case $items
     ((LNil LNil)
      ((LCons $item $rest)
       (let* (($here (gslt:canon:deep-splice $law $item))
              ($later (gslt:canon:deep-splice-all $law $rest)))
         (gslt:automata:append $here $later))))))

; The wrapper collapse (Wrappers.wrapFinish): without a rest, one element is that element and none is
; the unit, when the kind declares one.
(: gslt:canon:wrap-finish (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:canon:wrap-finish $law $kind $items $rest)
   (case $rest
     ((RNone
       (case $items
         ((LNil
           (case $law
             (((CollectionLaw $lawKind $unit)
               (case $unit
                 ((UNone (PCollection $kind LNil RNone))
                  ((USome $name) (PApp $name LNil))))))))
          ((LCons $item LNil) $item)
          ($more (PCollection $kind $items RNone)))))
      ($some (PCollection $kind $items $rest)))))

; A set's elements in canonical form once each (Wrappers.setForm): the canonical form of each, then the
; repetitions removed keeping the last ((items.map canon).dedup); a bag's or a vector's as they are.
(: gslt:canon:set-form (-> Atom Atom Atom %Undefined%))
(= (gslt:canon:set-form $names $kind $items)
   (if (gslt:canon:is-set $kind)
     (let $canonical (gslt:canon:canon-list $names $items) (gslt:canon:dedup $canonical))
     $items))

(: gslt:canon:member (-> Atom Atom %Undefined%))
(= (gslt:canon:member $item $items)
   (case $items
     ((LNil False)
      ((LCons $first $rest) (if (== $item $first) True (gslt:canon:member $item $rest))))))

(: gslt:canon:dedup (-> Atom %Undefined%))
(= (gslt:canon:dedup $items)
   (case $items
     ((LNil LNil)
      ((LCons $first $rest)
       (let $tail (gslt:canon:dedup $rest)
         (if (gslt:canon:member $first $rest) $tail (LCons $first $tail)))))))

; The model normal form (Wrappers.modelNormal): bottom up, the quote-drop test at each constructor,
; deep splicing and unit removal at each collection of a kind with a law, a set's elements in canonical
; form once each, then the wrapper collapse.
(: gslt:canon:model-normal (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:canon:model-normal $names $quote $drop $laws $pattern)
   (case $pattern
     (((PApp $label $arguments)
       (let $inner (gslt:canon:model-normal-list $names $quote $drop $laws $arguments)
         (gslt:rule:scope-reflective-normalize-finish $quote $drop $label $inner)))
      ((PLam $binder $body)
       (let $inner (gslt:canon:model-normal $names $quote $drop $laws $body) (PLam $binder $inner)))
      ((PMultiLam $arity $binders $body)
       (let $inner (gslt:canon:model-normal $names $quote $drop $laws $body) (PMultiLam $arity $binders $inner)))
      ((PSubst $body $replacement)
       (let* (($innerBody (gslt:canon:model-normal $names $quote $drop $laws $body))
              ($innerReplacement (gslt:canon:model-normal $names $quote $drop $laws $replacement)))
         (PSubst $innerBody $innerReplacement)))
      ((PCollection $kind $elements $rest)
       (let* (($inner (gslt:canon:model-normal-list $names $quote $drop $laws $elements))
              ($law (gslt:laws:law-for $laws $kind)))
         (case $law
           ((None (PCollection $kind $inner $rest))
            ((Some $found)
             (let* (($spliced (gslt:canon:deep-splice-all $found $inner))
                    ($items (gslt:canon:set-form $names $kind $spliced)))
               (gslt:canon:wrap-finish $found $kind $items $rest)))))))
      ($other $other))))

(: gslt:canon:model-normal-list (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:canon:model-normal-list $names $quote $drop $laws $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $pattern $rest)
       (let* (($head (gslt:canon:model-normal $names $quote $drop $laws $pattern))
              ($tail (gslt:canon:model-normal-list $names $quote $drop $laws $rest)))
         (LCons $head $tail))))))

; The standard form, then the canonical form.
(: gslt:canon:canonical (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:canon:canonical $names $laws $extrusions $pattern)
   (let $standard (gslt:laws:standard $laws $extrusions $pattern) (gslt:canon:canon $names $standard)))
