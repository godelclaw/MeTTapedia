; Lexicographic canonical forms of closed rho processes. Self-contained.
;
; A process is encoded as the wire pattern of the GSLT presentation: (Var i),
; (PApp name arguments), (PLam BNone body) and the parallel bag
; (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" elements RNone).
; The canonical form splices nested bags, removes nil components, sorts the
; components, removes an empty or singleton bag wrapper, and orients the name
; equation @(*x) = x. Components are sorted by insertion sort on the
; lexicographic order of a prefix-free serialization: a constructor name is
; serialized as its length followed by its character codes. Closed rho processes
; use only the five constructor names of the table below.

(: rho:lex:name-ser (-> Atom %Undefined%))
(= (rho:lex:name-ser $name)
   (if (== $name "NQuote") (LCons 6 (LCons 78 (LCons 81 (LCons 117 (LCons 111 (LCons 116 (LCons 101 LNil)))))))
   (if (== $name "PDrop") (LCons 5 (LCons 80 (LCons 68 (LCons 114 (LCons 111 (LCons 112 LNil))))))
   (if (== $name "PInput") (LCons 6 (LCons 80 (LCons 73 (LCons 110 (LCons 112 (LCons 117 (LCons 116 LNil)))))))
   (if (== $name "POutput")
     (LCons 7 (LCons 80 (LCons 79 (LCons 117 (LCons 116 (LCons 112 (LCons 117 (LCons 116 LNil))))))))
   (if (== $name "PZero") (LCons 5 (LCons 80 (LCons 90 (LCons 101 (LCons 114 (LCons 111 LNil))))))
     (UnknownRhoConstructor $name)))))))

(: rho:lex:append (-> Atom Atom %Undefined%))
(= (rho:lex:append $left $right)
   (case $left
     ((LNil $right)
      ((LCons $first $rest) (let $tail (rho:lex:append $rest $right) (LCons $first $tail))))))

(: rho:lex:length (-> Atom %Undefined%))
(= (rho:lex:length $items)
   (case $items
     ((LNil 0)
      ((LCons $item $rest) (let $tail (rho:lex:length $rest) (+ $tail 1))))))

(: rho:lex:ser (-> Atom %Undefined%))
(= (rho:lex:ser $pattern)
   (case $pattern
     (((Var $index) (LCons 0 (LCons $index LNil)))
      ((PApp $name $arguments)
       (let* (($head (rho:lex:name-ser $name))
              ($count (rho:lex:length $arguments))
              ($body (rho:lex:ser-list $arguments))
              ($all (rho:lex:append $head (LCons $count $body))))
         (LCons 2 $all)))
      ((PLam BNone $body)
       (let $inner (rho:lex:ser $body) (LCons 3 (LCons 0 $inner))))
      ((PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" $elements RNone)
       (let* (($count (rho:lex:length $elements))
              ($body (rho:lex:ser-list $elements))
              ($all (rho:lex:append $body (LCons 0 LNil))))
         (LCons 6 (LCons 1 (LCons $count $all))))))))

(: rho:lex:ser-list (-> Atom %Undefined%))
(= (rho:lex:ser-list $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $first $rest)
       (let* (($head (rho:lex:ser $first)) ($tail (rho:lex:ser-list $rest)))
         (rho:lex:append $head $tail))))))

; Lexicographic order of number lists; a proper prefix comes first.
(: rho:lex:le (-> Atom Atom %Undefined%))
(= (rho:lex:le $left $right)
   (case $left
     ((LNil True)
      ((LCons $x $xs)
       (case $right
         ((LNil False)
          ((LCons $y $ys)
           (if (< $x $y) True
             (if (== $x $y) (rho:lex:le $xs $ys) False)))))))))

(: rho:lex:insert (-> Atom Atom %Undefined%))
(= (rho:lex:insert $pattern $sorted)
   (case $sorted
     ((LNil (LCons $pattern LNil))
      ((LCons $first $rest)
       (let* (($key (rho:lex:ser $pattern))
              ($firstKey (rho:lex:ser $first))
              ($before (rho:lex:le $key $firstKey)))
         (if $before (LCons $pattern (LCons $first $rest))
           (let $tail (rho:lex:insert $pattern $rest) (LCons $first $tail))))))))

(: rho:lex:sort (-> Atom %Undefined%))
(= (rho:lex:sort $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $first $rest)
       (let $sorted (rho:lex:sort $rest) (rho:lex:insert $first $sorted))))))

; Keep the components that are not the parallel unit.
(: rho:lex:non-zero (-> Atom %Undefined%))
(= (rho:lex:non-zero $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $first $rest)
       (let $tail (rho:lex:non-zero $rest)
         (case $first
           (((PApp "PZero" LNil) $tail)
            ($other (LCons $other $tail)))))))))

; Splice nested bags into their parent and remove the parallel unit.
(: rho:lex:contents (-> Atom %Undefined%))
(= (rho:lex:contents $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $first $rest)
       (let $tail (rho:lex:contents $rest)
         (case $first
           (((PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" $inner RNone)
             (let $kept (rho:lex:non-zero $inner) (rho:lex:append $kept $tail)))
            ((PApp "PZero" LNil) $tail)
            ($other (LCons $other $tail)))))))))

(: rho:lex:collapse (-> Atom %Undefined%))
(= (rho:lex:collapse $patterns)
   (case $patterns
     ((LNil (PApp "PZero" LNil))
      ((LCons $only LNil) $only)
      ($many (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" $many RNone)))))

; Orient @(*x) = x; any other name stays quoted.
(: rho:lex:quote (-> Atom %Undefined%))
(= (rho:lex:quote $pattern)
   (case $pattern
     (((PApp "PDrop" (LCons $name LNil)) $name)
      ($other (PApp "NQuote" (LCons $other LNil))))))

(: rho:lex:canonical (-> Atom %Undefined%))
(= (rho:lex:canonical $pattern)
   (case $pattern
     (((Var $index) (Var $index))
      ((PApp "NQuote" (LCons $argument LNil))
       (let $inner (rho:lex:canonical $argument) (rho:lex:quote $inner)))
      ((PApp $name $arguments)
       (let $inner (rho:lex:canonical-list $arguments) (PApp $name $inner)))
      ((PLam $binder $body)
       (let $inner (rho:lex:canonical $body) (PLam $binder $inner)))
      ((PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" $elements RNone)
       (let* (($inner (rho:lex:canonical-list $elements))
              ($contents (rho:lex:contents $inner))
              ($sorted (rho:lex:sort $contents)))
         (rho:lex:collapse $sorted))))))

(: rho:lex:canonical-list (-> Atom %Undefined%))
(= (rho:lex:canonical-list $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $first $rest)
       (let* (($head (rho:lex:canonical $first)) ($tail (rho:lex:canonical-list $rest)))
         (LCons $head $tail))))))
