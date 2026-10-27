; Rows are (source-index integer-score payload). Equal scores retain source
; order; payloads remain data. The spine is RankNil / (RankCons row rest).
; Sequence computed arguments explicitly.
(: rank:insert (-> Atom Atom Atom))
(= (rank:insert $row $rows)
   (case $rows
     ((RankNil (RankCons $row RankNil))
      ((RankCons $first $rest)
         (let $score (index-atom $row 1)
           (let $head-score (index-atom $first 1)
             (if (>= $score $head-score) (RankCons $row $rows)
               (let $tail (rank:insert $row $rest)
                 (RankCons $first $tail)))))))))

(: rank:sort (-> Atom Atom))
(= (rank:sort $rows)
   (case $rows
     ((RankNil RankNil)
      ((RankCons $first $rest)
        (let $sorted (rank:sort $rest) (rank:insert $first $sorted))))))

(: rank:eligible (-> Atom Atom Atom))
(= (rank:eligible $before $rows)
   (case $rows
     ((RankNil RankNil)
      ((RankCons $first $rest)
         (let $index (index-atom $first 0)
           (let $tail (rank:eligible $before $rest)
             (if (< $index $before) (RankCons $first $tail) $tail)))))))

(: rank:take (-> Atom Atom Atom))
(= (rank:take $budget $rows)
   (if (<= $budget 0) RankNil
     (case $rows
       ((RankNil RankNil)
        ((RankCons $first $rest)
           (let $remaining (- $budget 1)
             (let $tail (rank:take $remaining $rest)
               (RankCons $first $tail))))))))

; Truncate after every insertion so a recursive result holds at most budget
; entries. The proof compares this implementation with stable full sorting.
(: rank:bounded (-> Atom Atom Atom))
(= (rank:bounded $budget $rows)
   (if (<= $budget 0) RankNil
     (case $rows
       ((RankNil RankNil)
        ((RankCons $first $rest)
          (let $tail (rank:bounded $budget $rest)
            (let $inserted (rank:insert $first $tail)
              (rank:take $budget $inserted))))))))

(: rank:select (-> Atom Atom Atom Atom))
(= (rank:select $before $budget $rows)
   (let $candidates (rank:eligible $before $rows)
     (rank:bounded $budget $candidates)))
