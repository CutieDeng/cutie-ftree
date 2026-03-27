#lang racket/base

(require racket/match racket/list)
(require "private/core.rkt" "private/core-algorithm.rkt")

;; ========================================
;; Interval Tree based on Finger Tree
;; ========================================
;;
;; Persistent interval tree using Hinze & Paterson's technique:
;; - Intervals stored ordered by low endpoint
;; - Measure: (min-lo, max-hi) for subtree pruning
;; - O(log n) insert/delete
;; - O(log n + k) overlap queries (k = result count)

;; Interval representation: (lo hi . value)
;; where lo <= hi

(struct interval-tree (ft count) #:transparent)

;; Measure: (min-lo . max-hi)
(define interval-empty-measure (cons +inf.0 -inf.0))

;; Singleton config - avoid repeated allocation
(define interval-config
  (ft:config
    (lambda () interval-empty-measure)
    ;; measure of single interval
    (lambda (interval)
      (cons (car interval) (cadr interval)))  ; (lo . hi)
    ;; combine measures
    (lambda (m1 m2)
      (if (eq? m1 interval-empty-measure)
          m2
          (if (eq? m2 interval-empty-measure)
              m1
              (cons (min (car m1) (car m2))
                    (max (cdr m1) (cdr m2))))))))

;; ========================================
;; Basic Operations
;; ========================================

(define (interval-tree-empty)
  (interval-tree (ft:empty) 0))

(define (interval-tree-empty? it)
  (ft:empty? (interval-tree-ft it)))

(define (it-count it)
  (interval-tree-count it))

;; ========================================
;; Insert - O(log n)
;; ========================================

(define (interval-tree-insert it lo hi value)
  (match-define (interval-tree ft cnt) it)
  (define interval (list lo hi value))
  (cond
    [(ft:empty? ft)
     (interval-tree (ft:single interval) (add1 cnt))]
    [else
     (define measure (ft-measure ft))
     ;; Fast path: if all intervals have lo <= new lo, append to end
     (cond
       [(<= (car measure) lo)
        (interval-tree (consR:impl interval-config ft interval 0) (add1 cnt))]
       [else
        ;; Split at first interval with lo' > lo
        (define (pred acc-measure)
          (and (not (eq? acc-measure interval-empty-measure))
               (> (car acc-measure) lo)))
        (define-values (l elem r) (split:impl interval-config pred ft 0))
        (define new-ft
          (concat:impl interval-config
                       (consR:impl interval-config l interval 0)
                       (consL:impl interval-config r elem 0)
                       0))
        (interval-tree new-ft (add1 cnt))]
       ) ; cond: fast path / split path
     ]
    ) ; cond: empty tree
  ) ; define interval-tree-insert

(define (ft-measure ft)
  (match ft
    [(ft:empty) interval-empty-measure]
    [(ft:single a) ((ft:config-measure interval-config) a)]
    [(ft:deep v _ _ _) v]))

;; ========================================
;; Search - O(log n + k)
;; ========================================
;;
;; Find all intervals overlapping with query [qlo, qhi].
;; Overlap condition: interval.lo <= qhi AND interval.hi >= qlo
;;
;; Optimizations:
;; 1. Use cons to accumulate, reverse at end (O(k) instead of O(k²))
;; 2. Use digit-fold to avoid list allocation
;; 3. Prune by min-lo > qhi (ordered by lo, so can stop early)

(define (interval-tree-search it qlo qhi)
  (match-define (interval-tree ft _) it)
  (reverse (search-ft ft qlo qhi 0 '())))

;; Accumulator-based search (returns reversed result)
(define (search-ft ft qlo qhi depth acc)
  (match ft
    [(ft:empty) acc]
    [(ft:single elem)
     (if (= depth 0)
         (if (interval-overlaps? elem qlo qhi)
             (cons elem acc)
             acc)
         (search-node elem qlo qhi depth acc))]
    [(ft:deep (cons min-lo max-hi) left inner right)
     ;; Pruning
     (cond
       [(< max-hi qlo) acc]  ; no interval can overlap
       [(> min-lo qhi) acc]  ; all intervals start after query end
       [else
       (define acc1 (search-digit left qlo qhi depth acc))
       (define acc2 (search-ft inner qlo qhi (add1 depth) acc1))
        (search-digit right qlo qhi depth acc2)]
       ) ; cond: pruning
     ]
    ) ; match: ft
  ) ; define search-ft

(define (search-digit digit qlo qhi depth acc)
  (digit-fold-left digit acc
    (lambda (a elem)
      (if (= depth 0)
          (if (interval-overlaps? elem qlo qhi)
              (cons elem a)
              a)
          (search-node elem qlo qhi depth a)))))

(define (search-node node qlo qhi depth acc)
  (match node
    [(node:2 (cons min-lo max-hi) a b)
     (cond
       [(< max-hi qlo) acc]
       [(> min-lo qhi) acc]
       [else
        (define acc1 (search-child a qlo qhi depth acc))
        (search-child b qlo qhi depth acc1)]
       ) ; cond: node:2
     ]
    [(node:3 (cons min-lo max-hi) a b c)
     (cond
       [(< max-hi qlo) acc]
       [(> min-lo qhi) acc]
       [else
        (define acc1 (search-child a qlo qhi depth acc))
        (define acc2 (search-child b qlo qhi depth acc1))
        (search-child c qlo qhi depth acc2)]
       ) ; cond: node:3
     ]
    ) ; match: node
  ) ; define search-node

(define (search-child child qlo qhi depth acc)
  (if (= depth 1)
      ;; Child is an interval
      (if (interval-overlaps? child qlo qhi)
          (cons child acc)
          acc)
      ;; Child is a node
      (search-node child qlo qhi (sub1 depth) acc)))

(define (interval-overlaps? interval qlo qhi)
  (and (<= (car interval) qhi)
       (>= (cadr interval) qlo)))

;; ========================================
;; Delete - O(log n)
;; ========================================
;;
;; Strategy: Use split twice
;; 1. Split at first interval with lo > target-lo (gives us all intervals with lo <= target-lo)
;; 2. Split at first interval with lo >= target-lo (gives us all intervals with lo < target-lo)
;; 3. The middle part contains all intervals with lo = target-lo
;; 4. Linear search in middle part (usually small) for exact match

(define (interval-tree-delete it lo hi value)
  (match-define (interval-tree ft cnt) it)
  (cond
    [(ft:empty? ft) it]
    [else
     (define target (list lo hi value))
     (define new-ft (delete-by-double-split ft target))
     (if new-ft
         (interval-tree new-ft (sub1 cnt))
         it)]
    ) ; cond: empty tree
  ) ; define interval-tree-delete

(define (delete-by-double-split ft target)
  (define target-lo (car target))
  (define measure (ft-measure ft))

  (cond
    [(eq? measure interval-empty-measure) #f]
    [(< target-lo (car measure)) #f]  ; target-lo < min-lo, not in tree
    [else
     ;; Predicate 1: lo > target-lo
     (define (pred> acc)
       (and (not (eq? acc interval-empty-measure))
            (> (car acc) target-lo)))

     ;; Predicate 2: lo >= target-lo
     (define (pred>= acc)
       (and (not (eq? acc interval-empty-measure))
            (>= (car acc) target-lo)))

     ;; Check if there are any intervals with lo > target-lo
     (define has-greater (> (car measure) target-lo))

     (cond
       [(not has-greater)
        ;; All intervals have lo <= target-lo
        ;; Split at lo >= target-lo to get intervals with lo = target-lo at the end
        (if (>= (car measure) target-lo)
            ;; There exist intervals with lo >= target-lo
            (let-values ([(before first-ge after) (split:impl interval-config pred>= ft 0)])
              ;; first-ge has lo = target-lo, search from here
              (delete-in-suffix (consL:impl interval-config after first-ge 0) target before))
            #f)]
       [else
        ;; Split at lo > target-lo
        (define-values (le-part first-gt gt-part) (split:impl interval-config pred> ft 0))
        ;; le-part contains all intervals with lo <= target-lo
        ;; Now split le-part at lo >= target-lo
        (define le-measure (ft-measure le-part))
        (cond
          [(eq? le-measure interval-empty-measure)
           ;; No intervals with lo <= target-lo, check first-gt
           (if (equal? first-gt target)
               (concat:impl interval-config (ft:empty) gt-part 0)
               #f)]
          [(>= (car le-measure) target-lo)
           ;; There are intervals with lo >= target-lo in le-part
           (define-values (lt-part first-ge ge-part) (split:impl interval-config pred>= le-part 0))
           ;; first-ge and ge-part have lo = target-lo
           ;; Search for target
           (define suffix (consL:impl interval-config ge-part first-ge 0))
           (define new-suffix (delete-exact-from-list suffix target))
           (if new-suffix
               (concat:impl interval-config
                            lt-part
                            (concat:impl interval-config new-suffix
                                        (consL:impl interval-config gt-part first-gt 0) 0)
                            0)
               #f)]
          [else
           ;; All intervals in le-part have lo < target-lo, target not found
           #f]
          ) ; cond: split le-part
        ]
      ) ; cond: has-greater
    ]
   ) ; cond: empty / min-lo guards
  ) ; define delete-by-double-split

;; Delete exact target from a tree where all elements have the same lo
;; Returns new tree or #f if not found
(define (delete-exact-from-list ft target)
  (match ft
    [(ft:empty) #f]
    [(ft:single elem)
     (if (equal? elem target) (ft:empty) #f)]
    [(ft:deep _ _ _ _)
     ;; Pop from left, checking each element
     (define-values (first rest) (hdL:impl interval-config ft 0))
     (cond
       [(equal? first target) rest]
       [(not (= (car first) (car target))) #f]  ; different lo, stop
       [else
       (define new-rest (delete-exact-from-list rest target))
       (if new-rest
           (consL:impl interval-config new-rest first 0)
           #f)]
      ) ; cond: first element check
    ]
   ) ; match: ft
  ) ; define delete-exact-from-list

;; Delete target from suffix, prepend before-part
(define (delete-in-suffix suffix target before-part)
  (define new-suffix (delete-exact-from-list suffix target))
  (if new-suffix
      (concat:impl interval-config before-part new-suffix 0)
      #f))

;; ========================================
;; Point Query - O(log n + k)
;; ========================================

(define (interval-tree-search-point it point)
  (interval-tree-search it point point))

;; ========================================
;; Conversion
;; ========================================

(define (list->interval-tree lst)
  (for/fold ([it (interval-tree-empty)]) ([elem lst])
    (match elem
      [(list lo hi value)
       (interval-tree-insert it lo hi value)]
      [(cons (cons lo hi) value)
       (interval-tree-insert it lo hi value)])))

(define (interval-tree->list it)
  (match-define (interval-tree ft _) it)
  (reverse (ft->list-acc ft 0 '())))

(define (ft->list-acc ft depth acc)
  (match ft
    [(ft:empty) acc]
    [(ft:single elem)
     (if (= depth 0)
         (cons elem acc)
         (node->list-acc elem depth acc))]
    [(ft:deep _ left inner right)
     (define acc1 (digit->list-acc left depth acc))
     (define acc2 (ft->list-acc inner (add1 depth) acc1))
     (digit->list-acc right depth acc2)]
    ) ; match: ft
  ) ; define ft->list-acc

(define (digit->list-acc digit depth acc)
  (digit-fold-left digit acc
    (lambda (a elem)
      (if (= depth 0)
          (cons elem a)
          (node->list-acc elem depth a)))))

(define (node->list-acc node depth acc)
  (match node
    [(node:2 _ a b)
     (if (= depth 1)
         (cons b (cons a acc))
         (node->list-acc b (sub1 depth)
                         (node->list-acc a (sub1 depth) acc)))]
    [(node:3 _ a b c)
     (if (= depth 1)
         (cons c (cons b (cons a acc)))
         (node->list-acc c (sub1 depth)
                         (node->list-acc b (sub1 depth)
                                         (node->list-acc a (sub1 depth) acc))))]
    ) ; match: node
  ) ; define node->list-acc

;; ========================================
;; Exports
;; ========================================

(provide
  interval-tree
  interval-tree?
  interval-tree-empty
  interval-tree-empty?
  (rename-out [it-count interval-tree-count])
  interval-tree-insert
  interval-tree-search
  interval-tree-search-point
  interval-tree-delete
  list->interval-tree
  interval-tree->list)
