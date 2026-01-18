#lang racket/base

(require rackunit)
(require racket/contract)
(require racket/string)
(require "../pvector/safe.rkt")
(require "../ordered-map/safe.rkt")
(require "../comparator.rkt")

;; ========================================
;; Contract Attachment Demonstration
;; ========================================

;; Case 1: Contract on module boundary (provide/contract)
;; - Contract is checked when value CROSSES the boundary
;; - After crossing, the value is "wrapped" or checked

;; Case 2: Contract on binding (define/contract)
;; - Contract is checked when value is ASSIGNED to the binding
;; - For functions: checked on EACH call

;; Case 3: Value wrapper (pvectorof/ordered-mapof)
;; - Contract TRAVELS with the value
;; - Checked on EVERY operation via *-functions

;; ========================================
;; Test: pvectorof contracts
;; ========================================

(test-case "pvectorof: first-order check"
  ;; First-order check happens immediately
  (check-true (contract-first-order-passes? (pvectorof integer?)
                (list->pvector '(1 2 3))))
  (check-false (contract-first-order-passes? (pvectorof integer?)
                 (list->pvector '(1 "two" 3))))
  (check-false (contract-first-order-passes? (pvectorof integer?)
                 "not a pvector")))

(test-case "pvectorof: boundary check"
  ;; Contract checked when crossing define/contract boundary
  (check-not-exn
    (lambda ()
      (contract (pvectorof integer?) (list->pvector '(1 2 3)) 'pos 'neg)))

  (check-exn exn:fail:contract?
    (lambda ()
      (contract (pvectorof integer?) (list->pvector '(1 "bad" 3)) 'pos 'neg))))

(test-case "pvectorof: wrapper preserves contract"
  (define/contract pv (pvectorof integer?)
    (list->pvector '(1 2 3)))

  ;; The wrapper type is created
  (check-true (contracted-pvector? pv))

  ;; Operations return wrapped values
  (define pv2 (pvector-cons-right* pv 4))
  (check-true (contracted-pvector? pv2))

  ;; Contract is still enforced on new value
  (check-exn exn:fail:contract?
    (lambda () (pvector-cons-right* pv2 "bad"))))

(test-case "pvectorof: input vs output blame"
  (define/contract pv (pvectorof integer?)
    (list->pvector '(1 2 3)))

  ;; Output check: ref returns checked value
  (check-equal? (pvector-ref* pv 0) 1)

  ;; Input check: cons-right checks the new element
  (check-exn exn:fail:contract?
    (lambda () (pvector-cons-right* pv "not-int")))

  ;; Input check: set checks the new value
  (check-exn exn:fail:contract?
    (lambda () (pvector-set* pv 0 "not-int")))

  ;; Input check: insert checks the new element
  (check-exn exn:fail:contract?
    (lambda () (pvector-insert* pv 0 "not-int"))))

(test-case "pvectorof: iteration with contract"
  (define/contract pv (pvectorof integer?)
    (list->pvector '(1 2 3)))

  ;; Iteration uses prop:sequence, elements are checked
  (check-equal? (for/list ([v pv]) v) '(1 2 3)))

(test-case "pvectorof: pop returns checked values"
  (define/contract pv (pvectorof integer?)
    (list->pvector '(1 2 3)))

  (define-values (elem rest) (pvector-pop-left* pv))
  (check-equal? elem 1)
  (check-true (contracted-pvector? rest)))

;; ========================================
;; Test: ordered-mapof contracts
;; ========================================

(test-case "ordered-mapof: first-order check"
  (define om (for/ordered-map integer-compare ([i 3]) (cons i (number->string i))))

  (check-true (contract-first-order-passes? (ordered-mapof integer? string?) om))
  (check-false (contract-first-order-passes? (ordered-mapof integer? integer?) om))
  (check-false (contract-first-order-passes? (ordered-mapof string? string?) om)))

(test-case "ordered-mapof: boundary check"
  (check-not-exn
    (lambda ()
      (contract (ordered-mapof integer? string?)
        (for/ordered-map integer-compare ([i 3]) (cons i (format "~a" i)))
        'pos 'neg)))

  (check-exn exn:fail:contract?
    (lambda ()
      (contract (ordered-mapof integer? string?)
        (for/ordered-map integer-compare ([i 3]) (cons i i)) ;; value is int, not string
        'pos 'neg))))

(test-case "ordered-mapof: wrapper preserves contract"
  (define/contract om (ordered-mapof integer? string?)
    (for/ordered-map integer-compare ([i 3]) (cons i (format "v~a" i))))

  (check-true (contracted-ordered-map? om))

  ;; Operations return wrapped values
  (define om2 (ordered-map-set* om 10 "ten"))
  (check-true (contracted-ordered-map? om2))

  ;; Contract still enforced
  (check-exn exn:fail:contract?
    (lambda () (ordered-map-set* om2 20 999)))) ;; value should be string

(test-case "ordered-mapof: key and value contracts"
  (define/contract om (ordered-mapof integer? string?)
    (ordered-map-empty integer-compare))

  ;; Valid key and value
  (check-not-exn (lambda () (ordered-map-set* om 1 "one")))

  ;; Invalid key type
  (check-exn exn:fail:contract?
    (lambda () (ordered-map-set* om "bad-key" "value")))

  ;; Invalid value type
  (check-exn exn:fail:contract?
    (lambda () (ordered-map-set* om 1 12345))))

(test-case "ordered-mapof: query returns checked values"
  (define/contract om (ordered-mapof integer? string?)
    (for/ordered-map integer-compare ([i 3]) (cons i (format "v~a" i))))

  ;; ref returns string (checked)
  (check-equal? (ordered-map-ref* om 1) "v1")

  ;; query returns pair with checked key and value
  (define result (ordered-map-query* om 1))
  (check-equal? result '(1 . "v1"))

  ;; min/max return checked pairs
  (check-equal? (ordered-map-min* om) '(0 . "v0"))
  (check-equal? (ordered-map-max* om) '(2 . "v2")))

(test-case "ordered-mapof: iteration with contract"
  (define/contract om (ordered-mapof integer? string?)
    (for/ordered-map integer-compare ([i 3]) (cons i (format "v~a" i))))

  ;; Iteration checks each key-value pair
  (check-equal?
    (for/list ([kv om]) kv)
    '((0 . "v0") (1 . "v1") (2 . "v2"))))

;; ========================================
;; Test: Contract behavior comparison
;; ========================================

(test-case "compare: unwrapped vs wrapped operations"
  ;; Without contract wrapper - no runtime checks
  (define pv-raw (list->pvector '(1 2 3)))
  (check-false (contracted-pvector? pv-raw))

  ;; With contract wrapper - runtime checks on *-operations
  (define/contract pv-wrapped (pvectorof integer?)
    (list->pvector '(1 2 3)))
  (check-true (contracted-pvector? pv-wrapped))

  ;; Raw pvector allows anything (no contract)
  (check-not-exn (lambda () (pvector-cons-right pv-raw "string")))

  ;; Wrapped pvector rejects non-integers
  (check-exn exn:fail:contract?
    (lambda () (pvector-cons-right* pv-wrapped "string"))))

(test-case "compare: contract location matters"
  ;; Contract on function parameter - checked on call
  (define/contract (process-ints pv)
    (-> (pvectorof integer?) integer?)
    ;; pv is now a contracted-pvector, iterate directly (uses prop:sequence)
    (for/fold ([sum 0]) ([v pv])
      (+ sum v)))

  ;; Valid call
  (check-equal? (process-ints (list->pvector '(1 2 3))) 6)

  ;; Invalid call - contract checked at call boundary
  (check-exn exn:fail:contract?
    (lambda () (process-ints (list->pvector '(1 "two" 3))))))

;; ========================================
;; Test: Nested contracts
;; ========================================

(test-case "nested: pvectorof with complex element contract"
  (define/contract pv (pvectorof (cons/c integer? string?))
    (list->pvector (list (cons 1 "a") (cons 2 "b"))))

  (check-true (contracted-pvector? pv))
  (check-equal? (pvector-ref* pv 0) '(1 . "a"))

  ;; Must add valid pair
  (check-not-exn
    (lambda () (pvector-cons-right* pv (cons 3 "c"))))

  ;; Invalid pair rejected
  (check-exn exn:fail:contract?
    (lambda () (pvector-cons-right* pv (cons "bad" "c")))))

;; ========================================
;; Summary output
;; ========================================

;; ========================================
;; Test: Ordinal Query API with Contracts
;; ========================================

(test-case "ordered-mapof: rank with contract (positive)"
  ;; 正例：rank 查询返回正确的排名
  (define/contract om (ordered-mapof integer? string?)
    (for/ordered-map integer-compare ([i 5]) (cons (* i 10) (format "v~a" i))))
  ;; om contains: {0->"v0", 10->"v1", 20->"v2", 30->"v3", 40->"v4"}

  (check-equal? (ordered-map-rank* om 0) 0)   ; 第 0 小
  (check-equal? (ordered-map-rank* om 20) 2)  ; 第 2 小
  (check-equal? (ordered-map-rank* om 40) 4)  ; 第 4 小
  (check-equal? (ordered-map-rank* om 15) #f)) ; 不存在

(test-case "ordered-mapof: rank with invalid key type (negative)"
  ;; 反例：用错误类型的 key 查询 rank 应该触发 contract 错误
  (define/contract om (ordered-mapof integer? string?)
    (for/ordered-map integer-compare ([i 3]) (cons i (format "v~a" i))))

  ;; 用字符串查询整数键的 map - 应该被 contract 拒绝
  (check-exn exn:fail:contract?
    (lambda () (ordered-map-rank* om "not-an-integer"))))

(test-case "ordered-mapof: select with contract (positive)"
  ;; 正例：select 按排名查询返回正确的键值对
  (define/contract om (ordered-mapof integer? string?)
    (for/ordered-map integer-compare ([i 5]) (cons (* i 10) (format "v~a" i))))

  (check-equal? (ordered-map-select* om 0) '(0 . "v0"))
  (check-equal? (ordered-map-select* om 2) '(20 . "v2"))
  (check-equal? (ordered-map-select* om 4) '(40 . "v4"))
  (check-equal? (ordered-map-select* om 5) #f)   ; 越界
  (check-equal? (ordered-map-select* om -1) #f)) ; 负数

(test-case "ordered-mapof: count-less-than with contract (positive)"
  ;; 正例：count-less-than 返回小于给定 key 的元素数量
  (define/contract om (ordered-mapof integer? string?)
    (for/ordered-map integer-compare ([i 5]) (cons (* i 10) (format "v~a" i))))
  ;; om contains: {0, 10, 20, 30, 40}

  (check-equal? (ordered-map-count-less-than* om 0) 0)   ; 没有比 0 小的
  (check-equal? (ordered-map-count-less-than* om 15) 2)  ; 0, 10 比 15 小
  (check-equal? (ordered-map-count-less-than* om 40) 4)  ; 0, 10, 20, 30 比 40 小
  (check-equal? (ordered-map-count-less-than* om 100) 5)) ; 所有 5 个都比 100 小

(test-case "ordered-mapof: count-less-than with invalid key type (negative)"
  ;; 反例：用错误类型的 key 应该触发 contract 错误
  (define/contract om (ordered-mapof integer? string?)
    (for/ordered-map integer-compare ([i 3]) (cons i "v")))

  (check-exn exn:fail:contract?
    (lambda () (ordered-map-count-less-than* om "bad-key"))))

;; ========================================
;; Test: Contract Error Messages (Blame)
;; ========================================

(test-case "blame: positive position (provider violated)"
  ;; 当提供者违反 contract 时，blame 指向 positive position
  ;; 场景：define/contract 时提供了不符合 contract 的值
  (check-exn
    (lambda (e)
      (and (exn:fail:contract:blame? e)
           ;; 错误消息应该包含违规位置信息
           (regexp-match? #rx"element" (exn-message e))))
    (lambda ()
      ;; 提供包含字符串的 pvector 给 (pvectorof integer?) contract
      (define/contract pv (pvectorof integer?)
        (list->pvector '(1 "bad" 3)))
      pv)))

(test-case "blame: negative position (consumer violated)"
  ;; 当消费者违反 contract 时，blame 指向 negative position
  ;; 场景：调用 *-operation 时传入不符合 contract 的参数
  (define/contract pv (pvectorof integer?)
    (list->pvector '(1 2 3)))

  (check-exn
    (lambda (e)
      (and (exn:fail:contract:blame? e)
           (regexp-match? #rx"element" (exn-message e))))
    (lambda ()
      ;; 消费者尝试插入字符串到整数 pvector
      (pvector-cons-right* pv "consumer-violation"))))

(test-case "blame: ordered-map key vs value distinction"
  ;; 验证 ordered-map 的 blame 能区分 key 和 value 违规
  (define/contract om (ordered-mapof symbol? integer?)
    (ordered-map-empty symbol-compare))

  ;; key 违规 - 错误消息应包含 "key"
  (check-exn
    (lambda (e)
      (and (exn:fail:contract:blame? e)
           (regexp-match? #rx"key" (exn-message e))))
    (lambda ()
      (ordered-map-set* om 123 456))) ; 123 不是 symbol

  ;; value 违规 - 错误消息应包含 "value"
  (check-exn
    (lambda (e)
      (and (exn:fail:contract:blame? e)
           (regexp-match? #rx"value" (exn-message e))))
    (lambda ()
      (ordered-map-set* om 'key "not-an-integer")))) ; "not-an-integer" 不是 integer

;; ========================================
;; Test: Edge Cases and Boundary Conditions
;; ========================================

(test-case "edge: empty containers with contracts"
  ;; 空容器应该通过任何元素类型的 contract
  (define/contract empty-pv (pvectorof (-> integer? integer?))
    (pvector-empty))
  (check-true (pvector-empty?* empty-pv))
  (check-equal? (pvector-length* empty-pv) 0)

  (define/contract empty-om (ordered-mapof string? (listof integer?))
    (ordered-map-empty string-compare))
  (check-true (ordered-map-empty?* empty-om))
  (check-equal? (ordered-map-count* empty-om) 0))

(test-case "edge: single element containers"
  ;; 单元素容器的 contract 检查
  (define/contract single-pv (pvectorof positive?)
    (list->pvector '(42)))
  (check-equal? (pvector-ref* single-pv 0) 42)
  (check-equal? (pvector-length* single-pv) 1)

  ;; 尝试添加非正数应该失败
  (check-exn exn:fail:contract?
    (lambda () (pvector-cons-right* single-pv 0)))
  (check-exn exn:fail:contract?
    (lambda () (pvector-cons-right* single-pv -5))))

(test-case "edge: contract with any/c"
  ;; any/c 允许任何值
  (define/contract pv (pvectorof any/c)
    (list->pvector '(1 "two" #t (a b c))))

  (check-equal? (pvector-ref* pv 0) 1)
  (check-equal? (pvector-ref* pv 1) "two")
  (check-equal? (pvector-ref* pv 2) #t)
  (check-equal? (pvector-ref* pv 3) '(a b c))

  ;; 可以添加任何类型的值
  (check-not-exn (lambda () (pvector-cons-right* pv 'symbol)))
  (check-not-exn (lambda () (pvector-cons-right* pv #\c)))
  (check-not-exn (lambda () (pvector-cons-right* pv (lambda (x) x)))))

(test-case "edge: contract with or/c"
  ;; or/c 允许多种类型
  (define/contract pv (pvectorof (or/c integer? string? symbol?))
    (list->pvector '(1 "two" three)))

  (check-equal? (for/list ([v pv]) v) '(1 "two" three))

  ;; 可以添加任意一种允许的类型
  (check-not-exn (lambda () (pvector-cons-right* pv 42)))
  (check-not-exn (lambda () (pvector-cons-right* pv "hello")))
  (check-not-exn (lambda () (pvector-cons-right* pv 'world)))

  ;; 不允许的类型被拒绝
  (check-exn exn:fail:contract?
    (lambda () (pvector-cons-right* pv 3.14)))  ; not integer/string/symbol
  (check-exn exn:fail:contract?
    (lambda () (pvector-cons-right* pv #t))))   ; not integer/string/symbol

;; ========================================
;; Test: Contract Propagation
;; ========================================

(test-case "propagation: operations preserve contract"
  ;; 验证各种操作后 contract 仍然有效
  (define/contract pv0 (pvectorof integer?)
    (list->pvector '(1 2 3)))

  ;; cons-right 返回的值仍有 contract
  (define pv1 (pvector-cons-right* pv0 4))
  (check-true (contracted-pvector? pv1))
  (check-exn exn:fail:contract? (lambda () (pvector-cons-right* pv1 "bad")))

  ;; cons-left 返回的值仍有 contract
  (define pv2 (pvector-cons-left* pv1 0))
  (check-true (contracted-pvector? pv2))
  (check-exn exn:fail:contract? (lambda () (pvector-cons-left* pv2 "bad")))

  ;; set 返回的值仍有 contract
  (define pv3 (pvector-set* pv2 0 100))
  (check-true (contracted-pvector? pv3))
  (check-exn exn:fail:contract? (lambda () (pvector-set* pv3 0 "bad")))

  ;; pop 返回的 rest 仍有 contract
  (define-values (elem pv4) (pvector-pop-left* pv3))
  (check-true (contracted-pvector? pv4))
  (check-exn exn:fail:contract? (lambda () (pvector-cons-right* pv4 "bad"))))

(test-case "propagation: ordered-map operations preserve contract"
  (define/contract om0 (ordered-mapof integer? string?)
    (ordered-map-empty integer-compare))

  ;; set 返回的值仍有 contract
  (define om1 (ordered-map-set* om0 1 "one"))
  (check-true (contracted-ordered-map? om1))
  (check-exn exn:fail:contract? (lambda () (ordered-map-set* om1 2 999)))

  ;; insert 返回的值仍有 contract
  (define om2 (ordered-map-insert* om1 2 "two" #t))
  (check-true (contracted-ordered-map? om2))
  (check-exn exn:fail:contract? (lambda () (ordered-map-insert* om2 "bad" "val" #t)))

  ;; delete 返回的值仍有 contract
  (define-values (om3 deleted) (ordered-map-delete* om2 1))
  (check-true (contracted-ordered-map? om3))
  (check-exn exn:fail:contract? (lambda () (ordered-map-set* om3 3 #f))))

;; ========================================
;; Test: Real-world Usage Patterns
;; ========================================

(test-case "usage: type-safe configuration map"
  ;; 场景：配置项必须是 symbol -> string 的映射
  (define/contract config (ordered-mapof symbol? string?)
    (ordered-map-empty symbol-compare))

  (define config2
    (ordered-map-set*
      (ordered-map-set*
        (ordered-map-set* config 'host "localhost")
        'port "8080")
      'debug "true"))

  (check-equal? (ordered-map-ref* config2 'host) "localhost")
  (check-equal? (ordered-map-ref* config2 'port) "8080")
  (check-equal? (ordered-map-count* config2) 3)

  ;; 防止意外用数字作为 value
  (check-exn exn:fail:contract?
    (lambda () (ordered-map-set* config2 'timeout 30))))

(test-case "usage: type-safe priority queue elements"
  ;; 场景：优先队列元素必须是 (priority . task-name) 的格式
  (define/contract tasks (pvectorof (cons/c integer? string?))
    (list->pvector (list (cons 1 "urgent") (cons 5 "low") (cons 3 "normal"))))

  ;; 添加新任务
  (define tasks2 (pvector-cons-right* tasks (cons 2 "important")))
  (check-equal? (pvector-length* tasks2) 4)

  ;; 防止格式错误的任务
  (check-exn exn:fail:contract?
    (lambda () (pvector-cons-right* tasks2 "just a string")))
  (check-exn exn:fail:contract?
    (lambda () (pvector-cons-right* tasks2 (cons "not-priority" "task")))))

(test-case "usage: contract as documentation"
  ;; Contract 作为活文档，表明函数期望和保证

  ;; 这个函数期望一个整数 pvector，返回它们的和
  (define/contract (sum-integers pv)
    (-> (pvectorof integer?) integer?)
    (for/fold ([sum 0]) ([v pv]) (+ sum v)))

  ;; 正确使用
  (check-equal? (sum-integers (list->pvector '(1 2 3 4 5))) 15)

  ;; 错误使用 - contract 提供清晰的错误信息
  (check-exn exn:fail:contract?
    (lambda () (sum-integers (list->pvector '(1 2 "three")))))

  ;; 这个函数期望一个 integer->string 的 ordered-map
  (define/contract (format-map om)
    (-> (ordered-mapof integer? string?) string?)
    (string-join
      (for/list ([kv om])
        (format "~a: ~a" (car kv) (cdr kv)))
      ", "))

  (define test-map
    (for/ordered-map integer-compare ([i 3]) (cons i (format "item~a" i))))
  (check-equal? (format-map test-map) "0: item0, 1: item1, 2: item2"))

;; ========================================
;; Summary output
;; ========================================

(displayln "")
(displayln "Contract System Summary:")
(displayln "========================")
(displayln "")
(displayln "1. pvectorof / ordered-mapof create WRAPPER structures")
(displayln "   - contracted-pvector? / contracted-ordered-map? check wrapper type")
(displayln "")
(displayln "2. Contracts are checked at:")
(displayln "   - Boundary crossing (define/contract, provide/contract)")
(displayln "   - Every *-operation (pvector-ref*, ordered-map-set*, etc.)")
(displayln "   - Iteration (for loops over wrapped values)")
(displayln "")
(displayln "3. Use *-suffixed operations to maintain contract enforcement:")
(displayln "   - pvector-ref* instead of pvector-ref")
(displayln "   - ordered-map-set* instead of ordered-map-set")
(displayln "")
(displayln "4. Ordinal query APIs with contracts:")
(displayln "   - ordered-map-rank* : key -> (or/c integer? #f)")
(displayln "   - ordered-map-select* : rank -> (or/c pair? #f)")
(displayln "   - ordered-map-count-less-than* : key -> integer?")
(displayln "")
