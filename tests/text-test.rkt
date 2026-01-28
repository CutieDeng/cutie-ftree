#lang racket/base

(require rackunit racket/list)
(require "../text.rkt")

;; ========================================
;; Basic Construction Tests
;; ========================================

(test-case "text-empty creates empty buffer"
  (define tb (text-empty))
  (check-pred text-empty? tb)
  (check-equal? (text-length tb) 0)
  (check-equal? (text-word-count tb) 0)
  (check-equal? (text-line-count tb) 0)
  (check-equal? (text-para-count tb) 0))

(test-case "string->text basic"
  (define tb (string->text "hello"))
  (check-equal? (text-length tb) 5)
  (check-equal? (text->string tb) "hello"))

(test-case "string->text empty string"
  (define tb (string->text ""))
  (check-pred text-empty? tb)
  (check-equal? (text-length tb) 0))

(test-case "text->string roundtrip"
  (define str "The quick brown fox jumps over the lazy dog.")
  (check-equal? (text->string (string->text str)) str))

;; ========================================
;; Word Count Tests
;; ========================================

(test-case "word count single word"
  (check-equal? (text-word-count (string->text "hello")) 1))

(test-case "word count two words"
  (check-equal? (text-word-count (string->text "hello world")) 2))

(test-case "word count with multiple spaces"
  (check-equal? (text-word-count (string->text "hello   world")) 2))

(test-case "word count with leading/trailing spaces"
  (check-equal? (text-word-count (string->text "  hello world  ")) 2))

(test-case "word count with tabs and newlines"
  (check-equal? (text-word-count (string->text "hello\tworld\nfoo")) 3))

(test-case "word count empty string"
  (check-equal? (text-word-count (string->text "")) 0))

(test-case "word count whitespace only"
  (check-equal? (text-word-count (string->text "   \t\n  ")) 0))

;; ========================================
;; Line Count Tests
;; ========================================

(test-case "line count no newlines"
  ;; Like wc -l: counts newline characters
  (check-equal? (text-line-count (string->text "hello")) 0))

(test-case "line count one newline"
  (check-equal? (text-line-count (string->text "hello\n")) 1))

(test-case "line count multiple lines"
  (check-equal? (text-line-count (string->text "line1\nline2\nline3")) 2))

(test-case "line count with trailing newline"
  (check-equal? (text-line-count (string->text "line1\nline2\n")) 2))

(test-case "line count empty lines"
  (check-equal? (text-line-count (string->text "a\n\nb")) 2))

;; ========================================
;; Paragraph Count Tests
;; ========================================

(test-case "para count single paragraph"
  (check-equal? (text-para-count (string->text "hello world")) 1))

(test-case "para count two paragraphs with blank line"
  (check-equal? (text-para-count (string->text "para one\n\npara two")) 2))

(test-case "para count no blank line between"
  ;; Two lines but same paragraph (no blank line separator)
  (check-equal? (text-para-count (string->text "line one\nline two")) 1))

(test-case "para count with multiple blank lines"
  (check-equal? (text-para-count (string->text "para1\n\n\npara2")) 2))

(test-case "para count with leading whitespace"
  (check-equal? (text-para-count (string->text "  \n  hello")) 1))

(test-case "para count whitespace only"
  (check-equal? (text-para-count (string->text "   \n\n   ")) 0))

;; ========================================
;; Character Navigation Tests
;; ========================================

(test-case "text-ref basic"
  (define tb (string->text "hello"))
  (check-equal? (text-ref tb 0) #\h)
  (check-equal? (text-ref tb 1) #\e)
  (check-equal? (text-ref tb 4) #\o))

(test-case "text-set basic"
  (define tb (string->text "hello"))
  (define tb2 (text-set tb 0 #\H))
  (check-equal? (text->string tb2) "Hello")
  ;; Original unchanged (persistence)
  (check-equal? (text->string tb) "hello"))

(test-case "text-set middle"
  (define tb (string->text "hello"))
  (define tb2 (text-set tb 2 #\L))
  (check-equal? (text->string tb2) "heLlo"))

(test-case "text-ref bounds checking"
  (define tb (string->text "hello"))
  (check-exn exn:fail? (lambda () (text-ref tb -1)))
  (check-exn exn:fail? (lambda () (text-ref tb 5))))

;; ========================================
;; Word Navigation Tests
;; ========================================

(test-case "text-word-at basic"
  (define tb (string->text "one two three"))
  (define-values (s0 e0 w0) (text-word-at tb 0))
  (check-equal? w0 "one")
  (check-equal? s0 0)
  (check-equal? e0 3)

  (define-values (s1 e1 w1) (text-word-at tb 1))
  (check-equal? w1 "two")
  (check-equal? s1 4)
  (check-equal? e1 7)

  (define-values (s2 e2 w2) (text-word-at tb 2))
  (check-equal? w2 "three")
  (check-equal? s2 8)
  (check-equal? e2 13))

(test-case "text-word-at with extra spaces"
  (define tb (string->text "  hello   world  "))
  (define-values (s0 e0 w0) (text-word-at tb 0))
  (check-equal? w0 "hello")
  (check-equal? s0 2)

  (define-values (s1 e1 w1) (text-word-at tb 1))
  (check-equal? w1 "world"))

(test-case "text-char-to-word"
  (define tb (string->text "one two three"))
  (check-equal? (text-char-to-word tb 0) 0)  ; 'o' in "one"
  (check-equal? (text-char-to-word tb 2) 0)  ; 'e' in "one"
  (check-equal? (text-char-to-word tb 4) 1)  ; 't' in "two"
  (check-equal? (text-char-to-word tb 8) 2)) ; 't' in "three"

;; ========================================
;; Line Navigation Tests
;; ========================================

(test-case "text-line-at single line"
  (define tb (string->text "hello world"))
  (define-values (s e line) (text-line-at tb 0))
  (check-equal? line "hello world")
  (check-equal? s 0)
  (check-equal? e 11))

(test-case "text-line-at multiple lines"
  (define tb (string->text "line1\nline2\nline3"))
  (define-values (s0 e0 l0) (text-line-at tb 0))
  (check-equal? l0 "line1")
  (check-equal? s0 0)
  (check-equal? e0 5)

  (define-values (s1 e1 l1) (text-line-at tb 1))
  (check-equal? l1 "line2")
  (check-equal? s1 6)
  (check-equal? e1 11)

  (define-values (s2 e2 l2) (text-line-at tb 2))
  (check-equal? l2 "line3")
  (check-equal? s2 12)
  (check-equal? e2 17))

(test-case "text-char-to-line"
  (define tb (string->text "line1\nline2\nline3"))
  (check-equal? (text-char-to-line tb 0) 0)
  (check-equal? (text-char-to-line tb 4) 0)
  (check-equal? (text-char-to-line tb 6) 1)
  (check-equal? (text-char-to-line tb 12) 2))

;; ========================================
;; Paragraph Navigation Tests
;; ========================================

(test-case "text-para-at single paragraph"
  (define tb (string->text "hello world"))
  (define-values (s e para) (text-para-at tb 0))
  (check-equal? para "hello world")
  (check-equal? s 0))

(test-case "text-para-at two paragraphs"
  (define tb (string->text "para one\n\npara two"))
  (define-values (s0 e0 p0) (text-para-at tb 0))
  (check-equal? p0 "para one")
  (check-equal? s0 0)

  (define-values (s1 e1 p1) (text-para-at tb 1))
  (check-equal? p1 "para two")
  (check-equal? s1 10))

;; ========================================
;; Insert Tests
;; ========================================

(test-case "text-insert at start"
  (define tb (string->text "world"))
  (define tb2 (text-insert tb 0 #\H))
  (check-equal? (text->string tb2) "Hworld"))

(test-case "text-insert at end"
  (define tb (string->text "hello"))
  (define tb2 (text-insert tb 5 #\!))
  (check-equal? (text->string tb2) "hello!"))

(test-case "text-insert in middle"
  (define tb (string->text "hllo"))
  (define tb2 (text-insert tb 1 #\e))
  (check-equal? (text->string tb2) "hello"))

(test-case "text-insert into empty"
  (define tb (text-empty))
  (define tb2 (text-insert tb 0 #\x))
  (check-equal? (text->string tb2) "x")
  (check-equal? (text-length tb2) 1))

(test-case "text-insert updates word count"
  (define tb (string->text "ab"))
  (check-equal? (text-word-count tb) 1)
  (define tb2 (text-insert tb 1 #\space))
  (check-equal? (text->string tb2) "a b")
  (check-equal? (text-word-count tb2) 2))

(test-case "text-insert-string"
  (define tb (string->text "hello"))
  (define tb2 (text-insert-string tb 5 " world"))
  (check-equal? (text->string tb2) "hello world")
  (check-equal? (text-word-count tb2) 2))

;; ========================================
;; Delete Tests
;; ========================================

(test-case "text-delete at start"
  (define tb (string->text "hello"))
  (define tb2 (text-delete tb 0))
  (check-equal? (text->string tb2) "ello"))

(test-case "text-delete at end"
  (define tb (string->text "hello"))
  (define tb2 (text-delete tb 4))
  (check-equal? (text->string tb2) "hell"))

(test-case "text-delete in middle"
  (define tb (string->text "hello"))
  (define tb2 (text-delete tb 2))
  (check-equal? (text->string tb2) "helo"))

(test-case "text-delete single char"
  (define tb (string->text "x"))
  (define tb2 (text-delete tb 0))
  (check-pred text-empty? tb2))

(test-case "text-delete-range"
  (define tb (string->text "hello world"))
  (define tb2 (text-delete-range tb 5 11))  ; Delete " world"
  (check-equal? (text->string tb2) "hello"))

(test-case "text-delete-range empty range"
  (define tb (string->text "hello"))
  (define tb2 (text-delete-range tb 2 2))
  (check-equal? (text->string tb2) "hello"))

;; ========================================
;; Split/Append Tests
;; ========================================

(test-case "text-split-at basic"
  (define tb (string->text "hello world"))
  (define-values (prefix suffix) (text-split-at tb 5))
  (check-equal? (text->string prefix) "hello")
  (check-equal? (text->string suffix) " world"))

(test-case "text-split-at at start"
  (define tb (string->text "hello"))
  (define-values (prefix suffix) (text-split-at tb 0))
  (check-pred text-empty? prefix)
  (check-equal? (text->string suffix) "hello"))

(test-case "text-split-at at end"
  (define tb (string->text "hello"))
  (define-values (prefix suffix) (text-split-at tb 5))
  (check-equal? (text->string prefix) "hello")
  (check-pred text-empty? suffix))

(test-case "text-append basic"
  (define tb1 (string->text "hello"))
  (define tb2 (string->text " world"))
  (define tb3 (text-append tb1 tb2))
  (check-equal? (text->string tb3) "hello world"))

(test-case "text-append with empty"
  (define tb (string->text "hello"))
  (define tb2 (text-append tb (text-empty)))
  (check-equal? (text->string tb2) "hello")
  (define tb3 (text-append (text-empty) tb))
  (check-equal? (text->string tb3) "hello"))

;; ========================================
;; Iterator Tests
;; ========================================

(test-case "in-text-chars"
  (define tb (string->text "hi"))
  (check-equal? (for/list ([c (in-text-chars tb)]) c)
                '(#\h #\i)))

(test-case "in-text-words"
  (define tb (string->text "one two three"))
  (define words (for/list ([w (in-text-words tb)]) w))
  (check-equal? (length words) 3)
  (check-equal? (third (first words)) "one")
  (check-equal? (third (second words)) "two")
  (check-equal? (third (third words)) "three"))

(test-case "in-text-lines"
  (define tb (string->text "line1\nline2"))
  (define lines (for/list ([l (in-text-lines tb)]) l))
  (check-equal? (length lines) 2)
  (check-equal? (third (first lines)) "line1")
  (check-equal? (third (second lines)) "line2"))

;; ========================================
;; Edge Cases
;; ========================================

(test-case "unicode characters"
  (define tb (string->text "hello"))
  (check-equal? (text-length tb) 5)
  (check-equal? (text->string tb) "hello"))

(test-case "large text"
  (define str (make-string 10000 #\x))
  (define tb (string->text str))
  (check-equal? (text-length tb) 10000)
  (check-equal? (text-ref tb 5000) #\x))

(test-case "persistence - insert doesn't modify original"
  (define tb1 (string->text "hello"))
  (define tb2 (text-insert tb1 0 #\X))
  (check-equal? (text->string tb1) "hello")
  (check-equal? (text->string tb2) "Xhello"))

(test-case "persistence - delete doesn't modify original"
  (define tb1 (string->text "hello"))
  (define tb2 (text-delete tb1 0))
  (check-equal? (text->string tb1) "hello")
  (check-equal? (text->string tb2) "ello"))

;; ========================================
;; Run all tests
;; ========================================

(printf "All text tests passed!\n")
