#lang info
(define collection "cutie-ftree")
(define deps '("base"))
(define build-deps '("scribble-lib" "racket-doc" "rackunit-lib"))
(define empty-flags '())
(define scribblings-entry
  (list "scribblings/cutie-ftree.scrbl" empty-flags))
(define scribblings
  (list scribblings-entry))
(define pkg-desc "Finger Tree based persistent data structures: pvector and ordered-map")
(define version "0.0")
(define pkg-authors '(cutiedeng))
(define license '(Apache-2.0 OR MIT))
