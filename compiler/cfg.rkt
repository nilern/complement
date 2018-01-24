#lang racket/base

(provide reverse-postorder dominator-forest)
(require racket/set (only-in racket/list drop) (only-in racket/sequence sequence-fold))

;; FIXME: ATM need to have entries and callees in reverse to get exectly the desired order
;;        for e.g. fallthrough.
;;
;; Return a list of the labels in `cont-calls` (a continuation call graph) corresponding to
;; a reverse postorder traversal starting at `entries`.
(define (reverse-postorder cont-calls entries)
  (define visited (mutable-set))

  ;; The usual recursive postorder walk:
  (define (visit! rpo label)
    (if (set-member? visited label)
      rpo
      (begin
        (set-add! visited label)
        (let ([succs (hash-ref (hash-ref cont-calls label) 'callees)])
          (cons label (sequence-fold visit! rpo succs))))))
  (sequence-fold visit! '() entries))

;; TODO: Avoid the forest complexity by computing instead the dominator tree with respect to a
;;       singular virtual root, the imaginary parent of all the `entries`.
;; OPTIMIZE: use worklist algorithm or at least make sure that DAG:s only take the minimum 2 passes
;;
;; Build the dominator forest for `rev-cont-calls` (a reverse continuation call graph) with
;; `entries` as the roots. Use the reverse postorder `rpo` (presumably build with
;; `reverse-postorder`). Based on Cooper-Harvey-Kennedy: A Simple, Fast Dominance Algorithm.
(define (dominator-forest rev-cont-calls rpo entries)
  ;; A hash from labels to their indices in `rpo`.
  (define label-rpo-indices (for/hash ([(label i) (in-indexed rpo)])
                              (values label i)))
  ;; Did this iteration change the builder (or, did we not converge)?
  (define changed #t)

  ;;; Dominators of a node are represented as bottom-up lists:

  ;; Are two dominator sets the same?
  (define (olset= set1 set2)
    (eq? (car set1) (car set2)))

  ;; Set intersection of two dominator sets.
  (define (olset-intersect doms1 doms2)
    (let ([idom1-idx (hash-ref label-rpo-indices (car doms1))]
          [idom2-idx (hash-ref label-rpo-indices (car doms2))])
      (cond
        [(< idom1-idx idom2-idx) (olset-intersect (cdr doms1) doms2)]
        [(> idom1-idx idom2-idx) (olset-intersect doms1 (cdr doms2))]
        [else doms1])))

  ;; Elementwise intersection of a sequence of hashes from entry labels to dominator sets.
  (define (intersect* dom-chain-hashes)
    (for/fold ([dom-chain-hashes-acc (hash)])
              ([entry entries])
      (define dom-chain
        (for/fold ([dom-chain-acc #f])
                  ([dom-chain-hash dom-chain-hashes]
                   #:when (hash-has-key? dom-chain-hash entry))
          (let ([dom-chain (hash-ref dom-chain-hash entry)])
            (if dom-chain-acc
              (olset-intersect dom-chain-acc dom-chain)
              dom-chain))))
      (if dom-chain
        (hash-set dom-chain-hashes-acc entry dom-chain)
        dom-chain-hashes-acc)))

  ;; Create initial dominator forest builder.
  (define (init rev-cont-calls)
    (for/hash ([(label _) rev-cont-calls])
      (values label
              (if (member label entries)
                (hash label (list label))
                (hash)))))

  ;; A single flow analysis iteration; update `builder` (functionally) and the `changed` flag
  ;; (imperatively).
  (define (update! builder)
    (set! changed #f)
    (for/hash ([label rpo])
      (values label
              (if (member label entries)
                (hash-ref builder label) ; The dominator set of roots never changes.
                (let ([dom-chain-hash (hash-ref builder label)]
                      [dom-chain-hash*
                       (intersect*
                         (for/list ([label (hash-ref (hash-ref rev-cont-calls label) 'callers)])
                           (hash-ref builder label)))])
                  ;; changed := dom-chain-hash* = dom-chain-hash:
                  (for ([(entry dom-chain*) dom-chain-hash*])
                    (unless (and (hash-has-key? dom-chain-hash entry)
                                 (olset= dom-chain* (hash-ref dom-chain-hash entry)))
                      (set! changed #t)))
                  dom-chain-hash*)))))

  ;; A list of the children of `label` in the dominator tree for `entry` in the forest
  ;; that will be built with `builder`.
  (define (children builder entry label)
    (filter (λ (label*)
              ;; Is `label` the parent of `label*`?
              (define dom-chain-hash (hash-ref builder label*))
              (and (hash-has-key? dom-chain-hash entry)
                   (eq? (car (hash-ref dom-chain-hash entry))
                        label)))
            ;; Nodes that came before `label` in the RPO cannot be its dom-tree children:
            (drop rpo (+ (hash-ref label-rpo-indices label) 1))))

  ;; Build the dominator forest.
  (define (build builder)
    (for/hash ([entry entries])
      (values entry
              ;; 'Reverse the pointers' to obtain the dominator tree for `entry`:
              (let build-node ([label entry])
                (cons label (map build-node (children builder entry label)))))))

  ;; Iterate until `builder` converges, then build the dominator forest:
  (let iterate ([builder (init rev-cont-calls)])
    (if changed
      (iterate (update! builder))
      (build builder))))
