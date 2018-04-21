#lang racket/base

(provide reverse-postorder dominator-tree)
(require racket/set
         (only-in racket/list drop)
         (only-in racket/sequence sequence-fold))

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

;; Build the dominator tree for `rev-cont-calls` (a reverse continuation call graph) with `entries`
;; as the children of the imaginary root.
;; Use the reverse postorder `rpo` (presumably built with `reverse-postorder`).
;; Based on Cooper-Harvey-Kennedy: A Simple, Fast Dominance Algorithm.
(define (dominator-tree rev-cont-calls rpo entries)
  (define root-label #t)

  (define full-rpo (cons root-label rpo))

  ;; A hash from labels to their indices in `rpo`.
  (define label-rpo-indices (for/hash ([(label i) (in-indexed full-rpo)])
                              (values label i)))

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

  ;; Create initial dominator tree builder.
  (define (make-builder rev-cont-calls)
    (for/fold ([builder (hash root-label (list root-label))])
              ([(label _) rev-cont-calls])
      (hash-set builder label (if (memq label entries) (list root-label) #f))))

  ;; Build the dominator tree.
  (define (build builder)
    (define (children builder label)
      (filter (lambda (label*)
                ;; Is `label` the parent of `label*`?
                (eqv? (car (hash-ref builder label*)) label))
              ;; Nodes that came before `label` in the RPO cannot be its dom-tree children:
              (drop full-rpo (+ (hash-ref label-rpo-indices label) 1))))

    ;; 'Reverse the pointers' to obtain the dominator tree for `entry`:
    (let build-node ([label root-label])
      (cons label (map build-node (children builder label)))))

  ;; Did this iteration change the builder (or, did we not converge)?
  (define changed #t)

  ;; A single flow analysis iteration; update `builder` (functionally) and the `changed` flag
  ;; (imperatively).
  (define (update! builder)
    (set! changed #f)
    (for/hash ([label full-rpo])
      (values label
              (let ([doms (hash-ref builder label)])
                (if (or (eqv? label root-label) (memq label entries))
                  doms ; The top never changes.
                  (let* ([callers (hash-ref (hash-ref rev-cont-calls label) 'callers)]
                         [caller-domss (for/list ([caller callers])
                                         (cons caller (hash-ref builder caller)))]
                         [doms* (foldl (lambda (doms1 doms2)
                                         (if doms1
                                           (olset-intersect doms1 doms2)
                                           doms2))
                                       (car caller-domss) (cdr caller-domss))])
                    (unless (and doms (olset= doms* doms))
                      (set! changed #t))
                    doms*))))))

  ;; Iterate until `builder` converges, then build the dominator tree:
  (let iterate ([builder (make-builder rev-cont-calls)])
    (if changed
      (iterate (update! builder))
      (build builder))))
