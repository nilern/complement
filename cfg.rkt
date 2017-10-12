#lang racket/base

(provide reverse-postorder dominator-forest)
(require racket/set (only-in racket/list drop))

(define (reverse-postorder cont-calls entries)
  (define visited (mutable-set))
  (define rpo '())
  (define (visit! label)
    (unless (set-member? visited label)
      (set-add! visited label)
      (for ([succ (hash-ref (hash-ref cont-calls label) 'callees)])
        (visit! succ))
      (set! rpo (cons label rpo))))
  (for ([entry entries])
    (visit! entry))
  rpo)

;; OPTIMIZE: use worklist algorithm or at least make sure that DAG:s only take the minimum 2 passes
(define (dominator-forest rev-cont-calls rpo entries)
  (define label-rpo-indices (for/hash ([(label i) (in-indexed rpo)])
                              (values label i)))
  (define changed #t)

  (define (olset= set1 set2)
    (eq? (car set1) (car set2)))

  (define (olset-intersect doms1 doms2)
    (let ([idom1-idx (hash-ref label-rpo-indices (car doms1))]
          [idom2-idx (hash-ref label-rpo-indices (car doms2))])
      (cond
        [(< idom1-idx idom2-idx) (olset-intersect (cdr doms1) doms2)]
        [(> idom1-idx idom2-idx) (olset-intersect doms1 (cdr doms2))]
        [else doms1])))

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

  (define (init rev-cont-calls)
    (for/hash ([(label _) rev-cont-calls])
      (values label
              (if (member label entries)
                (hash label (list label))
                (hash)))))

  (define (update! builder)
    (set! changed #f)
    (for/hash ([label rpo])
      (values label
              (if (member label entries)
                (hash-ref builder label)
                (let ([dom-chain-hash (hash-ref builder label)]
                      [dom-chain-hash*
                       (intersect*
                         (for/list ([label (hash-ref (hash-ref rev-cont-calls label) 'callers)])
                           (hash-ref builder label)))])
                  (for ([(entry dom-chain*) dom-chain-hash*])
                    (unless (and (hash-has-key? dom-chain-hash entry)
                                 (olset= dom-chain* (hash-ref dom-chain-hash entry)))
                      (set! changed #t)))
                  dom-chain-hash*)))))

  (define (children builder entry label)
    (filter (λ (label*)
              (define dom-chain-hash (hash-ref builder label*))
              (and (hash-has-key? dom-chain-hash entry)
                   (eq? (car (hash-ref dom-chain-hash entry))
                        label)))
            (drop rpo (+ (hash-ref label-rpo-indices label) 1))))

  (define (build builder)
    (for/hash ([entry entries])
      (values entry
              (let build-node ([label entry])
                (cons label (map build-node (children builder entry label)))))))

  (let iterate ([builder (init rev-cont-calls)])
    (if changed
      (iterate (update! builder))
      (build builder))))
