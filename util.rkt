#lang racket/base

(provide exn:unbound exn:unbound?)

(struct exn:unbound exn:fail ())
