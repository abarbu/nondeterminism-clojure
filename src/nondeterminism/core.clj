(ns nondeterminism.core
 (:require [clojure.core.match :only (match)]
           [proteus :refer :all]
           [monads.cont :refer :all]
           [monads.core :refer :all]))

(def ^:dynamic *fail?* true)

(defn top-level-fail []
 (when *fail?* (throw (Exception. "Top-level fail")))
 (set! *fail?* false))

(def ^:dynamic fail' top-level-fail)

(defn set-fail! [procedure] (set! fail' procedure))

(defn for-effects' [e]
 (binding [fail' fail']
  (run-cont
   (callcc (fn [k]
            (set! fail' (fn [] (k false)))
            (mdo (e)
                 (fail')))))))

(defmacro for-effects [e] `(for-effects' (fn [] ~e)))

(defn a-boolean []
 (callcc (fn [c]
          (let [old-fail fail']
           (set-fail! (fn [] (set-fail! old-fail) (if *fail?* (c false) (fail'))))
           (return true)))))

(defn upon-failure' [e]
 (let [old-fail fail']
  (set-fail! (fn [] 
              (set-fail! old-fail)
              (mdo (e)
                   (fail'))))))

(defmacro upon-failure [e] `(upon-failure' (fn [] ~e)))

(defmacro either [& more]
 (clojure.core.match/match
  (vec more)
  [] `(fail')
  [a] a
  [a & r] `(mdo b# ~'<- (a-boolean) (if b# ~a (either ~@r)))))

(defn all-values' [e]
 (let-mutable [values []]
              (for-effects'
               ^:local
               (fn []
                (monads.core/>>=
                 (e)
                 ^:local (fn [r] (set! values (conj values r)) (return r)))
                ;; same as below but I can't mark the generated fn as local for let-mutable
                ;; (mdo r <- (e)
                ;;      let _ = (set! values (conj r values))
                ;;      (return r))
                ))
              values))

(defmacro all-values [e] `(all-values' (fn [] ~e)))

(defn number-of-values' [e]
 (let-mutable [nr 0]
              (for-effects'
               ^:local
               (fn []
                (monads.core/>>=
                 (e)
                 ^:local (fn [r] (set! nr (inc nr)) (return r)))
                ;; same as below but I can't mark the generated fn as local for let-mutable
                ;; (mdo r <- (e)
                ;;      let _ = (set! values (inc values))
                ;;      (return r))
                ))
              nr))

(defmacro number-of-values [e] `(number-of-values' (fn [] ~e)))

(defn one-value' [e]
 (let [n (gensym "novalue")]
  (binding [fail' fail']
   (run-cont
    (callcc (fn [k]
             (mdo let _ = (set! fail' (fn [] (k n)))
                  (e))))))))

(defmacro one-value [e] `(~'one-value' (fn [] ~e)))

(defn possibly?' [e]
 (binding [fail' fail']
  (run-cont
   (callcc (fn [k]
            (mdo let _ = (set! fail' (fn [] (k false)))
                 r <- (e)
                 (if r (return true) (fail'))))))))

(defmacro possibly? [e] `(~'possibly?' (fn [] ~e)))

;; TODO This has somewhat strange semantics, succeeds when the
;; predicate is unsatisfiable
(defn necessarily?' [e]
 (binding [fail' fail']
  (run-cont
   (callcc (fn [k]
            (mdo let _ = (set! fail' (fn [] (k false)))
                 r <- (e)
                 (if r (fail') (return false))))))))

(defmacro necessarily? [e] `(~'necessarily?' (fn [] ~e)))

(defn an-integer-above [i] (either (return i) (an-integer-above (inc i))))
(defn an-integer-below [i] (either (return i) (an-integer-below (dec i))))

(defn an-integer []
 (either 0 (mdo i <- (an-integer-above 1)
                (either (return i) (return (- i))))))

(defn an-integer-between [i j]
 (if (> i j)
  (fail')
  (either (return i) (an-integer-between (inc i) j))))

(defn a-member-of [s]
 (if (vector? s)
  (mdo i <- (an-integer-between 0 (- (count s) 1))
       (return (nth s i)))
  ((fn loop' [l]
    (if (empty? l)
     (fail')
     (either (return (first l))
             (loop' (rest l)))))
   s)))

(defn a-subset-of [l]
 (if (empty? l)
  (return '())
  (mdo y <- (a-subset-of (rest l))
       (either (return (cons (first l) y)) (return y)))))

(defn a-split-of [l]
 ((fn loop' [x y]
   (if (empty? y)
    (return (list x y))
    (either (return (list x y))
            (loop' (concat x (list (first y))) (rest y)))))
  () l))

(defn a-permutation-of [l]
 (if (empty? l)
  (return l)
  (mdo s <- (a-permutation-of (rest l))
       split <- (a-split-of s)
       (return (concat (first split) (cons (first l) (second split)))))))

(defn a-partition-of [x]
 (if (empty? x)
  (return x)
  (mdo y <- (a-partition-of (rest x))
       (either (return (cons (list (first x)) y))
               (mdo z <- (a-member-of y)
                    (return (cons (cons (first x) z)
                                  (remove (fn [a] (identical? z a)) y))))))))

(defn a-partition-of-size [k x]
 (if (< (count x) k)
  (fail')
  ((fn loop' [x]
    (if (= (count x) k)
     (return (map list x))
     (mdo y <- (loop' (rest x))
          z <- (a-member-of y)
          (return (cons (cons (first x) z) (remove (fn [a] (= z a)) y))))))
   x)))

(defn a-subset-of-size [n l]
 (mdo s <- (a-subset-of l)
      (if (not (= (count s) n))
       (fail')
       (return s))))

(defn a-permutation-of-size [n l]
 (mdo a <- (a-subset-of-size n l)
      (a-permutation-of a)))

;; Not yet implemented:

;; (define (local-set-car! x y)
;;  (let ((p (car x))) (upon-failure (set-car! x p)))
;;  (set-car! x y))

;; (define (local-set-cdr! x y)
;;  (let ((p (cdr x))) (upon-failure (set-cdr! x p)))
;;  (set-cdr! x y))

;; (define (local-string-set! s i x)
;;  (let ((p (string-ref s i))) (upon-failure (string-set! s i p)))
;;  (string-set! s i x))

;; (define (local-vector-set! v i x)
;;  (let ((p (vector-ref v i))) (upon-failure (vector-set! v i p)))
;;  (vector-set! v i x))

;; (define-syntax local-one-value
;;  (syntax-rules ()
;;   ((_ a) (local-one-value a (fail')))
;;   ((_ a b)
;;    (call/cc
;;     (lambda (return)
;;      (let ((v #f) (old-fail' fail'))
;;       (set-fail'!
;;        (lambda () (set-fail'! old-fail')
;;           (return (cond (*fail'?* b) (else (set! *fail'?* #t) v)))))
;;       (set! v a)
;;       (set! *fail'?* #f)
;;       (fail')))))))

;; (define-syntax local-set!
;;  (syntax-rules ()
;;   ((_ obj val)
;;    (begin
;;     (let ((p obj)) (upon-fail'ure (set! obj p)))
;;     (set! obj val)))))
