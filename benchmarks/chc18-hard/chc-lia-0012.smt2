(set-logic ALL)
(declare-rel simple!!query ())
(declare-rel inv (Int Int Int Int))
(declare-var A Int)
(declare-var B Int)
(declare-var C Int)
(declare-var D Int)
(declare-var E Int)
(declare-var F Int)
(declare-var G Int)
(declare-var H Int)
(rule (=> (and (= B 1) (>= A D) (not (<= D 0)) (not (<= C 1)) (= (mod C 2) 0))
    (inv D C B A)))
(rule (let ((a!1 (= C (+ G (* (- 1) F)))) (a!2 (= D (+ H (* (- 1) G)))))
(let ((a!3 (and (inv H G F E)
                (= B (* (- 1) F))
                (= A (+ (- 1) E))
                a!1
                (not (<= H 0))
                a!2)))
  (=> a!3 (inv D C B A)))))
(rule (=> (and (inv C A B D) (not (<= C 0)) (not (<= 0 D))) simple!!query))
(query simple!!query)
