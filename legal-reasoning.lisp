(in-package :oscar)

;;; Reasoning rules for deontic opeators: Obl, Forb, Perm and Facult
;;; Author: Chun Tian (binghe)
;;;
;;; Based on `An Axiomatisation for Deontic Reasoning'
;;;          (Sec 17.4 of `Legal Reasoning: A Cognitive Approach to the Law', by Giovanni Sartor)

(def-forwards-reason FON1
    :forwards-premises "(Forb A)" :conclusions "(Obl ~A)" :variables A)

(def-backwards-reason i-FON1
    :backwards-premises "(Forb A)" :conclusions "(Obl ~A)" :variables A)

(def-forwards-reason FON2
    :forwards-premises "(Obl ~A)" :conclusions "(Forb A)" :variables A)

(def-backwards-reason i-FON2
    :backwards-premises "(Obl ~A)" :conclusions "(Forb A)" :variables A)

(def-forwards-reason OP
    :forwards-premises "(Obl A)" :conclusions "(Perm A)" :variables A)

(def-backwards-reason i-OP
    :backwards-premises "(Obl A)" :conclusions "(Perm A)" :variables A)

(def-forwards-reason PNF1
    :forwards-premises "(Forb A)" :conclusions "~(Perm A)"  :variables A)

(def-backwards-reason i-PNF1
    :backwards-premises "(Forb A)" :conclusions "~(Perm A)" :variables A)

(def-forwards-reason PNF2
    :forwards-premises "~(Perm A)" :conclusions "(Forb A)" :variables A)

(def-backwards-reason i-PNF2
    :backwards-premises "~(Perm A)" :conclusions "(Forb A)" :variables A)

(def-forwards-reason JO
    :forwards-premises "(Obl A)" "(Obl B)" :conclusions "(Obl A & B)" :variables A B :defeasible? t)

(def-backwards-reason i-JO
    :backwards-premises "(Obl A)" "(Obl B)" :conclusions "(Obl A & B)" :variables A B :defeasible? t)

(unless (member FON1 *forwards-logical-reasons*)
  (setq *forwards-logical-reasons*
	(nconc *forwards-logical-reasons*
	       (list FON1 FON2 OP PNF1 PNF2 JO))))

(unless (member i-FON1 *backwards-logical-reasons*)
  (setq *backwards-logical-reasons*
	(nconc *backwards-logical-reasons*
	       (list i-FON1 i-FON2 i-OP i-PNF1 i-PNF2 i-JO))))

;;; The support of Facultativeness

(def-forwards-reason FP1
    :forwards-premises "(Fault A)" :conclusions "(Perm A) & (Perm ~A)" :variables A)

(def-backwards-reason i-FP1
    :backwards-premises "(Fault A)" :conclusions "(Perm A) & (Perm ~A)" :variables A)

(def-forwards-reason FP2
    :forwards-premises "(Perm A)" "(Perm ~A)" :conclusions "(Fault A)" :variables A)

(def-backwards-reason i-FP2
    :backwards-premises "(Perm A)" "(Perm ~A)" :conclusions "(Fault A)" :variables A)

(unless (member FP1 *forwards-logical-reasons*)
  (setq *forwards-logical-reasons*
	(nconc *forwards-logical-reasons*
	       (list FP1 FP2))))

(unless (member i-FP1 *backwards-logical-reasons*)
  (setq *backwards-logical-reasons*
	(nconc *backwards-logical-reasons* (list i-FP1 i-FP2))))

;;; Legal reasoning problems

(setq *problems*
      (eval-when (:compile-toplevel :execute)
	(make-problem-list "
Problem #1
(Forb A) entails (Perm ~A)
Given premises:
     (Forb A)    justification = 1.0
Ultimate epistemic interests:
     (Perm ~A)    interest = 1.0

Problem #2
Permission Does Not Entail Facultativeness
Given premises:
     (Perm A)    justification = 1.0
Ultimate epistemic interests:
     (Fault A)    interest = 1.0

Problem #3
Facultativeness Entail Permission
Given premises:
     (Fault A)    justification = 1.0
Ultimate epistemic interests:
     (Perm A)    interest = 1.0

Problem #4
OG-obligation generic-making
Given premises:
     (A -> B)   justification = 1.0
     (Obl A)    justification = 1.0
Ultimate epistemic interests:
     (Obl B)    interest = 1.0

Problem #5
The Definition of Permission
Given premises:
Ultimate epistemic interests:
     (all A)((Perm (Does A)) <-> ~(Forb (Does A)))    interest = 1.0

Problem #6
The Alternative Definition of Permission
Given premises:
Ultimate epistemic interests:
     (all A)((Perm (Does A)) <-> ~(Obl ~(Does A)))    interest = 1.0

")))

(setq *comparison-log*
      '(OSCAR_3.31 0.23 0.23 10 0.95 ((6 1 10 12) (5 1 8 10) (4 2 0 8) (3 1 3 3) (2 2 0 19) (1 1 3 4))))

;; turn on proof showing
(proof-on)
