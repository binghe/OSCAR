;;;; This file cannot be compiled.

(in-package :oscar)

(def-backwards-reason VACUOUS-CONDITION
    :conclusions "(p -> q)"
    :forwards-premises
        "(define -p (neg p))"
        "-p"
    :variables  p q -p)

;;; Suppositional rules

(def-backwards-reason contra-conditionalization
    :conclusions "(p -> q)"
    :condition (or (and (not (u-genp p))
			(not (conjunctionp (quantifiers-matrix p)))
			(e-genp q))
		   (and (literal p)
			(literal q)
			(or (negationp p) (negationp q))))
    :backwards-premises "~p"
    :discharge "~q"
    :variables  p q)

(def-backwards-reason conditionalization
    :conclusions "(p -> q)"
    :condition (or (u-genp p)
		   (and (literal p) (not (e-genp q)))
		   (conjunctionp (quantifiers-matrix p))
		   (not (e-genp q)))
    :backwards-premises "q"
    :discharge "p"
    :variables  p q)

(setq *backwards-logical-reasons*
      (list adjunction neg-intro i-neg-disj i-neg-condit i-neg-bicondit
	    bicondit-intro disj-cond i-DM conditionalization
	    i-neg-ug i-neg-eg EG UG
	    disj-cond-2
	    contra-conditionalization
	    ;; vacuous-condition
	    ))

;;; Reasoning rules for deontic opeators: Obl, Forb, Perm and Facult
;;; Author: Chun Tian (binghe)
;;;
;;; Based on `An Axiomatisation for Deontic Reasoning'
;;;          (Sec 17.4 of `Legal Reasoning: A Cognitive Approach to the Law', by Giovanni Sartor)

(def-forwards-reason FON1
    :forwards-premises "(Forb A)" :conclusions "(Obl ~A)" :variables A)

(def-forwards-reason FON2
    :forwards-premises "(Obl ~A)" :conclusions "(Forb A)" :variables A)

(def-forwards-reason OP
    :forwards-premises "(Obl A)" :conclusions "(Perm A)" :variables A)

(def-forwards-reason PNF1
    :forwards-premises "(Forb A)" :conclusions "~(Perm A)"  :variables A)

(def-forwards-reason PNF2
    :forwards-premises "~(Perm A)" :conclusions "(Forb A)" :variables A)

(def-forwards-reason JO
    :forwards-premises "(Obl A)" "(Obl B)" :conclusions "(Obl A & B)"
    :variables A B :defeasible? t)

(unless (member FON1 *forwards-logical-reasons*)
  (setq *forwards-logical-reasons*
	(nconc *forwards-logical-reasons*
	       (list FON1 FON2 OP PNF1 PNF2 JO))))

(def-backwards-reason i-FON1
    :backwards-premises "(Forb A)" :conclusions "(Obl ~A)" :variables A)

(def-backwards-reason i-FON2
    :backwards-premises "(Obl ~A)" :conclusions "(Forb A)" :variables A)

(def-backwards-reason i-OP
    :backwards-premises "(Obl A)" :conclusions "(Perm A)" :variables A)

(def-backwards-reason i-PNF1
    :backwards-premises "(Forb A)" :conclusions "~(Perm A)" :variables A)

(def-backwards-reason i-PNF2
    :backwards-premises "~(Perm A)" :conclusions "(Forb A)" :variables A)

(def-backwards-reason i-JO
    :backwards-premises "(Obl A)" "(Obl B)" :conclusions "(Obl A & B)"
    :variables A B :defeasible? t)

(unless (member i-FON1 *backwards-logical-reasons*)
  (setq *backwards-logical-reasons*
	(nconc *backwards-logical-reasons*
	       (list i-FON1 i-FON2 i-OP i-PNF1 i-PNF2 i-JO))))

;;; The support of Facultativeness

(def-forwards-reason FP1
    :forwards-premises "(Fault A)" :conclusions "(Perm A) & (Perm ~A)" :variables A)

(def-forwards-reason FP2
    :forwards-premises "(Perm A)" "(Perm ~A)" :conclusions "(Fault A)" :variables A)

(unless (member FP1 *forwards-logical-reasons*)
  (setq *forwards-logical-reasons*
	(nconc *forwards-logical-reasons*
	       (list FP1 FP2))))

(def-backwards-reason i-FP1
    :backwards-premises "(Fault A)" :conclusions "(Perm A) & (Perm ~A)" :variables A)

(def-backwards-reason i-FP2
    :backwards-premises "(Perm A)" "(Perm ~A)" :conclusions "(Fault A)" :variables A)

(unless (member i-FP1 *backwards-logical-reasons*)
  (setq *backwards-logical-reasons*
	(nconc *backwards-logical-reasons* (list i-FP1 i-FP2))))
