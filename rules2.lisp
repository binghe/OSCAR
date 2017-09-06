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

;;; Rules of deontic operators for legal reasoning.

