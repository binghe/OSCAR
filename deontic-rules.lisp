;;;; Reasoning rules for deontic opeators: Obl, Forb, Perm and Facult
;;;; Author: Chun Tian (binghe)
;;;;
;;;; Based on `An Axiomatisation for Deontic Reasoning'
;;;;          (Sec 17.4 of `Legal Reasoning: A Cognitive Approach to the Law', by Giovanni Sartor)

(in-package "OSCAR")

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

;;; The support of Facultativeness
(def-forwards-reason FP1
    :forwards-premises "(Fault A)" :conclusions "(Perm A) & (Perm ~A)" :variables A)

(def-forwards-reason FP2
    :forwards-premises "(Perm A)" "(Perm ~A)" :conclusions "(Fault A)" :variables A)

(def-backwards-reason i-FP1
    :backwards-premises "(Fault A)" :conclusions "(Perm A) & (Perm ~A)" :variables A)

(def-backwards-reason i-FP2
    :backwards-premises "(Perm A)" "(Perm ~A)" :conclusions "(Fault A)" :variables A)

(defvar *forwards-deontic-reasons*
  (list FON1 FON2 OP PNF1 PNF2 JO FP1 FP2))

(defvar *backwards-deontic-reasons*
  (list i-FON1 i-FON2 i-OP i-PNF1 i-PNF2 i-JO i-FP1 i-FP2))
