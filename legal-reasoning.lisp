;;;; Legal reasoning problems

(in-package :oscar)

(setq *problems*
      (eval-when (:compile-toplevel :execute)
	(make-problem-list "
Problem #1
Replay FON
Given premises:
     (Forb A)    justification = 1.0
Ultimate epistemic interests:
     (Obl ~A)    interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      F-JO: {Obl A, Obl B} ||=> Obl (A & B)           strength = 1.0

    FORWARDS CONCLUSIVE REASONS
      F-FON:      {Forb A} ||=> Obl ~A                strength = 1.0
      F-OP:       {Obl A}  ||=> Perm A                strength = 1.0
      F-PNF:      {Forb A} ||=> ~(Perm A)             strength = 1.0
      F-FP:     {Facult A} ||=> (Perm A) & (Perm ~A)  strength = 1.0

")))
