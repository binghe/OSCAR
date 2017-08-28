#| This requires OSCAR_3.31.  This is based on non-linear planner 43.  Lots of little changes. |#
(in-package "OSCAR")

(proclaim '(special *operators* *plan-trace* *initial-state* *goal-state* **premises** *start-time* *inputs*
                  *empty-inference-queue* *msg* *plans* *plan-node-number* *finish*
                  *plan-nodes* *start* *display-time* *causal-links* *causal-link-number* *planner*
                  *planning-problems* *plan-comparison-log* *display-plans* protoplan *plans-decided*
                  *solutions* *defeater-priority*))

(setf *planner* "Non-Linear-Planner-44")

(setf *test-log* nil)

(setf *time-limit* nil)

(setf *display-plans* nil)

(setf *defeater-priority* 1.0)

(defunction show-plans () (setf *display-plans* (not *display-plans*)))

(defstruct (plan-node (:print-function print-plan-node) (:conc-name nil))
    (plan-node-number 0)
    (plan-node-action nil))

(defunction print-plan-node (node stream depth)
    (declare (ignore depth))
    (cond ((eql (plan-node-number node) 0) (princ "*start*" stream))
              ((eql (plan-node-number node) -1) (princ "*finish*" stream))
              (t
                (princ "<pn" stream)
                (princ (plan-node-number node) stream)
                (princ ": " stream)
                (princ (plan-node-action node) stream)
                (princ ">" stream))))

(defparameter *start* (make-plan-node))

(defparameter *finish* (make-plan-node :plan-node-number -1))

(defstruct (plan (:print-function print-plan) (:conc-name nil))
    (plan-number 0)
    (plan-steps nil)
    (plan-goal nil)
    (causal-links nil)
    (before-nodes nil)
    (not-between nil)
    (supporting-inference-nodes nil)
    (live-causal-links nil)
    (live-links? nil)   ;; t if live-causal-links has been computed
    (fixed-links nil)
    )

;; This lexically-orders before-nodes.
(defunction before-< (x y)
    (or (< (plan-node-number (car x)) (plan-node-number (car y)))
          (and (eql (plan-node-number (car x)) (plan-node-number (car y)))
                   (< (plan-node-number (cdr x)) (plan-node-number (cdr y))))))

;; This lexically-orders not-between.
(defunction not-between-< (x y)
    (or (< (plan-node-number (car x)) (plan-node-number (car y)))
          (and (eql (plan-node-number (car x)) (plan-node-number (car y)))
                   (< (plan-node-number (cadr x)) (plan-node-number (cadr y))))
          (and (eql (plan-node-number (car x)) (plan-node-number (car y)))
                   (eql (plan-node-number (cadr x)) (plan-node-number (cadr y)))
                   (< (plan-node-number (cddr x)) (plan-node-number (cddr y))))))

(defunction print-plan (plan stream depth)
    (declare (ignore depth))
    (princ "<plan " stream)
    (princ (plan-number plan) stream)
    (princ ">" stream))

(defunction plan-node (n)
    (find-if #'(lambda (x) (eql (plan-node-number x) n)) *plan-nodes*))

(defstruct (causal-link (:print-function print-causal-link) (:conc-name nil))
    (causal-link-number 0)
    (causal-link-root nil)
    (causal-link-goal nil)
    (causal-link-target nil))

(defunction print-causal-link (link stream depth)
    (declare (ignore depth))
    (princ "<" stream)
    (princ (plan-node-number (causal-link-root link)) stream) (princ " --" stream)
    (prinp (causal-link-goal link) stream) (princ "--> " stream)
    (if (eq (causal-link-target link) *finish*)
      (princ "*finish*" stream)
      (princ (plan-node-number (causal-link-target link)) stream))
    (princ ">" stream))

(defunction build-causal-link (root goal target)
    (let ((link
              (find-if
                #'(lambda (L)
                      (and (eq (causal-link-root L) root)
                               (eq (causal-link-target L) target)
                               (equal (causal-link-goal L) goal)))
                *causal-links*)))
      (when (null link)
           (setf link
                   (make-causal-link
                     :causal-link-number (incf *causal-link-number*)
                     :causal-link-root root
                     :causal-link-goal goal
                     :causal-link-target target))
           (push link *causal-links*))
      link))

(defunction call-set (node plan)
    (subset #'(lambda (L) (equal (causal-link-target L) node)) (causal-links plan)))

(defunction causal-link (n)
    (find-if #'(lambda (x) (eql (causal-link-number x) n)) *causal-links*))

(defunction plan (n)
    (find-if #'(lambda (p) (eql (plan-number p) n)) *plans*))

(defunction subplan (plan1 plan2)
    (and (subsetp (plan-steps plan1) (plan-steps plan2))
             (every #'(lambda (x)
                               (or (eq (cdr x) *finish*)
                                     (mem (car x) (preceding-nodes (cdr x) plan2 (before-nodes plan2)))))
                         (before-nodes plan1))
             (every #'(lambda (x)
                               (or (not (member (car x) (plan-steps plan1)))
                                     (not (member (cdr x) (plan-steps plan1)))
                                     (eq (cdr x) *finish*)
                                     (mem (car x) (preceding-nodes (cdr x) plan1 (before-nodes plan1)))))
                         (before-nodes plan2))
             (every #'(lambda (x)
                               (or (eq (cddr x) *finish*)
                                     (mem x (not-between plan2))))
                         (not-between plan1))
             (every #'(lambda (x)
                               (or (not (member (car x) (plan-steps plan1)))
                                     (not (member (cadr x) (plan-steps plan1)))
                                     (not (member (cddr x) (plan-steps plan1)))
                                     (eq (cddr x) *finish*)
                                     (mem x (not-between plan1))))
                         (not-between plan2))))

(defunction temporally-projectible (P)
    (or (literal P)
          (and (conjunctionp P)
                   (every #'(lambda (Q) (literal Q))
                               (conjuncts P)))))

(defun print-interest (x stream depth)
    (declare (ignore depth))
    (princ "#<" stream) (princ "Interest " stream)
    (princ (interest-number x) stream)
   ; (princ ": " stream) (prinp-sequent (interest-sequent x) stream)
    (princ ">" stream))

;;=============== substitution into plan formulas =============================

(defunction before-order (x y)
    (or (< (inference-number (car x)) (inference-number (car y)))
          (and (eql (inference-number (car x)) (inference-number (car y)))
                   (< (inference-number (cdr x)) (inference-number (cdr y))))))

(defunction not-between-order (x y)
    (or (< (inference-number (car x)) (inference-number (car y)))
          (and (eql (inference-number (car x)) (inference-number (car y)))
                   (< (inference-number (cadr x)) (inference-number (cadr y))))
          (and (eql (inference-number (car x)) (inference-number (car y)))
                   (eq (inference-number (cadr x)) (inference-number (cadr y)))
                   (< (inference-number (cddr x)) (inference-number (cddr y))))))

(defun match-sublis (m x &key (test 'eq))
   (cond ((eq m t) x)
             (t (plan-sublis m x :test test))))

(defunction plan-sublis (m x &key test)
   ; (setf m* m x* x) (break)
    (cond
      ((consp x)
        (cons (plan-sublis m (car x) :test test) (plan-sublis m (cdr x) :test test)))
      ((plan-p x)
        (let* ((plan-steps (plan-sublis m (plan-steps x) :test test))
                  (before-nodes (before-nodes x))
                  (not-between (not-between x))
                  (causal-links (causal-links x)))
          (cond
            ((equal plan-steps (plan-steps x)) x)
            (t
              (let ((node-match (mapcar #'(lambda (x y) (cons x y)) (plan-steps x) plan-steps)))
                (setf before-nodes (sublis node-match before-nodes))
                (setf not-between (sublis node-match not-between))
                (setf causal-links (sublis node-match causal-links))
                (build-plan plan-steps (plan-goal x) causal-links before-nodes not-between))))))
      ((plan-node-p x)
        (let ((action (plan-sublis m (plan-node-action x) :test test)))
          (if (not (equal action (plan-node-action x)))
            (let ((node
                      (make-plan-node
                        :plan-node-number (plan-node-number x)
                        :plan-node-action action)))
              (draw-conclusion `(plan-node ,node) nil :given nil 1.0 1 nil nil)
              node)
            x)))
      (t (let ((assoc (assoc x m :test test)))
            (if assoc (cdr assoc) x)))))

(defunction plan-subst (x y p &key (test 'eq))
    (cond
      ((consp p)
        (cons (plan-subst x y (car p) :test test) (plan-subst x y (cdr p) :test test)))
      ((plan-p p)
        (let* ((plan-steps (plan-subst x y (plan-steps p) :test test))
                  (before-nodes (before-nodes p))
                  (not-between (not-between p))
                  (causal-links (causal-links p)))
          (cond
            ((equal plan-steps (plan-steps p)) p)
            (t
              (let ((node-match (mapcar #'(lambda (x y) (cons x y)) (plan-steps x) plan-steps)))
                (setf before-nodes (sublis node-match before-nodes))
                (setf not-between (sublis node-match not-between))
                (setf causal-links (sublis node-match causal-links))
                (build-plan plan-steps (plan-goal p) causal-links before-nodes not-between))))))
      ((plan-node-p p)
        (let ((action (plan-subst x y (plan-node-action p) :test test)))
          (if (not (equal action (plan-node-action p)))
            (let ((node
                      (make-plan-node
                        :plan-node-number (plan-node-number p)
                        :plan-node-action action)))
              (draw-conclusion `(plan-node ,node) nil :given nil 1.0 1 nil nil)
              node)
            p)))
      (t (if (funcall test y p) x p))))

(defunction variable-correspondence (P Q P-vars Q-vars terms)
    (cond
      ((equal P Q) terms)
      ((member P P-vars)
        (let ((quantifier-variables (mem3 terms)))
          (cond ((rassoc Q quantifier-variables) (throw 'unifier nil))
                    (t (list (cons P (mem1 terms)) (cons Q (mem2 terms)) quantifier-variables)))))
      ((member Q Q-vars)
        (cond ((assoc P (mem3 terms)) (throw 'unifier nil))
                  (t (list (cons P (mem1 terms)) (cons Q (mem2 terms)) (mem3 terms)))))
      ((null P)
        (cond ((null Q) terms)
                    (t (throw 'unifier nil))))
      ((null Q) (throw 'unifier nil))
      ((plan-p P)
        (cond ((plan-p Q) (throw 'unifier nil))
                  ((member Q Q-vars)
                     (cond ((assoc P (mem3 terms)) (throw 'unifier nil))
                                 (t (list (cons P (mem1 terms)) (cons Q (mem2 terms)) (mem3 terms)))))
                    (t (throw 'unifier nil))))
      ((plan-node-p P)
      (cond ((member Q Q-vars)
                 (cond ((assoc P (mem3 terms)) (throw 'unifier nil))
                          (t (list (cons P (mem1 terms)) (cons Q (mem2 terms)) (mem3 terms)))))
               (t (throw 'unifier nil))))
      ((not (listp P))
        (cond ((not (listp Q))
                      (cond ((member Q Q-vars)
                                   (list (cons P (mem1 terms)) (cons Q (mem2 terms)) (mem3 terms)))
                                  ((eql P Q) terms)
                                  ((eql (cdr (assoc P (mem3 terms))) Q) terms)
                                  (t (throw 'unifier nil))))
                    (t (throw 'unifier nil))))
      ((not (listp Q)) (throw 'unifier nil))
      ((or (eq (car P) 'all) (eq (car P) 'some))
        (cond ((eql (car P) (car Q))
                     (variable-correspondence
                       (mem3 P) (mem3 Q) P-vars Q-vars
                       (list (mem1 terms) (mem2 terms)
                               (cons (cons (mem2 P) (mem2 Q)) (mem3 terms)))))
                    (t (throw 'unifier nil))))
      (t
        (variable-correspondence
          (cdr P) (cdr Q) P-vars Q-vars
          (variable-correspondence (car P) (car Q) P-vars Q-vars terms)))))

(defunction sequential-sublis (m X)
    (cond ((eq (length m) 1)
                 (plan-subst (cdr (mem1 m)) (mem1 (mem1 m)) X))
                (t (plan-subst (cdr (mem1 m)) (mem1 (mem1 m)) (sequential-sublis (cdr m) X)))))

;;======================= planning problems =================================

(defmacro make-planning-problem (&rest body)
    (let* ((newbody (make-clauses body))
              (number (cadr (find-if #'(lambda (x) (eq (car x) :number)) newbody)))
              (start-time (cadr (find-if #'(lambda (x) (eq (car x) :start-time)) newbody)))
              (msg (cadr (find-if #'(lambda (x) (eq (car x) :message)) newbody)))
              (reasons
                (mapcar 'eval (cdr (find-if #'(lambda (x) (eq (car x) :reasons)) newbody))))
              (forwards-reasons (subset #'forwards-reason-p reasons))
              (backwards-reasons (subset #'backwards-reason-p reasons))
              (inputs
                (mapcar #'(lambda (x) (list (car x) (reform-if-string (mem2 x)) (mem3 x)))
                               (cdr (find-if #'(lambda (x) (eq (car x) :inputs)) newbody))))
              (premises (cdr (find-if #'(lambda (x) (eq (car x) :premises)) newbody)))
              (goal (reform (cadr (find-if #'(lambda (x) (eq (car x) :goal)) newbody)))))
      (when premises
            (setf premises
                       (mapcar #'(lambda (p) (list (mem1 p) (mem2 p) (mem3 p) (mem4 p))) premises)))
      `(progn
           (setf *problem-number* ',number)
           (setf *msg* ,msg)
           (setf *start-time* (or ,start-time 0))
           (setf *forwards-substantive-reasons* ',forwards-reasons)
           (setf *backwards-substantive-reasons* ',backwards-reasons)
           (setf *inputs* ',inputs)
           (setf **premises** ',premises)
           (setf *goal-state* ',goal)
           (setf *fixed-ultimate-epistemic-interests* (list (plan-interest  ',goal)))
           (dolist (R *forwards-substantive-reasons*) (setf (undercutting-defeaters R) nil))
           (dolist (R *backwards-substantive-reasons*) (setf (undercutting-defeaters R) nil))
           (dolist (d *backwards-substantive-reasons*)
               (dolist (R (reason-defeatees d)) (push d (undercutting-defeaters R))))
           )))

(defunction plan-interest (goal)
    (make-query
      :query-number 1
      :query-formula `(? plan (plan-for plan ,goal))
      :query-strength 0.1
      :positive-query-instructions
      (list #'(lambda (c)
                   (cond ((and (or *display-plans* *display?*) (eql (old-undefeated-degree-of-support c) 0.0))
                               (reinstate-plan (mem2 (node-formula c))))
                             ((and *display-plans* (not *display?*)) (display-plan (mem2 (node-formula c)))))))
      :negative-query-instructions
      (list #'(lambda (c)
                   (when (or *display-plans* *display?*)
                        (let* ((formula (node-formula c))
                                  (plan (mem2 formula)))
                          (retract-plan plan)))))
      ))

(defunction display-planning-settings ()
    (terpri)
    (princ "(") (terpri)
    (princ "======================================================================")
    (terpri) (terpri)
    (princ "                                 ") (princ *version*) (princ "          ")
    (let ((time (multiple-value-list (get-decoded-time))))
       (princ (mem5 time)) (princ "/") (princ (mem4 time)) (princ "/")
       (princ (mem6 time)) (princ "          ") (princ (mem3 time))
       (princ ":") (if (< (mem2 time) 10) (princ "0")) (princ (mem2 time))
       (princ ":") (if (< (mem2 time) 10) (princ "0")) (princ (mem1 time))
       (terpri))
    (princ "                                           ") (princ *planner*) (terpri) (terpri)
    (let ((message 
                (if *problem-number*
                  (if (and *msg* (read-from-string *msg* nil)) 
                    (cat-list (list "Problem number " (write-to-string *problem-number*) ":  " *msg*))
                       (cat-list (list "Problem number " (write-to-string *problem-number*) ":  ")))
                     *msg*)))
      (when message (princ message) (terpri) (terpri)))
    (princ "Forwards-substantive-reasons:") (terpri)
    (dolist (R *forwards-substantive-reasons*)
        (princ "          ") (princ R) (terpri))
    (terpri)
    (princ "Backwards-substantive-reasons:") (terpri)
    (dolist (R *backwards-substantive-reasons*)
        (princ "          ") (princ R) (terpri))
    (terpri)
    (when (not (zerop *start-time*))
         (princ "Start reasoning at cycle ") (princ *start-time*) (terpri) (terpri))
    (princ "Goal-state:") (terpri)
    (dolist (p (conjuncts *goal-state*))
        (princ "          ") (princ (pretty p)) (terpri))
    (terpri)
    (princ "Inputs:") (terpri)
    (dolist (x *inputs*)
        (princ "          ") (prinp (mem2 x)) (princ " : at cycle ") (princ (mem1 x))
        (princ " with justification ") (princ (mem3 x)) (terpri))
    (terpri)
    (when **premises**
         (setf **premises** (mapcar #'(lambda (x) (cons (reform-if-string (car x)) (cdr x))) **premises**))
         (princ "Given:") (terpri)
         (dolist (P **premises**)
             (princ "          ") (prinp (mem1 P)) (princ "  : ")
             (when (mem3 P) (princ " at cycle ") (princ (mem3 P)))
             (princ " with justification = ") (princ (mem2 P)) (terpri))
         (terpri))
   ; (setf *ultimate-epistemic-interests* *fixed-ultimate-epistemic-interests*)
    (setf *query-number* 0)
    (princ "======================================================================")
    (terpri) (terpri))

(setf *reform-list* nil)
(let ((P (gensym)) (Q (gensym)))
;  (pushnew `((,P is a plan for ,Q) (plan-for ,P ,Q) (,P ,Q)) *reform-list* :test 'equal)
  (pushnew `((,P => ,Q) (=> ,P ,Q) (,P ,Q)) *reform-list* :test 'equal)
  )

#|
(defunction complexity (x)
    (cond ((null X) 0)
              ((stringp x) 1)
              ((atom x) 1)
              ((listp x) 
                (cond ((skolem-function (car x))
                            (cond ((null (cdr x)) 1)
                                      ((and (not (listp (cadr x))) (not (eq (cadr x) '=)))
                                        *skolem-multiplier*)
                                      ((and (listp (cadr x)) (skolem-function (caar (cdr x))))
                                        (* *skolem-multiplier* (1+ (complexity (cdr x)))))
                                      (t (apply #'+ (mapcar #'complexity x)))))
                          ((or (u-genp x) (e-genp x)) (* *quantifier-discount* (complexity (q-matrix x))))
                          ((eq (car x) 'plan-for) (+ 2 (complexity (mem3 x))))
                          ((eq (car x) 'protoplan-for) (+ 2 (complexity (mem3 x))))
                          ((eq (car x) 'embellished-plan-for) (+ 2 (complexity (mem3 x))))
                          ((consp (cdr x)) (apply #'+ (mapcar #'complexity x)))
                          (t (+ (complexity (car x)) (complexity (cdr x))))))))
|#

(defunction complexity (x)
    (cond ((null X) 0)
              ((stringp x) 1)
              ; ((plan-p x) (length (plan-steps x)))
              ((plan-p x) (length (plan-steps x)))
              ((atom x) 1)
              ((listp x) 
                (cond ((skolem-function (car x))
                            (cond ((null (cdr x)) 1)
                                      ((and (not (listp (cadr x))) (not (eq (cadr x) '=)))
                                        *skolem-multiplier*)
                                      ((and (listp (cadr x)) (skolem-function (caar (cdr x))))
                                        (* *skolem-multiplier* (1+ (complexity (cdr x)))))
                                      (t (apply #'+ (mapcar #'complexity x)))))
                          ((or (u-genp x) (e-genp x)) (* *quantifier-discount* (complexity (q-matrix x))))
                          ;   ((eq (car x) 'protoplan-for)
                          ;    (+ 1 
                          ;        (if (plan-p (mem2 x)) (length (plan-steps (mem2 x))) 1)
                          ;        (complexity (mem3 x))))
                          ;  ((eq (car x) 'plan-for)
                          ;    (+ 1 
                          ;        (if (plan-p (mem2 x)) (length (plan-steps (mem2 x))) 1)
                          ;        (complexity (mem3 x))))
                          
                          ((eq (car x) '=>) 1)
                          ((eq (car x) 'protoplan-for)
                           ; (-
                              (+ 1 
                                   (if (plan-p (mem2 x)) (length (plan-steps (mem2 x))) 1)
                                   ; (complexity (mem3 x))
                                   (length (mem4 x))))
                             ; (+ (length (mem5 x)) (length (mem6 x)))))
                          ((eq (car x) 'plan-for)
                            (+ 1 
                                 (if (plan-p (mem2 x)) (length (plan-steps (mem2 x))) 1)
                                 ))
                          ; (complexity (mem3 x))))
                          
                          ((eq (car x) 'embellished-plan-for)
                            (+ 2 (length (plan-steps (mem3 x)))))
                          ((eq (car x) 'embellished-protoplan-for)
                            (+ 2 (length (plan-steps (mem3 x)))))
                           ((eq (car x) 'plan-undermines-causal-link) 1)
                           ((eq (car x) 'plan-undermines-causal-links) 2)
                            ; (1+ (complexity (list (mem2 x) (mem3 x) (mem4 x) (mem5 x)))))
                            ; (+ 4 (if (plan-p (mem2 x)) (length (plan-steps (mem2 x))) 1))
                           ((eq (car x) 'plan-node) .1)
                          (t (+ (complexity (car x)) (complexity (cdr x))))))
              ((consp (cdr x)) (apply #'+ (mapcar #'complexity x)))
              (t 1)))

(defunction make-new-conclusion
    (sequent deductive-only reductio-ancestors non-reductio-supposition)
    (let* ((c-vars (formula-node-variables (sequent-formula sequent)))
              (sup (sequent-supposition sequent))
              (i-vars (supposition-variables sup))
              (node
                (make-inference-node
                  :inference-number (incf *inference-number*)
                  :node-sequent sequent
                  :node-formula (sequent-formula sequent)
                  :node-supposition sup
                  :node-kind :inference
                  :deductive-only deductive-only
                  :node-variables c-vars
                  :node-supposition-variables i-vars
                  :non-reductio-supposition non-reductio-supposition
                  :reductio-ancestors reductio-ancestors
                  )))
      (when (and (listp (sequent-formula sequent))
                       (or (equal (car (sequent-formula sequent)) 'plan-for)
                             (equal (car (sequent-formula sequent)) 'protoplan-for)
                             (equal (car (sequent-formula sequent)) 'embellished-protoplan-for)
                             (equal (car (sequent-formula sequent)) 'embellished-plan-for)))
         (push node (supporting-inference-nodes (mem2 (sequent-formula sequent))))
         (when *display?*
             (display-plan (mem2 (sequent-formula sequent)))))
       node))

(defunction display-query (Q)
    (princ "  Interest in ") (prinp (query-formula Q)) (terpri)
    (cond ((null (answered? Q))
                 (princ "  is unsatisfied.")
                 (when (null (query-answers Q)) (princ "  NO ARGUMENT WAS FOUND."))
                 (terpri))
              ((or (whether-query-p Q) (?-query-p Q))
            (dolist (C (query-answers Q))
           ; (let ((C (car (query-answers Q))))
                      (when (>= (compute-undefeated-degree-of-support C) (query-strength Q))
                           (princ "  is answered by node ")
                           (princ (inference-number C)) (princ ":  ")
                           (princ (pretty (node-formula C))) (terpri)
                           (when (plan-p (mem2 (node-formula C)))
                         (show-plan (mem2 (node-formula C)) nil))
                           (let ((skolem-functions (skolem-functions (node-formula C))))
                              (when skolem-functions
                                   (let* ((sf (mem1 skolem-functions))
                                             (support-link
                                               (find-if #'(lambda (SL)
                                                                 (and (eq (support-link-rule SL) EI)
                                                                           (occur sf (node-formula (support-link-target SL)))
                                                                           (not (occur sf (node-formula (mem1 (support-link-basis SL)))))))
                                                            (ancestral-links C))))
                                      (when support-link
                                           (let* ((node (mem1 (support-link-basis support-link)))
                                                     (formula (node-formula node))
                                                     (var (q-variable formula)))
                                              (princ "  where ") (princ sf) (princ " is any ") (princ var)
                                              (princ " such that ") (princ (q-matrix formula)) (princ ",") (terpri)
                                              (princ "  and the existence of such")
                                              (if (equal var "x") (princ " an ") (princ " a ")) (princ var)
                                              (princ " is guaranteed by node ") (princ (inference-number node)) (terpri))))))
                           )))
                (t (dolist (C (query-answers Q))
                       (when (>= (compute-undefeated-degree-of-support C) (query-strength Q))
                            (princ "  is answered affirmatively by node ")
                            (princ (inference-number C)) (terpri)))))
    (princ "---------------------------------------------------") (terpri))

(defunction display-node
    (n proof-nodes nodes-used interests-used interests-discharged nodes-displayed)
   ; (setf nn n pn proof-nodes nu nodes-used iu interests-used id interests-discharged nd nodes-displayed) ; (break)
    ;; (step (display-node nn pn nu iu id nd))
    (when (eq (node-kind n) :percept)
         (princ "|||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||")
         (terpri) (princ "It appears to me that ") (prinp (node-formula n)) (terpri)
         (princ "|||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||")
         (terpri))
    (princ "  # ") (princ (inference-number n))
    (when (member n *not-strictly-relevant-nodes*) (princ "   NOT STRICTLY RELEVANT"))
    (terpri)
    (princ "  ") (when (eq (node-kind n) :percept) (princ "It appears to me that "))
    (prin-pretty (node-formula n))
    (when (node-supposition n)
         (princ "    supposition: ") (set-prinp (node-supposition n)))
    (if (zerop (undefeated-degree-of-support n)) (princ "                  DEFEATED"))
    (when (and (member n nodes-used)
                          (not (member n proof-nodes)))
         (princ "   --  NOT USED IN PROOF"))
    (terpri)
    (cond ((keywordp (node-justification n)) (princ "  ") (princ (node-justification n)) (terpri))
                ((support-links n)
                  (princ "  Inferred by:") (terpri)
                  (dolist (L* (support-links n))
                      (when (subsetp (support-link-basis L*) nodes-displayed)
                           (princ "                support-link #") (princ (support-link-number L*))
                           (princ " from ") (princ-set (mapcar #'inference-number (support-link-basis L*)))
                           (princ " by ") (princ (support-link-rule L*))
                           (when (support-link-clues L*)
                         (princ " with clues ")
                         (princ-set (mapcar #'inference-number (support-link-clues L*))))
                           (when (support-link-defeaters L*)
                                (princ "  defeaters: ")
                                (princ-set (mapcar #'inference-number (support-link-defeaters L*))))
                           (when (defeating-assignment-trees L*) (princ "   DEFEATED"))
                           (terpri)))))
    (when (node-defeatees n)
         (princ "  defeatees: ")
         (princ "{ ")
         (let ((L (car (node-defeatees n))))
            (princ "link ")
            (princ (support-link-number L)) (princ " for node ")
            (princ (inference-number (support-link-target L))))
         (dolist (L (cdr (node-defeatees n)))
             (princ " , ")
            (princ "link ")
             (princ (support-link-number L)) (princ " for node ")
             (princ (inference-number (support-link-target L))))
         (princ " }") (terpri))
    ; (princ " by ") (princ (node-justification n))
    (let ((generating-interests (intersection (generating-interests n) interests-used)))
       (cond ((> (length generating-interests) 1)
                    (princ " generated by interests ")
                    (print-list (mapcar #'interest-number generating-interests) 40))
                   ((eq (length generating-interests) 1)
                     (princ "  generated by interest ")
                     (princ (interest-number (mem1 generating-interests)))))
       (when generating-interests (terpri)))
    (let ((DI (enabling-interests n)))
       (cond
         ((> (length DI) 1)
           (princ "  This node is inferred by discharging links to interests ")
           (princ (mapcar #'interest-number DI)) (terpri))
         (DI
           (princ "  This node is inferred by discharging a link to interest #")
           (princ (interest-number (car DI)))
           (let ((SL (find-if #'(lambda (SL) (equal (support-link-rule SL) :reductio)) (support-links n))))
              (when SL
                   (let* ((node* (mem1 (support-link-basis SL)))
                             (rs (find-if
                                    #'(lambda (sup)
                                          (and
                                            (member (car DI) (generating-interests sup))
                                            ;; 
                                            (mem sup (a-range (reductio-ancestors node*)))
                                            (not (mem sup (a-range (reductio-ancestors n))))))
                                    (a-range (reductio-ancestors node*)))))
                                    ;; (generated-suppositions (car DI)))))
                      (when rs
                           (princ " as a result of inferring node #") (princ (inference-number node*))
                           (princ " from") (terpri) (princ "  reductio-supposition #")
                           (princ (inference-number rs)) (princ ", which was generated by interest #")
                           (princ (interest-number (car DI)))))))
           (terpri)))
       (let ((interests
                 (subset
                   #'(lambda (in)
                         (and
                           (member n (discharging-nodes in))
                           (or
                             (some
                               #'(lambda (dr)
                                     (some
                                       #'(lambda (pn)
                                             (some
                                               #'(lambda (SL)
                                                     (and (equal (support-link-rule SL) :reductio)
                                                               (member n (support-link-basis SL))
                                                               (member (car dr) (support-link-basis SL))))
                                               (support-links pn)))
                                       proof-nodes))
                               (direct-reductio-interest in))
                             (some #'(lambda (L)
                                              (and
                                                (discharged-link L)
                                                (or
                                                  (equal (link-rule L) :answer)
                                                  (some
                                                    #'(lambda (pn)
                                                          (and
                                                            (member (resultant-interest L) (enabling-interests pn))
                                                            (some
                                                              #'(lambda (SL)
                                                                    (member n (support-link-basis SL)))
                                                              (support-links pn))))
                                                    proof-nodes))))
                                          (right-links in)))))
                   (set-difference interests-used DI))))
          (cond ((> (length interests) 1)
                       (princ "  This discharges interests ") (print-list (mapcar #'interest-number interests) 40))
                      ((eq (length interests) 1)
                        (princ "  This discharges interest ") (princ (interest-number (mem1 interests))))
                      (t
                        (setf interests
                                 (subset
                                   #'(lambda (in)
                                         (and
                                           (member n (discharging-nodes in))
                                           (not
                                             (some
                                               #'(lambda (dn)
                                                     (strongly-discharging-node dn in proof-nodes interests-discharged))
                                               (discharging-nodes in)))))
                                   (set-difference interests-used DI)))
                        (cond
                          ((> (length interests) 1)
                            (princ "  This discharges interests ") (print-list (mapcar #'interest-number interests) 40)
                            (princ " but no inference made by discharging these interests is used in the solution."))
                          ((eq (length interests) 1)
                            (princ "  This discharges interest ") (princ (interest-number (mem1 interests)))
                            (princ " but no inference made by discharging this interest is used in the solution.")))))
          (when interests (terpri))))
    (when (and (listp (node-formula n))
                     (or (eq (car (node-formula n)) 'plan-for)
                           (eq (car (node-formula n)) 'protoplan-for)
                           (eq (car (node-formula n)) 'embellished-protoplan-for)))
       (display-plan (mem2 (node-formula n))))
   (when *graphics-pause* (pause-graphics))  ;; wait for a character to be typed in the Listener
    (when (and *graph-log* (member n proof-nodes))
         (push n *nodes-displayed*)
         (draw-n n *og* nodes-displayed)))

(defunction display-used-interest
    (interest proof-nodes used-nodes used-interests enabling-interests interests-used-in-proof)
    ; (when (eq interest (interest 6)) (setf i interest pn proof-nodes un used-nodes ui used-interests ein enabling-interests iun interests-used-in-proof) (break))
    ;; (step (display-used-interest i pn un ui ein iun))
    (princ "                                        # ") (princ (interest-number interest))
    (when (not (member interest interests-used-in-proof))
         (princ "               NOT USED IN PROOF"))
    (terpri)
    (princ "                                        ")
    (when (deductive-interest interest) (princ "deductive "))
    (when (reductio-interest interest) (princ "reductio "))
    (princ "interest: ") (prin-pretty (interest-formula interest))
    (when (interest-supposition interest)
         (princ "    supposition: ")
         (set-prinp (interest-supposition interest)))
    (terpri)
    (when
         (some #'(lambda (L) (query-p (resultant-interest L)))
                     (right-links interest))
         (princ "                                        This is of ultimate interest") (terpri))
    (dolist (L (right-links interest))
        (when (and (not (query-p (resultant-interest L))) (discharged-link L)
                            (member (resultant-interest L) used-interests))
             (princ "                                        For ")
             (when (reductio-interest (resultant-interest L)) (princ "reductio "))
             (princ "interest ")
             (princ (interest-number (resultant-interest L)))
             (princ " by ") (princ (link-rule L))
             (let ((nodes (supporting-nodes L)))
               (when nodes
                    (cond ((equal (length nodes) 1)
                                (princ " using node ")
                                (princ (inference-number (mem1 nodes))))
                              (t
                                (princ " using nodes ")
                                (print-list (mapcar
                                                  #'(lambda (conclusion)
                                                        (inference-number conclusion))
                                                  nodes) 40)))))
             (let ((nodes (link-clues L)))
               (when nodes
                    (cond ((equal (length nodes) 1)
                                (princ " with clue ")
                                (princ (inference-number (mem1 nodes))))
                              (t
                                (princ " with clues ")
                                (print-list (mapcar
                                                  #'(lambda (conclusion)
                                                        (inference-number conclusion))
                                                  nodes) 40)))))
             (terpri)))
    (let ((direct-reductio-interest
              (subset #'(lambda (n) (assoc n (direct-reductio-interest interest)))
                            used-nodes)))
      (cond ((> (length direct-reductio-interest) 1)
                  (princ "                                        Reductio interest generated by nodes ")
                  (print-list (mapcar #'(lambda (n) (inference-number n))
                                                 direct-reductio-interest) 40) (terpri))
                ((= (length direct-reductio-interest) 1)
                  (princ "                                        Reductio interest generated by node ")
                  (princ (inference-number (mem1 direct-reductio-interest))) (terpri))))
    (let ((discharging-nodes
              (subset
                #'(lambda (dn)
                      (strongly-discharging-node dn interest proof-nodes enabling-interests))
                (intersection (discharging-nodes interest) used-nodes)))
            (defeatees
                (subset #'(lambda (L)
                                   (member (support-link-target L) proof-nodes))
                              (interest-defeatees interest))))
      (when defeatees
           (princ "                                        Of interest as a defeater for ")
           (cond ((cdr defeatees)
                       (princ "support-links: ")
                       (princ "{ ")
                       (let ((L (car defeatees)))
                         (princ "link ")
                         (princ (support-link-number L)) (princ " for node ")
                         (princ (inference-number (support-link-target L))))
                       (dolist (L (cdr defeatees))
                           (princ " , ")
                           (princ "link ")
                           (princ (support-link-number L)) (princ " for node ")
                           (princ (inference-number (support-link-target L))))
                       (princ " }"))
                     (t
                       (princ "support-link ")
                       (let ((L (car defeatees)))
                         (princ (support-link-number L)) (princ " for node ")
                         (princ (inference-number (support-link-target L))))))
           (terpri))
      (cond
        (discharging-nodes
          (princ "                                        This interest is discharged by")
          (cond ((> (length discharging-nodes) 1) (princ " nodes ")
                      (princ (mapcar #'inference-number discharging-nodes)))
                    (t (princ " node ") (princ (inference-number (mem1 discharging-nodes)))))
          (terpri))
        ((not (some #'(lambda (L) (and (query-p (resultant-interest L)) (discharged-link L)))
                             (right-links interest)))
          (setf discharging-nodes
                   (intersection (discharging-nodes interest) used-nodes))
          (cond
            (discharging-nodes
              (princ "                                        This interest is discharged by")
              (cond ((> (length discharging-nodes) 1) (princ " nodes ")
                          (princ (mapcar #'inference-number discharging-nodes)))
                        (t (princ " node ") (princ (inference-number (mem1 discharging-nodes)))))
              (terpri)
              (when
                   (and (null defeatees) (member interest interests-used-in-proof))
                   (princ "                                        but no inference made by discharging this interest is used in the solution.")
                   (terpri)))
            ((and (null defeatees) (member interest interests-used-in-proof))
              (princ "                                        No inference made by discharging this interest is used in the solution.") (terpri)))
          )))
    (when (and *graph-interests* *graph-log*)
         (when *graphics-pause* (pause-graphics))  ;; wait for a character to be typed in the Listener
         (draw-i interest *og*)))

(defunction display-belief-changes  (links new-beliefs new-retractions)
   ; (setf l links nb new-beliefs nr new-retractions)
    ; (when (member (support-link 12) links) (setf l links nb new-beliefs nr new-retractions) (break))
    ;; (step (display-belief-changes l  nb nr))
    (when *monitor-assignment-tree* (monitor-assignment-tree links))
   ; (when (and (not (complete-tree *assignment-tree*)) (null *deductive-only*))
   ;      (princ links) (terpri) (break))
    (when (or *display?* *log-on*)
         (cond
           ((and (not *deductive-only*) (or new-beliefs new-retractions))
             (when (and *display?*
                                 (some #'(lambda (n) (not (some #'(lambda (L) (eq n (support-link-target L))) links)))
                                             (append new-beliefs new-retractions)))
                  (princ "---------------------------------------------------------------------------") (terpri)
                  (princ "Affected-nodes:") (terpri)
                  (princ *affected-nodes*) (terpri)
                  (princ "---------------------------------------------------------------------------") (terpri)
                  (when *discards*
                       (princ "discarding:  ") (dolist (d *discards*) (princ d) (princ "  ")) (terpri))
                  (when *creations*
                       (princ "creating:  ") (dolist (d *creations*) (princ d) (princ "  ")) (terpri))
                  (when (or *discards* *creations*)
                       (princ "---------------------------------------------------------------------------")
                       (terpri))
                  (princ "Recomputed assignment-tree:") (terpri)
                  (display-assignment-tree))
             (when (and *display?* *graphics-on*)
                  (when *graphics-pause* (pause-graphics))
                  (dolist (link links) (draw-n (support-link-target link) *og* *nodes-displayed*))
                      (when
                           (set-difference (append new-beliefs new-retractions) (mapcar #'support-link-target links))
                           (flash-nodes *affected-nodes* *og* *yellow-color* 5)))
             (when
                  new-retractions
                  (when *log-on*
                       (push "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" *reasoning-log*))
                  (when *display?* (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri)))
             (dolist (N new-retractions)
                 (cond ((or (not (some #'(lambda (L) (eq N (support-link-target L))) links))
                                  (> (length (support-links N)) 1))
                              (cond
                                ((zerop (undefeated-degree-of-support N))
                                  (when *log-on*
                                       (push (list :defeated N) *reasoning-log*))
                                  (when *display?*
                                       (princ "               ") (princ N) (princ " has become defeated.") (terpri)
                                       (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri))
                                  (when (and *display?* *graphics-on*)
                                       (let ((posi (node-position N *og*)))
                                          (when posi
                                               (when (and (boundp '*speak*) *speak*)
                                                    (speak-text "Node ")
                                                    (speak-text (write-to-string (inference-number N)))
                                                    (speak-text "has become defeated."))
                                               (draw-just-defeated-node posi *og* N)))))
                                (t
                                  (when *log-on*
                                       (push (list :decreased-support N (undefeated-degree-of-support N))
                                                   *reasoning-log*))
                                  (when *display?*
                                       (princ "               The undefeated-degree-of-support of ") (princ N)
                                       (princ " has decreased to ") (princ (undefeated-degree-of-support N)) (terpri)
                                       (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri)))))
                             ((zerop (undefeated-degree-of-support N))
                               (when *log-on*
                                    (push (list :defeated N) *reasoning-log*))
                               (when *display?*
                                    (princ "               ") (princ N) (princ " is defeated.") (terpri)
                                    (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri))
                               (when (and *display?* *graphics-on*)
                                    (when (and (boundp '*speak*) *speak*)
                                         (speak-text "Node ")
                                         (speak-text (write-to-string (inference-number N)))
                                         (speak-text "is defeated."))
                                    (let ((posi (node-position n *og*)))
                                       (cond (posi (draw-just-defeated-node posi *og* n))
                                                     (t
                                                       (draw-n n *og* *nodes-displayed*)
                                                       (push n *nodes-displayed*)
                                                       (setf posi (node-position n *og*))
                                                       (draw-just-defeated-node posi *og* n)))))))
                 ))
           ((and *display?* *graphics-on*)
             (when *graphics-pause* (pause-graphics))
             (dolist (link links) (draw-n (support-link-target link) *og* *nodes-displayed*)))))
    (when (and *display?* *graphics-on*)
         (setf *nodes-displayed* (union (mapcar #'support-link-target links) *nodes-displayed*))))

(defunction display-peripherals (x boundary nodes-used)
    (cond
      ((equal x "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (setf boundary t))
      ((listp x)
        (cond ((and (equal (mem1 x) :increased-support) (member (mem2 x) nodes-used))
                     (when (equal boundary t)
                          (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri)
                          (setf boundary nil))
                     (princ "               The undefeated-degree-of-support of ") (princ (mem2 x))
                     (princ " has increased to ") (princ (mem3 x))
                     (terpri) (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri)
                     (when *graph-log*
                          (let ((posi (node-position (mem2 x) *og*)))
                            (when posi
                                 (when (and (boundp '*speak*) *speak*)
                                      (speak-text "The undefeeted-degree-of-support of node ")
                                      (speak-text (write-to-string (inference-number (mem2 x))))
                                      (speak-text "has increased to")
                                      (speak-text (write-to-string (mem3 x))))
                                 (draw-just-undefeated-node posi *og* (mem2 x))))))
                  ((and (equal (mem1 x) :new-support) (member (mem2 x) nodes-used)
                            (not (eql (mem3 x) 1.0)))
                     (when (equal boundary t)
                          (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri)
                          (setf boundary nil))
                     (princ "               The undefeated-degree-of-support of ") (princ (mem2 x))
                     (princ " is ") (princ (mem3 x))
                     (terpri) (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri)
                     (when *graph-log*
                          (let ((posi (node-position (mem2 x) *og*)))
                            (when posi
                                 (when (and (boundp '*speak*) *speak*)
                                      (speak-text "The undefeeted-degree-of-support of node ")
                                      (speak-text (write-to-string (inference-number (mem2 x))))
                                      (speak-text "is")
                                      (speak-text (write-to-string (mem3 x))))
                                 (draw-just-undefeated-node posi *og* (mem2 x))))))
                  ((and (equal (mem1 x) :defeated) (member (mem2 x) nodes-used))
                    (when (equal boundary t)
                         (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri)
                         (setf boundary nil))
                    (princ "               ") (princ (mem2 x)) (princ " has become defeated.") (terpri)
                    (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri)
                    (when *graph-log*
                         (let ((posi (node-position (mem2 x) *og*)))
                           (when posi
                                (when (and (boundp '*speak*) *speak*)
                                     (speak-text "Node ")
                                     (speak-text (write-to-string (inference-number (mem2 x))))
                                     (speak-text "has become defeated."))
                                (draw-just-defeated-node posi *og* (mem2 x))))))
                    ((and (equal (mem1 x) :decreased-support) (member (mem2 x) nodes-used))
                      (when (equal boundary t)
                           (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri)
                           (setf boundary nil))
                      (princ "               The undefeated-degree-of-support of ") (princ (mem2 x))
                      (princ " has decreased to ") (princ (mem3 x))
                      (terpri) (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri))
                    ((and (equal (mem1 x) :answer-query) (member (mem2 x) nodes-used))
                      (princ "               ")
                      (princ "=========================================") (terpri)
                      (princ "               ") (princ "Justified belief in ")
                      (prinp (node-formula (mem2 x))) (terpri)
                     (princ "               with undefeated-degree-of-support ") (princ (mem4 x)) (terpri)
                      (princ "               ") (princ "answers ") (princ (mem3 x))
                      (terpri) (princ "               ")
                      (princ "=========================================") (terpri)
                      (when (equal (mem1 (node-formula (mem2 x))) 'protoplan-for)
                           (adopt-plan (mem2 (node-formula (mem2 x)))))
                      (when (equal (mem1 (node-formula (mem2 x))) 'plan-for)
                           (adopt-plan (mem2 (node-formula (mem2 x)))))
                      (when (and (boundp '*speak*) *speak*)
                           (speak-text "Node ")
                           (speak-text (write-to-string (inference-number (mem2 x))))
                           (speak-text "answers query ")
                           (speak-text (write-to-string (query-number (mem3 x))))))
                    ((and (equal (mem1 x) :retract-answer) (member (mem2 x) nodes-used))
                      (princ "               ")
                      (princ "=========================================") (terpri)
                      (princ "               ") (princ "Lowering the undefeated-degree-of-support of ")
                      (prinp (node-formula (mem2 x))) (terpri)
                      (princ "               ") (princ "retracts the previous answer to ")
                      (princ (mem3 x)) (terpri) (princ "               ")
                      (princ "=========================================") (terpri)
                      (when (equal (mem1 (node-formula (mem2 x))) 'plan-for)
                           (retract-plan (mem2 (node-formula (mem2 x)))))
                      (when (equal (mem1 (node-formula (mem2 x))) 'protoplan-for)
                           (retract-plan (mem2 (node-formula (mem2 x)))))
                      (when (and (boundp '*speak*) *speak*)
                           (speak-text "Node ")
                           (speak-text (write-to-string (inference-number (mem2 x))))
                           (speak-text "no longer answers query ")
                           (speak-text (write-to-string (query-number (mem3 x)))))))))
    boundary)

(defunction display-interest (interest)
    (if (numberp interest) (setf interest (interest interest)))
    (princ "                                        # ") (princ (interest-number interest)) (princ "  ")
    (when (deductive-interest interest) (princ "deductive "))
    (when (reductio-interest interest) (princ "reductio "))
    (princ "interest:")
    (terpri)
    (princ "                                           ") (prin-pretty  (interest-formula interest))
    (when (interest-supposition interest)
         (princ "    supposition: ")
         (set-prinp (interest-supposition interest)))
    (terpri)
    (when
         (some #'(lambda (L) (query-p (resultant-interest L)))
                     (right-links interest))
         (princ "                                        This is of ultimate interest") (terpri))
    (let ((L (lastmember (right-links interest))))
      (when (and L (not (query-p (resultant-interest L))))
           (princ "                                        For ")
           (when (reductio-interest (resultant-interest L)) (princ "reductio "))
           (princ "interest ")
           (princ (interest-number (resultant-interest L)))
           (princ " by ") (princ (link-rule L))
           (let ((nodes (supporting-nodes L)))
             (when nodes
                  (cond ((equal (length nodes) 1)
                              (princ " using node ")
                              (princ (inference-number (mem1 nodes))))
                            (t
                              (princ " using nodes ")
                              (print-list (mapcar
                                                #'(lambda (conclusion)
                                                      (inference-number conclusion))
                                                nodes) 40)))))
           (when (or (eq (link-rule L) goal-regression)
                             (eq (link-rule L) embedded-goal-regression)
                             (eq (link-rule L) reuse-node))
                (let ((action (e-assoc 'action (link-binding L))))
                  (when (not (interest-variable action))
                       (princ " and action ") (princ (e-assoc 'action (link-binding L))))))
           (let ((nodes (link-clues L)))
             (when nodes
                  (cond ((equal (length nodes) 1)
                              (princ " with clue ")
                              (princ (inference-number (mem1 nodes))))
                            (t
                              (princ " with clues ")
                              (print-list (mapcar
                                                #'(lambda (conclusion)
                                                      (inference-number conclusion))
                                                nodes) 40)))))
           (terpri))
      (when (discharge-condition interest)
           (princ "                                        Discharge condition: ") (terpri)
           (princ "                                             ")
           (display-discharge-condition interest L) (terpri)))
    (terpri))

(defunction display-support-link (L)
   (if (numberp L) (setf L (support-link L)))
    (let ((n (support-link-target L)))
     (princ "  # ") (princ (inference-number n)) (princ "   ")
     (when (not (equal (node-kind n) :inference)) (princ (node-kind n)) (princ "         "))
     (prin-pretty (node-formula n))
     (when (node-supposition n)
         (princ "    supposition: ") (set-prinp (node-supposition n)))
     (terpri) 
     (princ "  Inferred by support-link #") (princ (support-link-number L))
     (princ " from ") (princ-set (mapcar #'inference-number (support-link-basis L)))
     (princ " by ") (princ (support-link-rule L))
     (when (support-link-clues L)
         (princ " with clues ")
         (princ-set (mapcar #'inference-number (support-link-clues L))))
     (when (support-link-defeaters L)
         (princ "  defeaters: ") (princ-set (mapcar #'inference-number (support-link-defeaters L))))
     (terpri)
     (when (and (reason-p (support-link-rule L)) (reason-description (support-link-rule L)))
         (princ "  ") (princ (reason-description (support-link-rule L))) (terpri))
     (let ((links (remove L (support-links n))))
       (when links
           (princ "  Previously inferred by:") (terpri)
           (dolist (L* links)
              (princ "                support-link #") (princ (support-link-number L*))
              (princ " from ") (princ-set (mapcar #'inference-number (support-link-basis L*)))
              (princ " by ") (princ (support-link-rule L*))
              (when (support-link-clues L*)
                  (princ " with clues ")
                  (princ-set (mapcar #'inference-number (support-link-clues L*))))
              (when (support-link-defeaters L*)
                  (princ "  defeaters: ")
                        (princ-set (mapcar #'inference-number (support-link-defeaters L*))))
              (terpri))))
    ; (princ "  nearest-defeasible-ancestors: ")
    ; (princ (nearest-defeasible-ancestors n)) (terpri)
      (when (node-defeatees n)
           (princ "  defeatees: ")
           (princ "{ ")
           (let ((L (car (node-defeatees n))))
              (princ "link ")
              (princ (support-link-number L)) (princ " for node ")
              (princ (inference-number (support-link-target L))))
           (dolist (L (cdr (node-defeatees n)))
               (princ " , ")
               (princ "link ")
                (princ (support-link-number L)) (princ " for node ")
                (princ (inference-number (support-link-target L))))
           (princ " }") (terpri)))
    (terpri))

(defunction prin-pretty (P &optional stream)
    (cond
      ((listp P)
        (cond ((member (car P) '(plan-for protoplan-for embellished-plan-for embellished-protoplan-for
                                             plan-undermines-causal-links plan-undermines-causal-link))
                    (print-pretty P))
                  ((negationp P) (princ '~ stream) (prin-pretty (negand P) stream))
                  ((eq (car P) '@) (print-pretty (list (mem2 P) '@ (mem3 P))))
                  (t (princ (pretty P) stream))))
      (t (princ (pretty P) stream))))

;;============================ relativized quantifiers=================================

(defunction resolve-variable-conflicts (p &optional variables (reset-counter? t))
    (when reset-counter? (setf *gensym-counter* 1))
    (cond ((or (u-genp p) (e-genp p))
                (let ((var (q-variable p)))
                  (cond ((eq (mem3 p) :type)
                              (cond ((mem var variables)
                                          (let ((var* (gensym (string var))))
                                            (list (mem1 p) var* (mem3 p) (mem4 p)
                                                   (=subst var* var
                                                                 (resolve-variable-conflicts (mem5 p) variables nil)))))
                                        (t 
                                          (list (mem1 p) var (mem3 p) (mem4 p)
                                                 (resolve-variable-conflicts (mem5 p) (cons var variables) nil)))))
                            (t
                              (cond ((mem var variables)
                                          (let ((var* (gensym (string var))))
                                            (list (mem1 p) var*
                                                   (=subst var* var
                                                                 (resolve-variable-conflicts (mem3 p) variables nil)))))
                                        (t 
                                          (list (mem1 p) var
                                                 (resolve-variable-conflicts (mem3 p) (cons var variables) nil))))))))
                ((negationp p) (tilde (resolve-variable-conflicts (negand p) variables nil)))
                ((conjunctionp p)
                  (conj (resolve-variable-conflicts (conjunct1 p) variables nil)
                            (resolve-variable-conflicts (conjunct2 p) variables nil)))
                ((disjunctionp p)
                  (disj (resolve-variable-conflicts (disjunct1 p) variables nil)
                            (resolve-variable-conflicts (disjunct2 p) variables nil)))
                ((conditionalp p)
                  (condit (resolve-variable-conflicts (antecedent p) variables nil)
                            (resolve-variable-conflicts (consequent p) variables nil)))
                ((biconditionalp p)
                  (bicondit (resolve-variable-conflicts (bicond1 p) variables nil)
                            (resolve-variable-conflicts (bicond2 p) variables nil)))
                (t p)))

(defunction convert-to-prefix-form (P)
    (let ((P* nil))
      (cond ((listp P)
                  (cond 
                    ((equal (mem1 P) "~")
                      (list '~ (convert-to-prefix-form (mem2 P))))
                    ((equal (mem1 P) "?")
                      (list '? (convert-to-prefix-form (mem2 P))))
                    ((equal (mem1 P) "&")
                      (gen-conjunction (mapcar #'convert-to-prefix-form (cdr P))))
                    ((equal (mem1 P) "v")
                      (gen-disjunction (mapcar #'convert-to-prefix-form (cdr P))))
                    (t
                      (let ((mem2 (mem2 p)))
                        (cond
                          ((equal mem2 "v")
                            (list 'v (convert-to-prefix-form (mem1 P)) (convert-to-prefix-form (mem3 P))))
                          ((equal mem2 "&")
                            (list '& (convert-to-prefix-form (mem1 P)) (convert-to-prefix-form (mem3 P))))
                          ((equal mem2 "->")
                            (list '-> (convert-to-prefix-form (mem1 P)) (convert-to-prefix-form (mem3 P))))
                          ((equal mem2 "<->")
                            (list '<-> (convert-to-prefix-form (mem1 P)) (convert-to-prefix-form (mem3 P))))
                          ((equal mem2 "@")
                            (list '@ (convert-to-prefix-form (mem1 P)) (convert-to-prefix-form (mem3 P))))
                          ;;========================================================
                          ((some
                             #'(lambda (rf)
                                   (let ((m (match (mem1 rf) P (mem3 rf))))
                                     (when m
                                          (when (listp m)
                                               (setf m
                                                        (mapcar
                                                          #'(lambda (x)
                                                                (if (consp x)
                                                                  (cons (car x) (convert-to-prefix-form (cdr x)))
                                                                  (cdr x)))
                                                          m)))
                                          (setf P* (match-sublis m (mem2 rf))))))
                             *reform-list*)
                            P*)
                          ;;========================================================
                          ((listp (mem1 P))
                            (cond ((equal (mem1 (mem1 P)) "all")
                                        (cond ((eq (mem3 (mem1 P)) :type)
                                                    (list 'all (mem2 (mem1 P)) (mem3 (mem1 P)) (mem4 (mem1 P))
                                                           (convert-to-prefix-form (mem2 P))))
                                                  (t (list 'all (mem2 (mem1 P)) (convert-to-prefix-form (mem2 P))))))
                                      ((equal (mem1 (mem1 P)) "some")
                                        (cond ((eq (mem3 (mem1 P)) :type)
                                                    (list 'some (mem2 (mem1 P)) (mem3 (mem1 P)) (mem4 (mem1 P))
                                                           (convert-to-prefix-form (mem2 P))))
                                                  (t (list 'some (mem2 (mem1 P)) (convert-to-prefix-form (mem2 P))))))
                                      ((equal (mem1 (mem1 P)) "?")
                                        (list '? (mem2 (mem1 P)) (convert-to-prefix-form (mem2 P))))
                                      (t (mapcar #'convert-to-prefix-form P))))
                          (t (mapcar #'convert-to-prefix-form P)))))))
                (t P))))

(defunction pretty (p)
    (let ((p* nil))
      (cond ((stringp p) p)
                ((symbolp p) (convert-to-string p))
                ; ((identityp p) (imp (list "(" (pretty (iden1 p)) " = " (pretty (iden2 p)) ")")))
                ((negationp p) (imp (list "~" (pretty (negand p)))))
                ((u-genp p)
                  (implode
                    (cond ((eq (mem3 P) :type)
                                (list "(all" " " (convert-to-string (mem2 p)) " " (convert-to-string (mem3 p))
                                        " " (convert-to-string (mem4 p)) ")" (pretty (mem5 p))))
                              (t (list "(all" " " (convert-to-string (mem2 p))
                                         ")" (pretty (mem3 p)))))))
                ((e-genp p)
                  (implode
                    (cond ((eq (mem3 P) :type)
                                (list "(some" " " (convert-to-string (mem2 p)) " " (convert-to-string (mem3 p))
                                        " " (convert-to-string (mem4 p)) ")" (pretty (mem5 p))))
                              (t (list "(some" " " (convert-to-string (mem2 p))
                                         ")" (pretty (mem3 p)))))))
                ((?-genp p)
                  (implode
                    (list "(?" " " (convert-to-string (mem2 p))
                           ")" (pretty (mem3 p)))))
                ((and (listp p) (not (listp (cdr p)))) (write-to-string p))
                ((listp p)
                  (let ((mem1 (mem1 p)))
                    (cond
                      ((equal mem1 'v)
                        (imp (list "(" (pretty (mem2 P)) " " "v" " " (pretty (mem3 P)) ")")))
                      ((equal mem1 '&)
                        (imp (list "(" (pretty (mem2 P)) " " "&" " " (pretty (mem3 P)) ")")))
                      ((equal mem1 '->)
                        (imp (list "(" (pretty (mem2 P)) " " "->" " " (pretty (mem3 P)) ")")))
                      ((equal mem1 '<->)
                        (imp (list "(" (pretty (mem2 P)) " " "<->" " " (pretty (mem3 P)) ")")))
                      ((equal mem1 '@)
                        (imp (list "(" (pretty (mem2 P)) " " "@" " " (pretty (mem3 P)) ")")))
                      ((equal mem1 '?) (imp (list "(? " (pretty (mem2 P)) ")")))
                  ;    ((equal mem1 'open) (imp (list "(" (pretty (mem2 P)) " " (pretty (mem3 P)) ")")))
                  ;    ((equal mem1 'closed) (imp (list "[" (pretty (mem2 P)) " " (pretty (mem3 P)) "]")))
                  ;    ((equal mem1 'clopen) (imp (list "(" (pretty (mem2 P)) " " (pretty (mem3 P)) "]")))
                    ;  ((equal mem1 'protoplan-for)
                    ;    (imp (list "(protoplan-for " (pretty (mem2 P)) " " (pretty (mem3 P)) ")")))
                         ; (append (list "(protoplan-for " (pretty (mem2 P)) " " (pretty (mem3 P)) " { ")
                         ;                (unionmapcar #'(lambda (x) (list (pretty x) " ")) (mem4 P)) '("})"))))
                    ; ((equal mem1 'embellished-protoplan-for)
                    ;   (imp 
                    ;     (append (list "(embellished-protoplan-for " (pretty (mem2 P)) " { ")
                    ;                     (unionmapcar #'(lambda (x) (list (pretty x) " ")) (mem3 P)) '("} ")
                    ;                     (list (pretty (mem4 P)) ")"))))
                                       ;  " { ")
                                       ;  (unionmapcar #'(lambda (x) (list (pretty x) " ")) (mem5 P)) '("})"))))
                      ;;========================================================
                      ((some #'(lambda (rf)
                                         (let ((m (match (mem2 rf) P (mem3 rf))))
                                           (when m
                                                (when (listp m)
                                                     (setf m
                                                              (mapcar
                                                                #'(lambda (x) (if (consp x) (cons (car x) (pretty (cdr x))) (cdr x))) m)))
                                                (setf P* (match-sublis m (mem1 rf))))))
                                   *reform-list*)
                        (remove-if-equal #\" (pretty P*)))
                      ;;========================================================
                      (t
                        (imp (cons "(" (append (pretty-cons p) (list ")"))))))))
                (t (write-to-string p))
                )))

(def-forwards-reason RELATIVIZED-UI
    :conclusions P*
    :forwards-premises
        "(all x :type type) P)"
        "(:type object type)"
        "(define P* (subst object x P))"
    :variables  x type object P P*)

;;============================ interest priorities ====================================
(proclaim '(special *answered-priority*))

(setf *answered-priority* .005)

(defunction affected-items
    (new-beliefs new-retractions altered-interests altered-queries &optional display)
    ;; (affected-items nb nr ai aq t)
    (let* ((affected-nodes (append new-beliefs new-retractions))
              (affected-interests
                (union altered-interests (mapcar #'query-interest altered-queries)))
              (new-affected-nodes affected-nodes)
              (new-affected-interests affected-interests))
      (when display
         (princ "affected-nodes: ") (princ affected-nodes) (terpri)
         (princ "affected-interests: ") (princ affected-interests) (terpri))
      (dolist (query altered-queries)
          (pushnew (query-interest query) altered-interests))
      (loop
        (when display (princ "=======") (terpri))
        (dolist (node new-affected-nodes)
            (pull node new-affected-nodes)
            (when display (terpri) (princ "from ") (princ node) (terpri))
            (dolist (n (node-consequences node))
                (when (not (member n affected-nodes))
                (when display (princ "     ") (princ n) (princ " node-consequence") (terpri))
                      (push n affected-nodes)
                      (push n new-affected-nodes)))
            (dolist (in (generated-interests node))
                (when (not (member in affected-interests))
                (when display (princ "     ") (princ in) (princ " generated-interest") (terpri))
                      (push in affected-interests)
                      (push in new-affected-interests)))
            (when (and (listp (node-formula node))
                                (or (eq (car (node-formula node)) 'plan-for)
                                      (eq (car (node-formula node)) 'embellished-plan-for)))
                 (dolist (x (discharged-interests node))
                     (let ((in (car x)))
                       (when (not (member in affected-interests))
                            (when display (princ "     ") (princ in) (princ " discharged protoplan interest") (terpri))
                            (push in affected-interests)
                            (push in new-affected-interests)))))
            (dolist (in (generated-defeat-interests node))
                (when (not (member in affected-interests))
                (when display (princ "     ") (princ in) (princ " generated-defeat-interest") (terpri))
                      (push in affected-interests)
                      (push in new-affected-interests)))
            (when (eq (node-justification node) :reductio-supposition)
                 (dolist (in *direct-reductio-interests*)
                     (when (not (member in affected-interests))
                          (when display (princ "     ") (princ in) (princ " direct reductio interest") (terpri))
                          (push in affected-interests)
                          (push in new-affected-interests)))))
        (dolist (interest new-affected-interests)
            (pull interest new-affected-interests)
            (when display (terpri) (princ "from ") (princ interest) (terpri))
            (dolist (L (left-links interest))
                (let ((in (link-interest L)))
                  (when (not (member in affected-interests))
                 (when display (princ "     ") (princ in) (princ " from left link") (terpri))
                       (push in affected-interests)
                       (push in new-affected-interests))))
            (dolist (n (generated-suppositions interest))
                (when (not (member n affected-nodes))
                (when display (princ "     ") (princ n) (princ " generated-supposition") (terpri))
                      (push n affected-nodes)
                      (push n new-affected-nodes))))
        (when (and (null new-affected-nodes) (null new-affected-interests))
                (when display (princ "Affected-nodes: ") (princ affected-nodes) (terpri))
                (when display (princ "Affected-interests: ") (princ affected-interests) (terpri) (terpri))
             (return (list affected-nodes affected-interests))))))

#|
(find-if #'(lambda (i)
                  (some #'(lambda (L)
                                   (some #'(lambda (link) (equal (resultant-interest link) i))
                                               (right-links (resultant-interest L))))
                              (right-links i)))
            af)
|#

(defunction i-preferred (node1 node2)
    (or (and (eq (item-kind node2) :interest)
                  (eql (interest-priority (enqued-item node2)) *answered-priority*))
          (> (degree-of-preference node1) (degree-of-preference node2))
          (and (eql (degree-of-preference node1) (degree-of-preference node2))
                   (eq (item-kind node1) :conclusion) (eq (item-kind node2) :interest))))

(defunction recompute-priorities (new-beliefs new-retractions altered-interests altered-queries  &optional display)
    ; (when (eql *cycle* 79) (setf nb new-beliefs nr new-retractions ai altered-interests aq altered-queries)  (break))
    ;; (step (recompute-priorities nb nr ai aq))
     ;; (recompute-priorities nb nr ai aq t)
    (let* ((affected-items (affected-items new-beliefs new-retractions altered-interests altered-queries display))
              (affected-nodes (mem1 affected-items))
              (affected-interests (mem2 affected-items))
              (altered-queue nil))
      (dolist (query altered-queries)
          (let ((interest (query-interest query)))
            (pull interest affected-interests)
            (cond ((and (answered? query)
                                (not (member query *permanent-ultimate-epistemic-interests*)))
                        (setf (interest-priority interest) *answered-priority*)
                        (when display (princ "soft-cancelling query interest ")
                             (princ interest) (terpri)))
                      (t (setf (interest-priority interest) (maximum-degree-of-interest interest))
                          (when display (princ "reinstating query interest ")
                             (princ interest) (terpri))))))
      ; (dolist (N new-retractions)
      (dolist (N affected-nodes)
          (when (every
                       #'(lambda (L)
                             (some
                               #'(lambda (d)
                                     (and (not (equal (node-formula d) (neg (node-formula N))))
                                              (or (null (support-link-strength L))
                                                    (<= (support-link-strength L)
                                                           (undefeated-degree-of-support d)))))
                               (support-link-defeaters L)))
                       (support-links N))
               (pull N affected-nodes)
            (when display (princ "soft-cancelling undercut node ")
                       (princ N) (terpri))
               (setf (discounted-node-strength N) *answered-priority*)
               (let ((Q (node-queue-node N)))
                 (when Q (pushnew Q altered-queue))))
          (when (zerop (undefeated-degree-of-support N))
               (dolist (in (generated-defeat-interests N))
                   (when (member in affected-interests)
                        (pull in affected-interests)
                        (setf (interest-priority in) *answered-priority*)
                        (when display (princ "soft-cancelling generated-defeat-interest ")
                             (princ in) (terpri))
                        (let ((Q (interest-queue-node in)))
                          (when Q (pushnew Q altered-queue)))))))
      (dolist (node affected-nodes)
       (when display (terpri) (princ "from ") (princ node) (terpri))
          (when (listp (node-formula node))
               (cond ((zerop (undefeated-degree-of-support node))
                           (when (or (eq (car (node-formula node)) 'plan-for)
                                             (eq (car (node-formula node)) 'embellished-plan-for))
                                (dolist (x (discharged-interests node))
                                    (let ((in (car x)))
                                      (when (and (member in affected-interests)
                                                          (every
                                                            #'(lambda (n) (zerop (undefeated-degree-of-support n)))
                                                            (discharging-nodes in)))
                                           (pull in affected-interests)
                                           (when display
                                     (princ "     requeueing no longer discharged plan interest ")
                                     (princ in) (terpri))
                                           (let ((Q (interest-queue-node in)))
                                             (when Q (pushnew Q altered-queue))))))))
                         ((or (eq (car (node-formula node)) 'plan-for)
                                (eq (car (node-formula node)) 'embellished-plan-for))
                           (dolist (x (discharged-interests node))
                               (let ((in (car x)))
                                 (when (not (eql (interest-priority in) *answered-priority*))
                                      (pull in affected-interests)
                                      (setf (interest-priority in) *answered-priority*)
                             (when display
                                 (princ "     requeueing newly discharged plan interest ")
                                 (princ in) (terpri))
                                       (let ((Q (interest-queue-node in)))
                                         (when Q (pushnew Q altered-queue)))))))))
          (cond ((zerop (undefeated-degree-of-support node))
                      ;; If a node is defeated, its discounted-node-strength is *base-priority*.
                      (pull node affected-nodes)
                 (when display
                     (princ "     requeueing defeated node ") (princ node)
                     (princ " with discounted-node-strength ")
                     (princ (discounted-node-strength node)) (terpri))
                      (setf (discounted-node-strength node) *base-priority*)
                      (let ((Q (node-queue-node node)))
                        (when Q (pushnew Q altered-queue))))
                    ((null (generating-interests node))
                      ;; If an undefeated node has an empty list of generating-interests, its 
                      ;; discounted-node-strength is the maximum  (over its node-arguments) 
                      ;; of the product of the discount-factor of the support-link-rule of the last 
                      ;; support-link in the argument and the strength of the argument.  
                      ;; (This case includes all non-suppositional nodes.)
                      (pull node affected-nodes)
                 (when display
                     (princ "     requeueing undefeated affected node with no generating-interests ")
                     (princ node) (princ " with discounted-node-strength ")
                     (princ (discounted-node-strength node)) (terpri))
                      (let ((Q (node-queue-node node)))
                        (when Q (pushnew Q altered-queue))))))
      ;---------------------------------
      (loop
        (when display (princ "=======") (terpri))
        ; (when (eql *cycle* 89) (setf af affected-interests) (break))
        ; (p-print (setf af affected-interests))
        (when (and (null affected-nodes) (null affected-interests)) (return))
        (let ((changes? nil))
          ; ===============
          ;; For each altered-node or altered-interest whose discounted-node-strength 
          ;; or interest-priority can be computed without appealing to any other altered-nodes 
          ;; or altered-interests, we do so and remove them from the lists of altered-nodes 
          ;; and altered-interests.  Repeat this step until no further nodes or interests can be 
          ;; removed.  If there are no generation-cycles, this will get them all, but if there are 
          ;; cycles, some may remain.
          (loop
            (when display (princ "          ===============") (terpri))
            (setf changes? nil)
            (dolist (node affected-nodes)
                (let ((reductio-interests (generating-reductio-interests node))
                        (non-reductio-interests (generating-non-reductio-interests node)))
                  (when (and (not (some #'(lambda (in) (member in affected-interests))
                                                          reductio-interests))
                                      (not (some #'(lambda (in) (member in affected-interests))
                                                          non-reductio-interests)))
                       (setf changes? t)
                       (pull node affected-nodes)
                       ;; If a node is a supposition, its discounted-node-strength is the maximum of:
                       ;;  (1)  the product of *reductio-discount* and the maximum of the 
                       ;;  interest-priorities of the generating-interests for which it is a 
                       ;;  reductio-supposition; and
                       ;;  (2)  the interest-priorities of the generating-interests for which it is 
                       ;;  not a reductio-supposition.
                       (setf (discounted-node-strength node)
                                (max
                                  (* *reductio-discount*
                                       (maximum0 (mapcar #'interest-priority reductio-interests)))
                                  (maximum0 (mapcar #'interest-priority non-reductio-interests))))
                       (let ((Q (node-queue-node node)))
                         (when display (princ "               requeuing supposition ") (princ node)
                             (princ " with discounted-node-strength ")
                             (princ (discounted-node-strength node)) (terpri))
                         (when Q (pushnew Q altered-queue))))))
            (dolist (interest affected-interests)
                (let ((GN (broadly-generating-nodes interest))
                        (links (subset #'(lambda (L) (null (link-defeat-status L))) (right-links interest))))
                  (cond ((and (null GN) (null links))
                              ;; If an interest has neither generating-nodes nor undefeated right-links,
                              ;;  its interest-priority is *defeater-priority*  (This includes interest in defeaters.)
                              (setf changes? t)
                              (pull interest affected-interests)
                              (setf (interest-priority interest) *defeater-priority*)
                              (when display
                           (princ "               requeuing interest with broadly generating nodes but not undefeated right links ")
                           (princ interest) (princ " with interest-priority ")
                           (princ (interest-priority interest)) (terpri))
                              (let ((Q (interest-queue-node interest)))
                                (when Q (pushnew Q altered-queue))))
                            ((and (not (some #'(lambda (n) (member n affected-nodes)) GN))
                                      (not (some #'(lambda (link) (member (resultant-interest link) affected-interests)) links)))
                              ;; Otherwise, the interest-priority is the maximum of:
                              ;;  (1)  the discounted-node-strengths of its generating-nodes that are 
                              ;;  not reductio-suppositions;
                              ;;  (2)  the product of *reductio-interest* and the maximum of the 
                              ;;  discounted-node-strengths of its generating-nodes that are 
                              ;;  reductio-suppositions;
                              ;;  (3)  for each of its right-links, the product 
                              ;;  of the discount-factor of the link-rule and the interest-priority of the 
                              ;;  resultant-interest.
                              (setf changes? t)
                              (pull interest affected-interests)
                              (setf (interest-priority interest)
                                       (maximum
                                         (append
                                           (mapcar
                                             #'(lambda (n)
                                                   (if (eq (node-justification n) :reductio-supposition)
                                                     (* *reductio-interest* (compute-discounted-node-strength n))
                                                     (compute-discounted-node-strength n)))
                                             GN)
                                           (mapcar
                                             #'(lambda (L)
                                                   (if (eq (link-rule L) :answer)
                                                     (query-strength (resultant-interest L))
                                                     (* (discount-factor (link-rule L))
                                                          (interest-priority (resultant-interest L)))))
                                             links))))
                              (when display
                           (princ "               requeuing interest with no affected broadly generating odes and no undefeated right links with affected resultant interests ")
                           (princ interest) (princ " with interest-priority ")
                           (princ (interest-priority interest)) (terpri))
                              (let ((Q (interest-queue-node interest)))
                                (when Q (pushnew Q altered-queue)))))))
            (when (and (null affected-nodes) (null affected-interests)) (return))
            (when (null changes?) (return)))
          ; ===============
          (when (and (null affected-nodes) (null affected-interests)) (return))
          ;; For any remaining nodes or interests, we want to compute their discounted-
          ;; nodes-strengths and interest-priorities just in terms of the nodes and interests 
          ;; not involved in the cycles.  Cycles arise from direct-reductio-interests that also 
          ;; have other sources and reductio-suppositions that are also non-reductio-
          ;; suppositions.  So for any such interests and suppositions, compute their 
          ;; interest-priorities and discounted-node-strengths just in terms of those of their 
          ;; sources that are no longer contained in the lists of altered-nodes or altered-interests.
          (dolist (node affected-nodes)
              (let ((reductio-interests (generating-reductio-interests node))
                      (non-reductio-interests (generating-non-reductio-interests node)))
                (when (not (some #'(lambda (in) (member in affected-interests))
                                               non-reductio-interests))
                     (setf changes? t)
                     (pull node affected-nodes)
                     ;; If a node is a supposition, its discounted-node-strength is the maximum of:
                     ;;  (1)  the product of *reductio-discount* and the maximum of the 
                     ;;  interest-priorities of the generating-interests for which it is a 
                     ;;  reductio-supposition; and
                     ;;  (2)  the interest-priorities of the generating-interests for which it is 
                     ;;  not a reductio-supposition.
                     (setf (discounted-node-strength node)
                              (max
                                (* *reductio-discount*
                                     (maximum0
                                       (mapcar #'interest-priority
                                                      (subset #'(lambda (in) (not (member in affected-interests)))
                                                                    reductio-interests))))
                                (maximum0 (mapcar #'interest-priority non-reductio-interests))))
                 (when display
                     (princ "     requeueing supposition ")
                     (princ node) (princ " with discounted-node-strength ")
                     (princ (discounted-node-strength node)) (terpri))
                     (let ((Q (node-queue-node node)))
                       (when Q (pushnew Q altered-queue))))))
          (dolist (interest affected-interests)
              (let ((GN (broadly-generating-nodes interest))
                      (links (subset #'(lambda (L) (null (link-defeat-status L))) (right-links interest))))
                (when (and (direct-reductio-interest interest)
                                    (not (some #'(lambda (n)
                                                             (and (not (eq (node-justification n) :reductio-supposition))
                                                                      (member n affected-nodes))) GN))
                                    (not (some #'(lambda (in) (member in affected-interests)) links)))
                     (setf changes? t)
                     (pull interest affected-interests)
                     ;; If an interest has either generating-nodes or undefeated right-links
                     ;;  the interest-priority is the maximum of:
                     ;;  (1)  the discounted-node-strengths of its generating-nodes that are 
                     ;;  not reductio-suppositions;
                     ;;  (2)  the product of *reductio-interest* and the maximum of the 
                     ;;  discounted-node-strengths of its generating-nodes that are 
                     ;;  reductio-suppositions;
                     ;;  (3)  for each of its right-links, the product 
                     ;;  of the discount-factor of the link-rule and the interest-priority of the 
                     ;;  resultant-interest.
                     (setf (interest-priority interest)
                              (maximum
                                (cons
                                  (* *reductio-interest*
                                       (maximum0
                                         (mapcar #'compute-discounted-node-strength
                                                        (subset
                                                          #'(lambda (n)
                                                                (and (eq (node-justification n) :reductio-supposition)
                                                                         (not (member n affected-nodes)))) GN))))
                                  (append
                                    (mapcar #'compute-discounted-node-strength
                                                   (subset
                                                     #'(lambda (n)
                                                           (not (eq (node-justification n) :reductio-supposition)))
                                                     GN))
                                    (mapcar
                                      #'(lambda (L)
                                            (if (eq (link-rule L) :answer)
                                              (query-strength (resultant-interest L))
                                              (* (discount-factor (link-rule L))
                                                   (interest-priority (resultant-interest L)))))
                                      links)))))
                 (when display
                     (princ "     requeueing interest with broadly-generating-nodes or undefeated right links ")
                     (princ interest) (princ " with interest-priority ")
                     (princ (interest-priority interest)) (terpri))
                     (let ((Q (interest-queue-node interest)))
                       (when Q (pushnew Q altered-queue))))))))
      ;---------------------------------
     (when display (princ "----------------") (terpri))
      (dolist (Q altered-queue)
          (cond ((eq (item-kind Q) :conclusion)
                      (setf (discounted-strength Q)
                               (compute-discounted-node-strength (enqued-item Q)))
                      (setf (degree-of-preference Q)
                               (/ (discounted-strength Q) (item-complexity Q)))
                      (let ((n (enqued-item Q)))
                        (cond ((and (listp (node-formula n))
                                            (or (eq (car (node-formula n)) 'embellished-protoplan-for)
                                                  (eq (car (node-formula n)) 'embellished-plan-for)
                                                  (eq (car (node-formula n)) 'plan-undermines-causal-links)
                                                  ))
                                    (cond ((and (every #'(lambda (in) (equal (interest-priority in) *answered-priority*))
                                                                    (enabling-interests n))
                                                        (every #'(lambda (L)
                                                                          (let ((R (support-link-rule L)))
                                                                            (and (backwards-reason-p R) (backwards-premises R))))
                                                                    (support-link n)))
                                    (when display
                                        (princ "     unqueueing plan node with softly-cancelled enabling interests ")
                                        (princ n) (terpri))
                                                (pull Q *inference-queue*))
                                              (t
                                    (when display
                                        (princ "     requeueing plan node ") (princ n) (terpri))
                                                (setf *inference-queue*
                                                         (ordered-insert Q (remove Q *inference-queue*) #'i-preferred)))))
                                  (t
                           (when display
                               (princ "     requeueing non-plan node ") (princ n) (terpri))
                                    (setf *inference-queue*
                                             (ordered-insert Q (remove Q *inference-queue*) #'i-preferred))))))
                    ((not (cancelled-interest (enqued-item Q)))
                      (setf (discounted-strength Q) (interest-priority (enqued-item Q)))
                      (setf (degree-of-preference Q)
                               (/ (discounted-strength Q) (item-complexity Q)))
                      (let ((n (enqued-item Q)))
                        (cond ((and (listp (interest-formula n))
                                            (or (eq (car (interest-formula n)) 'protoplan-for)
                                                  (eq (car (interest-formula n)) 'embellished-protoplan-for)
                                                  (eq (car (interest-formula n)) 'embellished-plan-for)
                                                  (eq (car (interest-formula n)) 'plan-undermines-causal-links)
                                                  ))
                                    (cond ((eql (interest-priority n) *answered-priority*)
                                    (when display
                                        (princ "     unqueueing softly-cancelled plan interest ")
                                        (princ n) (terpri))
                                                (pull Q *inference-queue*))
                                              (t
                                    (when display
                                        (princ "     requeueing plan interest ") (princ n) (terpri))
                                                (setf *inference-queue*
                                                         (ordered-insert Q (remove Q *inference-queue*) #'i-preferred)))))
                                  (t
                           (when display
                               (princ "     requeueing non-plan interest ") (princ n) (terpri))
                                    (setf *inference-queue*
                                             (ordered-insert Q (remove Q *inference-queue*) #'i-preferred))))))))))

;;=============================== decided-plans =============================

;(defunction decided-node (node)
;    (every
;      #'(lambda (in)
;            (and (processed-interest in)
;                     (every #'decided-node (discharging-nodes in))))
;      (generated-defeat-interests node)))
;
;(defunction processed-interest (interest)
;    (and (null (interest-queue-node interest))
;             (every #'(lambda (L) (processed-interest (link-interest L)))
;                         (left-links interest))))

(defstruct (interest (:print-function print-interest)
                                    (:conc-name nil))   ; "An interest-graph-node"
    (interest-number 0)
    (interest-sequent nil)
    (interest-formula nil)
    (interest-supposition nil)
    (right-links nil)
    (left-links nil)
    (degree-of-interest *base-priority*)
    (last-processed-degree-of-interest nil)
    (interest-defeat-status nil)
    (discharged-degree nil)  ;; used in computing priorities
    (deductive-interest nil)
    (cancelled-interest nil)
    (interest-queue-node nil)
    (interest-i-list nil)
    (maximum-degree-of-interest 0)
    (interest-defeatees nil)
    (reductio-interest nil)
    (direct-reductio-interest nil)
    (generated-suppositions nil)
    (generating-nodes nil)
    (interest-priority 0)
    (interest-variables nil)
    (discharge-condition nil)  ;;a function of node, unifier, and interest-link
    (interest-supposition-variables nil)
    (cancelling-node nil)
    (discharging-nodes nil)
    (interest-supposition-nodes nil)
    (generated-interest-schemes nil)
    (defeater-binding nil)
    (generating-defeat-nodes nil)
    (cancelled-left-links nil)
   (non-reductio-interest t)
    (anchored-nodes nil)
    (text-discharge-condition nil)  ;; a text statement of the discharge condition
    (enabled-nodes nil)  ;; the nodes for which this is an enabling-interest
    (decision-plans nil)  ;; the nodes this interest is relevant to deciding on
    )

(defunction make-undercutting-defeater (base formula supposition antecedent* link reverse-binding)
    ; (when (eql link 64) (setf b base f formula s supposition a antecedent* l link rb reverse-binding) (break))
    ; (setf b base f formula s supposition a antecedent* l link rb reverse-binding) (break)
    ;; (step (make-undercutting-defeater b f s a l rb))
    (let* ((defeater (make-@ (gen-conjunction base) formula))
              (undercutting-defeater
                (cond (antecedent* (conj defeater antecedent*))
                          (t defeater)))
              (undercutting-variables
                (formula-node-variables undercutting-defeater)))
      (multiple-value-bind
           (undercutting-interest i-list)
           (interest-for (list supposition undercutting-defeater)
                                 undercutting-variables nil nil)
           (cond ((null undercutting-interest)
                       (setf undercutting-interest
                                (make-interest
                                  :interest-number (incf *interest-number*)
                                  :interest-sequent (list supposition undercutting-defeater)
                                  :interest-formula undercutting-defeater
                                  :interest-supposition supposition
                                  :interest-variables undercutting-variables
                                  :interest-supposition-variables (supposition-variables supposition)
                                  :interest-defeatees (list link)
                                  :interest-priority *defeater-priority*
                                  :defeater-binding (support-link-binding link)
                                  :generating-defeat-nodes (list (support-link-target link))
                                  :decision-plans
                                  (when (eq (support-link-rule link) protoplan)
                                       (list (mem2 (node-formula (support-link-target link)))))
                                  ))
                       (store-interest undercutting-interest i-list)
                       (pushnew undercutting-interest (generated-defeat-interests (support-link-target link)))
                       (when *display?* 
                            (display-interest undercutting-interest)
                            (princ 
                              "                                        Of interest as defeater for support-link ")
                            (princ (support-link-number link)) (terpri) (terpri))
                       (when *log-on* (push undercutting-interest *reasoning-log*))
                       (when (and *display?* *graphics-on* *graph-interests*)
                            (draw-i undercutting-interest *og*))
                       (instantiate-defeater
                         undercutting-interest defeater antecedent* link reverse-binding))
                     (t 
                       (readopt-interest undercutting-interest (list link))
                       (push undercutting-interest (generated-defeat-interests (support-link-target link)))
                       (push (support-link-target link) (generating-defeat-nodes undercutting-interest))
                       (when (eq (support-link-rule link) protoplan)
                            (push (mem2 (node-formula (support-link-target link)))
                                      (decision-plans undercutting-interest)))
                       (dolist (in (discharged-interests (support-link-target link)))
                           (dolist (p (decision-plans (car in)))
                               (pushnew p (decision-plans undercutting-interest))))
                       (setf (interest-defeatees undercutting-interest)
                                (cons link (interest-defeatees undercutting-interest)))))
           (dolist (node (unifying-nodes undercutting-interest))
               (when (subsetp= (node-supposition node) supposition)
                    (when *display?*
                         (princ "  Node # ") (princ (inference-number node))
                         (princ " defeats link # ")
                         (princ (support-link-number link)) (terpri))
                    (pushnew node (support-link-defeaters link))
                    (pushnew node (discharging-nodes undercutting-interest))
                    (pushnew link (node-defeatees node)))))))

(defunction make-rebutting-defeater (variables base formula supposition antecedent* link)
    (let ((rebutting-defeater
              (cond (antecedent* (conj antecedent* (conj (gen-conjunction base) (neg formula))))
                        (variables (conj (gen-conjunction base) (neg formula)))
                        (t (neg formula))))
            (rebutting-variables
              (node-variables (support-link-target link))))
      (multiple-value-bind
           (rebutting-interest i-list)
           (interest-for (list supposition rebutting-defeater) rebutting-variables nil nil)
           (cond ((null rebutting-interest)
                       (setf rebutting-interest
                                (make-interest
                                  :interest-number (incf *interest-number*)
                                  :interest-sequent (list supposition rebutting-defeater)
                                  :interest-formula rebutting-defeater
                                  :interest-supposition supposition
                                  :interest-variables rebutting-variables
                                  :interest-supposition-variables (supposition-variables supposition)
                                  :interest-defeatees (list link)
                                  :interest-priority *defeater-priority*
                                  :generating-defeat-nodes (list (support-link-target link))
                                  :decision-plans
                                  (when (eq (support-link-rule link) protoplan)
                                       (list (mem2 (node-formula (support-link-target link)))))))
                       (store-interest rebutting-interest i-list)
                       (pushnew rebutting-interest (generated-defeat-interests (support-link-target link)))
                       (when *display?* 
                            (display-interest rebutting-interest)
                            (princ 
                              "                                        Of interest as defeater for support-link ")
                            (princ (support-link-number link)) (terpri) (terpri))
                       (when *log-on* (push rebutting-interest *reasoning-log*))
                       (when (and *display?* *graphics-on* *graph-interests*)
                            (draw-i rebutting-interest *og*))
                       (queue-interest
                         rebutting-interest *defeater-priority*))
                     (t 
                       (readopt-interest rebutting-interest (list link))
                       (push rebutting-interest (generated-defeat-interests (support-link-target link)))
                       (push (support-link-target link) (generating-defeat-nodes rebutting-interest))
                       (when (eq (support-link-rule link) protoplan)
                                       (push (mem2 (node-formula (support-link-target link)))
                                                 (decision-plans rebutting-interest)))
                       (dolist (in (discharged-interests (support-link-target link)))
                           (dolist (p (decision-plans (car in)))
                               (pushnew p (decision-plans rebutting-interest))))
                       (setf (interest-defeatees rebutting-interest)
                                (cons link (interest-defeatees rebutting-interest)))))
           (dolist (node (unifying-nodes rebutting-interest))
               (when (subsetp= (node-supposition node) supposition)
                    (when *display?*
                         (princ "  Node # ") (princ (inference-number node))
                         (princ " defeats link # ")
                         (princ (support-link-number link)) (terpri))
                    (pushnew node (support-link-defeaters link))
                    (pushnew node (discharging-nodes rebutting-interest))
                    (pushnew link (node-defeatees node)))))))

(defunction defeater-priority (interest)
    (declare (ignore interest))
    *defeater-priority*)

(defunction instantiate-defeater (undercutting-interest defeater antecedent* link reverse-binding)
   ; (setf u undercutting-interest d defeater a antecedent* l link r reverse-binding) (break)
    ;; (step (instantiate-defeater u d a l r))
    (let ((binding (match-sublis reverse-binding (support-link-binding link) :test 'equal)))
      (cond
        (antecedent*
          (let*
            ((i-link
               (construct-initial-interest-link
                 nil nil adjunction undercutting-interest 0 *defeater-priority*
                 (list (cons 'p defeater) (cons 'q antecedent*)) (interest-supposition undercutting-interest)))
              (interest (link-interest i-link)))
            (dolist (reason (undercutting-defeaters (support-link-rule link)))
                (when (and (member reason *backwards-reasons*) (funcall* (reason-condition reason) binding))
                     (let ((supposition (interest-supposition interest)))
                       (cond
                         ((forwards-premises reason)
                           (construct-interest-scheme
                             reason nil interest binding nil (forwards-premises reason) nil 1
                             *defeater-priority* supposition))
                         (t (make-backwards-inference 
                               reason binding interest 1 *defeater-priority* nil nil nil supposition))))))))
        (t
          (dolist (reason (undercutting-defeaters (support-link-rule link)))
              (when (and (member reason *backwards-reasons*) (funcall* (reason-condition reason) binding))
                   (let ((supposition (interest-supposition undercutting-interest)))
                     (cond
                       ((forwards-premises reason)
                         (construct-interest-scheme
                           reason nil undercutting-interest binding nil (forwards-premises reason) nil 1
                           *defeater-priority* supposition))
                       (t (make-backwards-inference 
                             reason binding undercutting-interest 1 *defeater-priority* nil nil nil supposition))))))))))

(defunction compute-link-interest
    (link condition1 condition2 degree max-degree depth priority &optional new-vars text-condition)
    (declare (ignore new-vars))
    ; (setf l link c1 condition1 c2 condition2 d degree md max-degree dp depth p priority nv new-vars) ; (break))
    ;; (step (compute-link-interest l c1 c2 d md dp p nv))
    (let* ((interest-priority
                (if priority
                  (* priority (discount-factor (link-rule link)))
                  (interest-priority (resultant-interest link))))
              (vars (formula-node-variables (link-interest-formula link))))
      (multiple-value-bind
           (interest i-list match match*)
           (interest-for (list (link-supposition link) (link-interest-formula link)) vars condition1 link)
           (cond
             (interest
               (setf (degree-of-interest interest) (min (degree-of-interest interest) degree))
               (setf (maximum-degree-of-interest interest)
                        (max (maximum-degree-of-interest interest) max-degree))
               (when (not (reductio-interest interest))
                    (setf (reductio-interest interest) (reductio-interest (resultant-interest link))))
               (setf (interest-priority interest) (max (interest-priority interest) interest-priority))
               (let ((gn (link-generating-node link)))
                 (when gn
                      (pushnew gn (generating-nodes interest))
                      (push interest (generated-interests gn))))
               (if (right-links interest)
                 (setf (right-links interest) (reverse (cons link (reverse (right-links interest)))))
                 (setf (right-links interest) (list link)))
             ;  (setf (interest-depth interest)
             ;           (min (interest-depth interest) (1+ (interest-depth (resultant-interest link)))))
               (setf (interest-match link) match)
               (setf (interest-reverse-match link) match*)
               (readopt-interest interest nil))
             (t
               (setf interest
                        (construct-new-interest-for
                          link vars condition2 degree max-degree depth i-list text-condition))

               ;; (when *display?* (terpri) (princ (car (link-instantiations link))) (terpri) (terpri))

              ; (let ((i-depth (interest-depth (resultant-interest link))))
              ;   (setf (interest-depth interest) (1+ i-depth))
              ;   (setf (interest-priority interest) (* interest-priority (/  i-depth (1+ i-depth)))))
               
               (setf (interest-priority interest) interest-priority)
               ))
           (setf (link-interest link) interest)
           (dolist (p (decision-plans (resultant-interest link)))
               (pushnew p (decision-plans interest)))
           )))

(defunction decided-node (node)
    (and (every #'decided-interest (generated-defeat-interests node))
             (every #'(lambda (L)
                               (every #'decided-node (support-link-defeaters L)))
                         (support-links node))))

(defunction decided-interest (interest)
    (and (null (interest-queue-node interest))
             (every #'decided-node (discharging-nodes interest))
             (every #'(lambda (L)
                               (decided-interest (link-interest L)))
                         (left-links interest))))

(defunction SOLVE-PLANNING-PROBLEM ()
    (let ((pp *print-pretty*)
            (red *use-reductio*))
      (setf *print-pretty* nil)
      (setf *use-reductio* nil)
      (gc)
      (unwind-protect
          (progn
              (display-planning-settings)
              (setf *premises* **premises**)
              (setf *plan-number* 0)
              (setf *plan-node-number* 0)
              (setf *start* (make-plan-node))
              (setf *plans* nil)
              (setf *plan-nodes* (list *start*))
              (setf *causal-link-number* 0)
              (setf *causal-links* nil)
              (initialize-reasoner)
              (setf *empty-inference-queue* nil)
              (setf *cycle* *start-time*)
              (setf *display-time* 0)
              (setf *plans-decided* nil)
              (let* (;(max-input-cycle
                     ;     (maximum0 (union= (domain *inputs*) (remove nil (mapcar #'caddr *premises*)))))
                        (time (get-internal-run-time))
                        (abort-time (if *time-limit* (+ (* *time-limit* internal-time-units-per-second 60) time))))
                ; (when (not *display?*) (gc))
                (catch 'die 
                   (dolist (query *ultimate-epistemic-interests*)
                       (reason-backwards-from-query query (query-strength query) 0))
                   (loop
                     (cond ;((and *inference-queue*
                       ;             (every
                       ;               #'(lambda (q)
                       ;                     (and (interest-p (enqued-item q))
                       ;                              (<= (interest-priority (enqued-item q)) *answered-priority*)))
                       ;               *inference-queue*))
                       ;     (return))
                       ; ((eq *cycle* 114) (break))
                       ((null *inference-queue*) (return))
                       ((some
                                  #'(lambda (c)
                                        (and (decided-node c)
                                                 (>= (compute-undefeated-degree-of-support C) (query-strength (query 1)))))
                                       (query-answers (query 1)))
                                 (return))
                     ;  (*inference-queue*
                     ;    (if *empty-inference-queue* (setf *empty-inference-queue* nil)))
                     ;  ((and (not (zerop max-input-cycle)) (> *cycle* max-input-cycle)) (return))
                     ;  ((not *empty-inference-queue*)
                     ;    (setf *empty-inference-queue* t)
                     ;    ; (when *display?*
                     ;    (terpri) (terpri)
                     ;    (princ "-------------------------------------------------") (terpri) (terpri)
                     ;    (princ "                    Waiting for input") (terpri) (terpri)
                     ;    (princ "-------------------------------------------------") (terpri)
                     ;    (terpri) (terpri)))
                     )
                     (incf *cycle*)
                    ; (when (eql *cycle* 30) (break))
                     (update-percepts)
                     (dolist (percept *percepts*)
                         (pull percept *percepts*)
                         (queue-percept percept))
                     (dolist (premise *premises*)
                         (when (eq (mem4 premise) *cycle*)
                              (pull premise *premises*)
                              (queue-premise premise)))
                     (think)
                     (when (and abort-time (> (get-internal-run-time) abort-time))
                          (princ "NO PROOF WAS FOUND WITHIN ") (princ *time-limit*) (princ " MINUTES.")
                          (throw 'die nil))
                     ; (initiate-actions)
                     ))
                (setf time (- (- (get-internal-run-time) time) *display-time*))
                (display-queries) (terpri)
                (when (not *display?*)
                     (princ "Elapsed time = ") (display-run-time-in-seconds time) (terpri))
                (let ((nodes nil))
                  (dolist (query *ultimate-epistemic-interests*)
                      (dolist (N (query-answers query))
                          (pushnew N nodes)))
                  (compute-strictly-relevant-nodes nodes)
                  (let ((argument-length (length *strictly-relevant-nodes*)))
                    (cond (*proofs?* (terpri) (show-arguments))
                              (t (princ "Cumulative size of arguments = ") (princ argument-length) (terpri)
                                  (princ "Size of inference-graph = ") (princ *inference-number*)
                                  (princ " of which ") (princ *unused-suppositions*)
                                  (princ " were unused suppositions.") (terpri)
                                  (princ (truncate (* argument-length 100) *inference-number*))
                                  (princ "% of the inference-graph was used in the argument.") (terpri)))
                    (princ *interest-number*) (princ " interests were adopted.") (terpri)
                    (let ((ri (length (subset 
                                               #'(lambda (in)
                                                     (some #'(lambda (N) (member N *strictly-relevant-nodes*))
                                                                 (discharging-nodes in)))
                                               *interests*))))
                      (princ ri) (princ " interests were discharged by nodes used in the solution.") (terpri)
                      (princ (truncate (* ri 100) *interest-number*))
                      (princ "% of the interests were used directly in finding the solution.") (terpri)
                      (when (not (zerop ri))
                           (princ "The branching factor = ")
                           ; (princ (/ (truncate (* 100 (log *interest-number*)) (log ri)) 100.0)) (terpri))
                           (princ (/ (truncate (* 100 (expt *interest-number* (/ 1 ri)))) 100.0)) (terpri)))
                    (princ *interest-scheme-number*) (princ " interest-schemes were constructed.") (terpri)
                    (princ (- *ip-number* (length *forwards-logical-reasons*)))
                    (princ " instantiated-premises were constructed.") (terpri)
                    (princ *cycle*) (princ " cycles of reasoning occurred.") (terpri)
                    (princ (length *plans*)) (princ " plans were constructed.") (terpri)
                    (analyze-schemes)
                    (when *display?*
                         (princ "The following nodes were used in the arguments:") (terpri)
                         (print-list (order (mapcar #'inference-number *strictly-relevant-nodes*) #'<) 40))
                    (terpri)
                    (push (list *problem-number* time argument-length
                                     (- *inference-number* *unused-suppositions*) (length *plans*)
                                     (answered? (mem1 *ultimate-epistemic-interests*))) *test-log*)))
                (when *log-on* (terpri) (display-reasoning) (display-queries))
                (princ ")") (terpri)))
          (setf *print-pretty* pp)
        (setf *use-reductio* red))))

(defunction think ()
    (when (some
                 #'(lambda (p)
                       (and
                         (some #'(lambda (n)
                                          (and (eq (car (node-formula n)) 'plan-for)
                                                   (not (zerop (undefeated-degree-of-support n)))))
                                     (supporting-inference-nodes p))
                         (every
                           #'(lambda (Q)
                                 (or (not (eq (item-kind Q) :interest))
                                       (not (member p (decision-plans (enqued-item Q))))))
                           *inference-queue*)))
                 *plans-decided*)
         (throw 'die nil))
    ; (when (read-char-no-hang) (clear-input) (throw 'die nil))
    (when (and *display-inference-queue* *display?*) (display-inference-queue))
    (when (eql *cycle* *start-trace*)
         (trace-on)
         (menu-item-disable (oscar-menu-item "Trace on"))
         (menu-item-enable (oscar-menu-item "Trace off"))
         (menu-item-enable (oscar-menu-item "Trace from")))
    (when (eql *cycle* *start-display*)
         (display-on)
         (menu-item-disable (oscar-menu-item "Display on"))
         (menu-item-enable (oscar-menu-item "Display off"))
         (menu-item-enable (oscar-menu-item "Display from")))
    (when *inference-queue*
         (let ((Q (mem1 *inference-queue*)))
           (setf *inference-queue* (cdr *inference-queue*))
           (when *display?*
                (princ "---------------------------------------------------------------------------") (terpri)
                (princ *cycle*) (princ ":    ")
                (princ "Retrieving ") (princ (enqued-item Q))
                (princ " from the inference-queue.")
                (terpri) (terpri))
           (pause)
           (cond ((eq (item-kind Q) :conclusion)
                       (setf *plans-decided* nil)
                       (let ((node (enqued-item Q)))
                         (when (eq (node-kind node) :inference)
                              (store-processed-inference-node node)
                              (setf (node-queue-node node) nil))
                         (reason-forwards-from node 0)))
                     (t
                       (let ((priority
                                 (retrieved-interest-priority
                                   (degree-of-preference Q) (item-complexity Q))))
                         (cond ((eq (item-kind Q) :query)
                                     (setf *plans-decided* nil)
                                     (let ((query (enqued-item Q)))
                                       (setf (query-queue-node query) nil)
                                       (reason-backwards-from-query query priority 0)))
                                   ((eq (item-kind Q) :interest)
                                     (let ((interest (enqued-item Q)))
                                       (setf *plans-decided* (decision-plans interest))
                                       (setf (interest-queue-node interest) nil)
                                       (reason-backwards-from interest priority 0)
                                       (form-epistemic-desires-for interest)))))))))
    (when *new-links*
         (update-beliefs)
         (setf *new-links* nil)))

(defunction display-query (Q)
    (setf *solutions* nil)
    (princ "  Interest in ") (prinp (query-formula Q)) (terpri)
    (cond ((null (answered? Q))
                 (princ "  is unsatisfied.")
                 (when (null (query-answers Q)) (princ "  NO ARGUMENT WAS FOUND."))
                 (terpri))
              ((or (whether-query-p Q) (?-query-p Q))
                (dolist (C (query-answers Q))
                    (when (and (>= (compute-undefeated-degree-of-support C) (query-strength Q))
                                        (let ((p (mem2 (node-formula C))))
                                          (or (not (plan-p p))
                                                (every
                                                  #'(lambda (Q)
                                                        (or (not (eq (item-kind Q) :interest))
                                                              (not (member p (decision-plans (enqued-item Q))))))
                                                  *inference-queue*))))
                           (princ "  is answered by node ")
                           (princ (inference-number C)) (princ ":  ")
                           (princ (pretty (node-formula C))) (terpri)
                           (when (plan-p (mem2 (node-formula C)))
                                (push (mem2 (node-formula C)) *solutions*)
                                (show-plan (mem2 (node-formula C)) nil))
                           (let ((skolem-functions (skolem-functions (node-formula C))))
                              (when skolem-functions
                                   (let* ((sf (mem1 skolem-functions))
                                             (support-link
                                               (find-if #'(lambda (SL)
                                                                 (and (eq (support-link-rule SL) EI)
                                                                           (occur sf (node-formula (support-link-target SL)))
                                                                           (not (occur sf (node-formula (mem1 (support-link-basis SL)))))))
                                                            (ancestral-links C))))
                                      (when support-link
                                           (let* ((node (mem1 (support-link-basis support-link)))
                                                     (formula (node-formula node))
                                                     (var (q-variable formula)))
                                              (princ "  where ") (princ sf) (princ " is any ") (princ var)
                                              (princ " such that ") (princ (q-matrix formula)) (princ ",") (terpri)
                                              (princ "  and the existence of such")
                                              (if (equal var "x") (princ " an ") (princ " a ")) (princ var)
                                              (princ " is guaranteed by node ") (princ (inference-number node)) (terpri))))))
                           )))
                (t (dolist (C (query-answers Q))
                       (when (>= (compute-undefeated-degree-of-support C) (query-strength Q))
                            (princ "  is answered affirmatively by node ")
                            (princ (inference-number C)) (terpri)))))
    (princ "---------------------------------------------------") (terpri))

(defunction live-interest (N)
    (or (interest-queue-node N)
          (some #'(lambda (L) (live-interest (link-interest L)))
                      (left-links N))))

;;========================= reason-schemas for planning =================================

(def-backwards-reason PROTOPLAN
    :conclusions "(plan-for plan goal)"
    :condition (interest-variable plan)
    :backwards-premises
        "(protoplan-for plan goal nil nil nil nil nil)"
    :defeasible? t
    :strength .99
    :variables goal plan)

(defunction null-plan (goal)
   ; (when (equal goal '(on c table)) (break))
    (or
      (find-if
        #'(lambda (p)
              (and (null (plan-steps p)) (equal (plan-goal p) goal)))
        *plans*)
      (let ((plan (make-plan
                           :plan-number (incf *plan-number*)
                           :plan-goal goal
                           :causal-links (list (build-causal-link *start* goal *finish*)))))
        (push plan *plans*)
        plan)))

(def-backwards-reason NULL-PLAN
    :conclusions "(protoplan-for plan goal goals nodes nodes-used links bad-link)"
    :condition (and (interest-variable plan)
                             (not (equal goal 'true))
                             (not (conjunctionp goal))
                             (temporally-projectible goal)
                            ; (or (null bad-link) (not (eq (causal-link-root bad-link) *start*))
                            ;       (not (equal goal (causal-link-goal bad-link))))
                             (or nodes nodes-used (not (mem goal goals))))
    :backwards-premises
        "goal"
        (:condition (not (contains-duplicates goals goal)))
        "(define plan (null-plan goal))"
    :variables goal plan goals nodes nodes-used links bad-link)

(def-backwards-reason THE-TRUE
    :conclusions "(protoplan-for plan true goals nodes nodes-used links bad-link)"
    :condition (interest-variable plan)
    :backwards-premises
        "(define plan (null-plan 'true))"
    :variables plan goals nodes nodes-used links bad-link)

(defunction contains-duplicates (goals &optional goal)
    (let ((goals0 goals))
      (loop
        (if (null goals0) (return nil))
        (let ((g (car goals))) 
          (if (and (not (equal g goal)) (mem g (cdr goals0))) (return t))
        (setf goals0 (cdr goals0))))))

(defunction merge-plans (plan1 plan2 goal1 goal2)
    ; (when (eq *cycle* 127) (setf p1 plan1 p2 plan2 g1 goal1 g2 goal2) (break))
    ; (setf p1 plan1 p2 plan2 g1 goal1 g2 goal2)
    ;; (step (merge-plans p1 p2 g1 g2))
    (let* ((plan nil)
              (g (conj goal1 goal2))
              (plan-steps (union (plan-steps plan1) (plan-steps plan2)))
              (before-nodes (before-nodes plan1))
              (not-between (not-between plan1)))
      (multiple-value-bind
           (before not-between)
           (add-constraints (before-nodes plan2) (not-between plan2) before-nodes not-between plan1)
           (when (or before not-between
                             (and (null (before-nodes plan2)) (null (not-between plan2))
                                      (null before-nodes) (null not-between)))
                (let* ((causal-links (union (causal-links plan1) (causal-links plan2))))
                  (setf plan (build-plan plan-steps g causal-links before not-between)))))
       plan))

(def-backwards-reason SPLIT-CONJUNCTIVE-GOAL
    :conclusions
    "(protoplan-for plan& (goal1 & goal2) goals nodes nodes-used links bad-link)"
    :condition  (and (interest-variable plan&)
                              (temporally-projectible goal1)
                              (temporally-projectible goal2)
                              (or (null bad-link)
                                    (and
                                      (or (equal (causal-link-goal bad-link) goal1)
                                            (not (mem goal1 goals)))
                                      (or (equal (causal-link-goal bad-link) goal2)
                                            (not (mem goal2 goals))))))
    :backwards-premises
        "(protoplan-for plan1 goal1 goals nodes nodes-used links bad-link)"
        "(protoplan-for plan2 goal2 goals nodes nodes-used links bad-link)"
        (:condition
          (not (some #'(lambda (L1)
                                   (some #'(lambda (L2)
                                                    (and (eq (causal-link-target L1) (causal-link-target L2))
                                                             (equal (causal-link-goal L1) (causal-link-goal L2))
                                                             (not (eq (causal-link-root L1) (causal-link-root L2)))))
                                               (causal-links plan2)))
                              (causal-links plan1))))
        "(define plan& (merge-plans plan1 plan2 goal1 goal2))"
        (:condition (not (null plan&)))
    :variables  goal1 goal2 plan1 plan2 goals plan& nodes nodes-used links bad-link)

(defunction build-plan (plan-steps goal causal-links before not-between)
    (setf plan-steps (order plan-steps #'plan-node-order))
    (setf causal-links (order causal-links #'causal-link-order))
    (setf before (order before #'before-order))
    (setf not-between (order not-between #'not-between-order))
    (let ((plan (find-if
                       #'(lambda (p)
                             (and
                               (equal (plan-steps p) plan-steps)
                               (equal (plan-goal p) goal)
                               (equal (causal-links p) causal-links)
                               (equal (before-nodes p) before)
                               (equal (not-between p) not-between)))
                       *plans*)))
      (when (null plan)
           (setf plan
                    (make-plan
                      :plan-number (incf *plan-number*)
                      :plan-steps (order plan-steps #'plan-node-order)
                      :plan-goal goal
                      :causal-links causal-links
                      :before-nodes before
                      :not-between not-between))
           (push plan *plans*))
      plan))

(defunction add-before (node1 node2 plan before not-between)
    ; (when (eq plan (plan 55)) (setf n1 node1 n2 node2 p plan b before nb not-between) (break))
   ; (setf n1 node1 n2 node2 p plan b before nb not-between)
    ;; (step (add-before n1 n2 p b nb))
    (let ((preceding-nodes1 (preceding-nodes node1 plan before))
            (preceding-nodes2 (preceding-nodes node2 plan before))
            (succeeding1 (succeeding-nodes node1 plan before))
            (succeeding2 (succeeding-nodes node2 plan before)))
      (when (member node2 preceding-nodes1) (return-from add-before nil))
      (when (not (member node1 preceding-nodes2))
           ;; remove contained intervals
           (dolist (b before)
               (when (and (eq (car b) node1)
                                   (or (eq node2 (cdr b))
                                         (member (cdr b) (succeeding-nodes node2 plan before))))
                    (pull b before))
               (when (and (eq (cdr b) node2)
                                   (or (eq node1 (car b))
                                         (member (car b) preceding-nodes1)))
                    (pull b before)))
           ;; adjoin overlapping left and right intervals
           (let ((add? t))
             (dolist (b not-between)
                 (cond
                   ((eq (car b) node1)
                     (when
                          (or (eq node2 (cadr b))
                                (and (eq node2 *finish*)
                                         (not (some #'(lambda (x) (or (eq (car x) node2) (eq (cdr x) node2)))
                                                             before)))
                                (and
                                  (member (cadr b) preceding-nodes2)
                                  (member (cddr b) succeeding2)))
                          (pull b not-between)
                          (setf add? nil)
                          (push (cons node1 (cadr b)) before)))
                   ((eq (car b) node2)
                     (when
                          (or (eq node1 (cadr b))
                                (and
                                  (member (cadr b) preceding-nodes1)
                                  (member (cddr b) succeeding1)))
                          (pull b not-between)
                          (setf add? nil)
                          (push (cons (cddr b) node2) before)))))
             (when add? (push (cons node1 node2) before)))
           (dolist (b not-between)
               (when (member (car b) (preceding-nodes (cddr b) plan before))
                    (pull b not-between)
                    (push (cons (car b) (cadr b)) before))
               (when (member (car b) (succeeding-nodes (cadr b) plan before))
                    (pull b not-between)
                    (push (cons (cddr b) (car b)) before)))
           ;; remove newly-redundant pairs
           (dolist (b before)
               (when (equal (car b) node2)
                    (dolist (b* before)
                        (when (and (equal (cdr b*) (cdr b))
                                            (member (car b*) (preceding-nodes node1 plan before)))
                             (pull b* before))))))
      (values before not-between)))

(defunction add-befores (befores before not-between plan)
  ; (when (eql *cycle* 1399) (setf b befores b* before nb not-between p plan) (break))
   ;;(step (add-befores b b* nb p))
    (cond ((null befores) (values before not-between))
              ((null before) (values befores not-between))
              (t 
                (dolist (x befores)
                    (when (not (mem x before))
                         (cond
                           ((or (not (member (car x) (plan-steps plan)))
                                  (not (member (cdr x) (plan-steps plan)))
                                  (member (car x) (possibly-preceding-nodes (cdr x) plan (plan-steps plan) before)))
                             (multiple-value-bind
                                  (before-nodes* not-between*)
                                  (add-before (car x) (cdr x) plan before not-between)
                                  (when (and (null before-nodes*) (null not-between*)) (throw 'merge-plans nil))
                                  (setf before before-nodes* not-between not-between*)))
                           (t (throw 'merge-plans nil)))))
                (values before not-between))))

(defunction add-not-betweens (not-betweens before not-between plan)
    (cond ((null not-betweens) not-between)
              ((null not-between) not-betweens)
              (t 
                (dolist (x not-betweens)
                    (when (not (mem x not-between))
                         (multiple-value-bind
                              (before-nodes* not-between*)
                              (add-<> (car x) (cadr x) (cddr x) plan before not-between)
                              (when (and (null before-nodes*) (null not-between*)) (throw 'merge-plans nil))
                              (setf before before-nodes* not-between not-between*))))))
    (values before not-between))

(defunction add-constraints (befores not-betweens before not-between plan)
    (catch 'merge-plans
       (multiple-value-bind
            (before* not-between*)
            (add-befores befores before not-between plan)
            (multiple-value-bind
                 (before* not-between*)
                 (add-not-betweens not-betweens before* not-between* plan)
                 (values before* not-between*)))))    

(defunction extend-plan (action goal plan bad-link &optional new?)
    ; (when (eq plan (plan 13)) (setf o action g goal p plan) (break))
    ; (setf o action g goal p plan)
    ;; (step (extend-plan o g p))
    (let ((node 
              (when (null new?)
                   (find-if
                     #'(lambda (n)
                           (and (equal (plan-node-action n) action)
                                    (not (member n (plan-steps plan)))))
                     *plan-nodes*))))
      (when (null node)
           (setf new? t)
           (setf node
                    (make-plan-node
                      :plan-node-number (incf *plan-node-number*)
                      :plan-node-action action))
           (draw-conclusion `(plan-node ,node ,action) nil :given nil 1.0 1 nil nil)
           (setf *plan-nodes* (reverse (cons node (reverse *plan-nodes*)))))   ;; This is a kludge
      ; (push node *plan-nodes*))
      (let* ((plan-steps (order (cons node (plan-steps plan)) #'plan-node-order))
                (causal-links
                  (cons
                    (build-causal-link node goal *finish*)
                    (mapcar
                      #'(lambda (x)
                            (cond ((eq (causal-link-target x) *finish*)
                                        (let ((L (build-causal-link (causal-link-root x) (causal-link-goal x) node)))
                                          (if (eq L bad-link) (return-from extend-plan nil) L)))
                                      (t x)))
                      (causal-links plan))))
                (before (cons (cons node *finish*) (before-nodes plan)))
                (not-between (not-between plan)))
        (dolist (x (call-set *finish* plan))
            (when (and (not (eq (causal-link-root x) *start*))
                                (not (member (causal-link-root x) (preceding-nodes node plan before))))
                 (multiple-value-bind
                      (before-nodes* not-between*)
                      (add-before (causal-link-root x) node plan before not-between)
                      (when (and (null before-nodes*) (null not-between*)) (return-from extend-plan nil))
                      (setf before before-nodes* not-between not-between*))))
        (setf causal-links (order causal-links #'causal-link-order))
        (setf before (order before #'before-order))
        (setf not-between (order not-between #'not-between-order))
        (let ((plan*
                  (if (not new?)
                    (find-if #'(lambda (p)
                                      (and
                                        (equal (plan-steps p) plan-steps)
                                        (equal (plan-goal p) goal)
                                        (equal (causal-links p) causal-links)
                                        (equal (before-nodes p) before)
                                        (equal (not-between p) not-between))) *plans*))))
          (when (null plan*)
               (setf plan*
                        (make-plan
                          :plan-number (incf *plan-number*)
                          :plan-steps plan-steps
                          :plan-goal goal
                          :causal-links causal-links
                          :before-nodes before
                          :not-between not-between))
               (push plan* *plans*))
           plan*))))

(def-backwards-reason GOAL-REGRESSION
    :conclusions "(protoplan-for plan goal goals nodes nodes-used links bad-link)"
    :condition (and (not (eq goal 'true))
                             (interest-variable plan) (null nodes-used)
                             (not (conjunctionp goal))
                             (not (mem goal goals))
                             (or (null bad-link)
                                   (equal (causal-link-goal bad-link) goal)
                                   (not (some
                                             #'(lambda (L) (equal (causal-link-goal L) goal))
                                             links))))
    :backwards-premises
        "(define new-goals (cons goal goals))"
        "((precondition & action) => goal)"
        (:condition (and (temporally-projectible precondition)
                                   (not (mem precondition goals))
                                   (not (some #'(lambda (c) (mem c goals)) (conjuncts precondition)))
                                   (not (contains-duplicates goals))))
        "(protoplan-for subplan precondition new-goals nodes nodes-used links bad-link)"
        (:condition (not (mem goal goals)))
        "(define plan (extend-plan action goal subplan bad-link))"
        (:condition (not (null plan)))
    :variables precondition action goal plan subplan goals new-goals nodes nodes-used links bad-link)

(def-backwards-reason PROTOPLAN-FOR-GOAL
   :conclusions 
   	(protoplan-for plan goal goals nil nil nil nil)
   :condition (interest-variable plan)
   :forwards-premises
   	"(protoplan-for plan goal goals0 nil nil nil nil)"
        (:condition
          (and  (not (contains-duplicates goals))
                   (every #'(lambda (L) (not (mem (causal-link-goal L) goals))) (causal-links plan))))
    :variables plan goal goals goals0)

(defunction prinp-causal-link (link)
    (princ (plan-node-number (causal-link-root link))) (princ " --")
    (prinp (causal-link-goal link)) (princ "--> ")
    (if (plan-node-p (causal-link-target link))
      (princ (plan-node-number (causal-link-target link)))
      (prinp (causal-link-target link))))

(defunction prinp-plan-node (node)
    (princ "(") (princ (plan-node-number node)) (princ ") ") (prinp (plan-node-action node)))

(defunction show-plan (plan msg &optional show-supporting-nodes)
    (when (numberp plan) (setf plan (plan plan)))
    (let ((time (get-internal-run-time)))
      (terpri)
      (princ "Plan #") (princ (plan-number plan)) (when msg (princ msg))
      (terpri)
      (when (plan-steps plan) (princ "     PLAN-STEPS: ") (terpri))
      (dolist (node (order (cons *finish* (plan-steps plan)) #'(lambda (x y) (plan-step-order x y plan))))
          (cond
            ((eq node *finish*)
              (princ "        GOAL: ") (prinp (plan-goal plan)) (terpri)
              (princ "             established by:") (terpri)
              (dolist (link (call-set *finish* plan))
                  (princ "               ") (princ (plan-node-number (causal-link-root link))) (princ " --> ")
                  (prinp (causal-link-goal link)) (terpri)))
            (t
              (princ "        ") (prinp-plan-node node) (terpri)
              (when (call-set node plan)
                   (princ "             causal-links:") (terpri)
                   (dolist (link (call-set node plan))
                       (princ "               ") (prinp-causal-link link) (terpri)))
              (when (or 
                           (some #'(lambda (x) (eq (cdr x) node)) (before-nodes plan))
                           (some #'(lambda (x) (eq (car x) node)) (not-between plan)))
                   (princ "             ordering-constraints:") (terpri))
              (dolist (x (before-nodes plan))
                  (when (eq (cdr x) node)
                       (princ "               ") (princ (plan-node-number node)) (princ " > ")
                       (if (eql (plan-node-number (car x)) -1) (princ "*finish*")
                            (princ (plan-node-number (car x)))) (terpri)))
              (dolist (x (not-between plan))
                  (when (eq (car x) node)
                       (princ "               ") (princ (plan-node-number node)) (princ " < ")
                       (princ (plan-node-number (cadr x))) (princ " or ")
                       (princ (plan-node-number node)) (princ " > ")
                       (if (eql (plan-node-number (cddr x)) -1) (princ "*finish*")
                            (princ (plan-node-number (cddr x)))) (terpri))))))
                 (when show-supporting-nodes
                      (dolist (node (supporting-inference-nodes plan))
                          (princ node) (princ ":  ") (princ (node-formula node)) (terpri))
                      (terpri))
      (terpri)
      (when (boundp '*display-time*)
           (setf *display-time* (+ *display-time* (- (get-internal-run-time) time))))
      nil))

(defunction display-plan* (plan)
    (when (numberp plan) (setf plan (plan plan)))
    (let ((time (get-internal-run-time)))
      (terpri)
      (princ "Plan #") (princ (plan-number plan))
      (terpri)
      (when (plan-steps plan)
           (princ "     PLAN-STEPS: ") (terpri)
           (dolist (node (order (cons *finish* (plan-steps plan)) #'(lambda (x y) (plan-step-order x y plan))))
               (princ "        ") (prinp-plan-node node) (terpri)
               (when (call-set node plan)
                    (princ "             causal-links:") (terpri)
                    (dolist (link (call-set node plan))
                        (princ "               ") (prinp-causal-link link) (terpri)))
               (when (or 
                            (some #'(lambda (x) (eq (cdr x) node)) (before-nodes plan))
                            (some #'(lambda (x) (eq (car x) node)) (not-between plan)))
                    (princ "             ordering-constraints:") (terpri))
               (dolist (x (before-nodes plan))
                   (when (eq (cdr x) node)
                        (princ "               ") (princ (plan-node-number node)) (princ " > ")
                        (if (eql (plan-node-number (car x)) -1) (princ "*finish*")
                             (princ (plan-node-number (car x)))) (terpri)))
               (dolist (x (not-between plan))
                   (when (eq (car x) node)
                        (princ "               ") (princ (plan-node-number node)) (princ " < ")
                        (princ (plan-node-number (cadr x))) (princ " or ")
                        (princ (plan-node-number node)) (princ " > ")
                        (if (eql (plan-node-number (cddr x)) -1) (princ "*finish*")
                             (princ (plan-node-number (cddr x)))) (terpri)))))
      (princ "     GOAL: ") (prinp (plan-goal plan)) (terpri)
      (princ "             established by:") (terpri)
      (dolist (link (call-set *finish* plan))
          (princ "               ") (princ (plan-node-number (causal-link-root link))) (princ " --> ")
          (prinp (causal-link-goal link)) (terpri))
      (terpri)
      (when (boundp '*display-time*)
           (setf *display-time* (+ *display-time* (- (get-internal-run-time) time))))
      nil))

(defunction display-plan (plan &optional supporting-nodes)
    (show-plan plan " has been constructed" supporting-nodes))

(defunction adopt-plan (plan)
    (show-plan plan " has been adopted"))

(defunction retract-plan (plan)
    (show-plan plan " has been retracted:"))

(defunction reinstate-plan (plan)
    (show-plan plan " has been reinstated:"))

(defunction display-plans ()
    (dolist (plan (reverse *plans*))
        (display-plan plan)
        (when (every #'(lambda (n) (zerop (undefeated-degree-of-support n)))
                                (supporting-inference-nodes plan))
             (princ "THIS PLAN IS DEFEATED.") (terpri))
        (terpri)))

(defunction plan-steps* (plan)
    (when (numberp plan) (setf plan (plan plan)))
    (cons *finish* (plan-steps plan)))

(defunction display*-plan (plan indents)
    (when (numberp plan) (setf plan (plan plan)))
    (when (plan-steps plan) (line-indentations indents) (princ "     PLAN-STEPS: ") (terpri))
    (dolist (node (order (cons *finish* (plan-steps plan)) #'(lambda (x y) (plan-step-order x y plan))))
        (cond
          ((eq node *finish*)
            (line-indentations indents) (princ "        GOAL: ") (prinp (plan-goal plan)) (terpri)
            (line-indentations indents) (princ "             established by:") (terpri)
            (dolist (link (call-set *finish* plan))
                (line-indentations indents) (princ "               ") (princ (plan-node-number (causal-link-root link)))
                (princ " --> ") (prinp (causal-link-goal link)) (terpri)))
          (t
            (line-indentations indents) (princ "        ") (prinp-plan-node node) (terpri)
            (when (call-set node plan)
                 (line-indentations indents) (princ "             causal-links:") (terpri)
                 (dolist (link (call-set node plan))
                     (line-indentations indents) (princ "               ") (prinp-causal-link link) (terpri)))
            (when (or 
                         (some #'(lambda (x) (eq (cdr x) node)) (before-nodes plan))
                         (some #'(lambda (x) (eq (car x) node)) (not-between plan)))
                 (line-indentations indents) (princ "             ordering-constraints:") (terpri))
            (dolist (x (before-nodes plan))
                (when (eq (cdr x) node)
                     (line-indentations indents) (princ "               ") (princ (plan-node-number node)) (princ " > ")
                     (if (eql (plan-node-number (car x)) -1) (princ "*finish*")
                          (princ (plan-node-number (car x)))) (terpri)))
            (dolist (x (not-between plan))
                (when (eq (car x) node)
                     (line-indentations indents) (princ "               ") (princ (plan-node-number node)) (princ " < ")
                     (princ (plan-node-number (cadr x))) (princ " or ")
                     (princ (plan-node-number node)) (princ " > ")
                     (if (eql (plan-node-number (cddr x)) -1) (princ "*finish*")
                          (princ (plan-node-number (cddr x)))) (terpri))))))
    nil)

;;=========================== defeat for planning ============================

(defunction preceding-nodes (node plan before)
    (let ((X nil))
      (dolist (pair before)
          (when (eq (cdr pair) node)
               (push (car pair) X)
               (dolist (n (preceding-nodes (car pair) plan before))
                   (pushnew n X))))
      X))

(defunction succeeding-nodes (node plan before)
    (cond ((eq node *start*) (plan-steps plan))
              (t
                (let ((X nil))
                  (dolist (pair before)
                      (when (eq (car pair) node)
                           (push (cdr pair) X)
                           (dolist (n (succeeding-nodes (cdr pair) plan before))
                               (pushnew n X))))
                  X))))

(defunction possibly-preceding-nodes (node plan nodes before)
    (if (not (eq node *start*))
         (let ((succeeding-nodes (succeeding-nodes node plan before)))
           (subset #'(lambda (x)
                              (and
                                (not (eq x node))
                                (not (member x succeeding-nodes))))
                         nodes))))

(defunction possibly-succeeding-nodes (node plan nodes before)
    (when (plan-node-p node)
         (let ((preceding-nodes (preceding-nodes node plan before)))
           (subset #'(lambda (x)
                              (and
                                (not (eq x node))
                                (not (member x preceding-nodes))))
                         nodes))))

(defunction possibly-intermediate-nodes (node1 node2 plan nodes before not-between)
    (cond
      ((plan-node-p node2)
        (let ((possibly-succeeding-nodes (possibly-succeeding-nodes node1 plan nodes before)))
          (when possibly-succeeding-nodes
               (subset
                 #'(lambda (node)
                       (and
                         (not (member (cons node (cons node1 node2)) not-between))
                         (not
                           (some #'(lambda (n1)
                                            (some #'(lambda (n2)
                                                             (mem (cons node (cons n1 n2)) (not-between plan)))
                                                        (cons node2 (succeeding-nodes node2 plan before))))
                                       (cons node1 (preceding-nodes node1 plan before))))))
                 (possibly-preceding-nodes node2 plan possibly-succeeding-nodes before)))))
      (t (possibly-succeeding-nodes node1 plan nodes before))))

(defunction plan-step-order (node1 node2 plan)
    (or
      (plan-step-strict-order node1 node2 plan)
      (and (not (plan-step-strict-order node2 node1 plan))
               (< (plan-node-number node1) (plan-node-number node2)))))

(defunction plan-step-strict-order (node1 node2 plan)
    (and
      (member node1 (possibly-preceding-nodes node2 plan (plan-steps plan) (before-nodes plan)))
      (not (member node2 (possibly-preceding-nodes node1 plan (plan-steps plan) (before-nodes plan))))))

(defunction plan-node-order (node1 node2)
    (< (plan-node-number node1) (plan-node-number node2)))

(defunction causal-link-order (link1 link2)
    (< (causal-link-number link1) (causal-link-number link2)))

;; These search for undermined links by giving preference to those with the
;; most potential undermining nodes.
(defunction causal-link-length (L plan)
    (length (possibly-intermediate-nodes
                  (causal-link-root L) (causal-link-target L) plan
                  (plan-steps plan) (before-nodes plan) (not-between plan))))

#|
(def-backwards-undercutter UNDERMINE-CAUSAL-LINKS
    :defeatee  protoplan
    :backwards-premises
    "(define links
          (order (if (live-links? plan) (live-causal-links plan) (causal-links plan))
                     #'(lambda (x y) (> (causal-link-length x plan) (causal-link-length y plan)))))"
    "(plan-undermines-causal-links plan links)"
    :variables plan links)
|#

(def-backwards-undercutter UNDERMINE-CAUSAL-LINKS
    :defeatee  protoplan
    :backwards-premises
    "(define links (if (live-links? plan) (live-causal-links plan) (reverse (causal-links plan))))"
    "(plan-undermines-causal-links plan links)"
    :variables plan links)

(def-backwards-reason PLAN-UNDERMINES-FIRST-CAUSAL-LINK
    :conclusions  "(plan-undermines-causal-links plan links)"
    :condition  (car links)
    :backwards-premises
        "(define first-link (car links))"
        "(plan-undermines-causal-link plan R node first-link e-plan)"
    :variables  plan node links first-link R e-plan)

(def-backwards-reason PLAN-UNDERMINES-ANOTHER-CAUSAL-LINK
    :conclusions  "(plan-undermines-causal-links plan links)"
    :condition  (cdr links)
    :backwards-premises
        "(define rest-of-links (cdr links))"
        "(plan-undermines-causal-links plan rest-of-links)"
    :variables  plan links rest-of-links)

(defunction penultimate-node (plan)
    (find-if #'(lambda (n)
                      (some #'(lambda (l) (eq (causal-link-root l) n)) (call-set *finish* plan)))
                (plan-steps plan)))

(def-backwards-reason PLAN-UNDERMINES-CAUSAL-LINK
    :conclusions  "(plan-undermines-causal-link plan+ R node link plan)"
    :backwards-premises
        "(define -goal (neg (causal-link-goal link)))"
        "(define node1 (if (not (eq *start* (causal-link-root link))) (causal-link-root link)))"
        "(define node2 (causal-link-target link))"
        "(define before (before-nodes plan+))"
        "(define not-between (not-between plan+))"
        "(embellished-plan-for plan plan+ -goal node1 node2 before not-between)"
        (:condition
          (or (null (fixed-links plan+))
                (some #'(lambda (L) (not (member L (fixed-links plan+)))) (causal-links plan))))
        "(define node (penultimate-node plan))"
        "(define R
            (let ((u-links
                      (subset #'(lambda (L)
                                         (not (some
                                                   #'(lambda (L*) (and (eq (causal-link-target L*) node)
                                                                                     (equal (causal-link-goal L) (causal-link-goal L*))))
                                                   (causal-links plan+))))
                                    (call-set node plan))))
              (when u-links (gen-conjunction (mapcar #'causal-link-goal u-links)))))"
        ;; R is used for CONFRONTATION
    :variables  plan plan+ link -goal node node1 node2 R before not-between)

(def-backwards-reason EMBELLISHED-PROTOPLAN
    :conclusions "(embellished-plan-for plan plan+ -goal node1 node2 before not-between)"
    :condition (interest-variable plan)
    :backwards-premises
        "(embellished-protoplan-for plan plan+ -goal node1 node2 before not-between)"
    :defeasible? t
    :strength .99
    :variables plan plan+ -goal node1 node2 before not-between)

(def-backwards-undercutter UNDERMINE-EMBEDDED-CAUSAL-LINKS
    :defeatee  embellished-protoplan
    :backwards-premises
    "(define links (set-difference (causal-links plan) (causal-links plan+)))"
    "(plan-undermines-causal-links plan links)"
    :variables plan plan+ links)

(defunction remove-finish (before)
    (let ((new-before nil))
      (dolist (b before)
          (cond
            ((eq (car b) *finish*)
              (dolist (b* before)
                  (when (eq (cdr b*) *finish*)
                       (push (cons (car b*) (cdr b)) new-before))))
            ((not (eq (cdr b) *finish*))  (push b new-before))))
      new-before))

(defunction remove-not-between-finish (before not-between)
    (let ((new-not-between nil))
      (dolist (nb not-between)
          (cond ((eq (cddr nb) *finish*)
                      (dolist (b before)
                          (when (eq (car b) *finish*)
                               (push (cons (car nb) (cons (cadr nb) (cdr b))) new-not-between))))
                    ((not (eq (car nb) *finish*)) (push nb new-not-between))))
      new-not-between))

(defunction penultimate-nodes (plan)
    (let ((nodes nil))
      (dolist (L (call-set *finish* plan))
          (pushnew (causal-link-root L) nodes))
      nodes))

(def-backwards-reason EMBELLISHED-PROTOPLAN-for-GOAL
    :conclusions  "(embellished-protoplan-for plan plan+ -goal node1 node2 before not-between)"
    :condition  (interest-variable plan)
    :forwards-premises
        "(protoplan-for plan0 -goal goals nil nil nil)"
        (:condition (subplan plan0 plan+))
        "(define p-nodes (penultimate-nodes plan0))"
        (:condition
          (if node1 (subsetp p-nodes
                             (possibly-intermediate-nodes node1 node2 plan+ (plan-steps plan+) before not-between))
                          (subsetp p-nodes
                                (possibly-preceding-nodes node2 plan+ (plan-steps plan+) before))))
        "(define new-order
            (let ((before0 (remove-finish before))
                    (not-between0 (remove-not-between-finish before not-between)))
              (dolist (L (causal-links plan0))
                  (when (eq (causal-link-target L) *finish*) (push (cons (causal-link-root L) *finish*) before0)))
              (dolist (penultimate-node p-nodes)
                  (dolist (n (possibly-succeeding-nodes penultimate-node plan+ (plan-steps plan+) before0))
                      (multiple-value-bind
                           (before-nodes* not-between*)
                           (add-before *finish* n plan+ before0 not-between0)
                           (setf before0 before-nodes* not-between0 not-between*))))
              (list before0 not-between0)))"
        (:condition (not (null new-order)))
        "(define plan
            (build-plan
              (plan-steps plan+) -goal (causal-links plan0) (car new-order) (cadr new-order)))"
    :variables  plan plan0 plan+ -goal node node1 node2 p-nodes goals before not-between new-order)

(defunction extend-embellished-plan (new-node goal subplan plan+)
    ; (when (eq subplan (plan 10)) (setf nn new-node g goal p subplan p+ plan+) (break))
    ; (setf nn new-node g goal p plan no p+ plan+)
    ;; (step (extend-embellished-plan nn g p p+))
    (let* ((causal-links
                (cons
                  (build-causal-link new-node goal *finish*)
                  (mapcar
                    #'(lambda (x)
                          (cond ((eq (causal-link-target x) *finish*)
                                      (build-causal-link (causal-link-root x) (causal-link-goal x) new-node))
                                    (t x)))
                    (causal-links subplan))))
              (before (cons (cons new-node *finish*) (remove-finish (before-nodes subplan))))
              (not-between (remove-not-between-finish (before-nodes subplan) (not-between subplan))))
      (when before
           (dolist (n (possibly-succeeding-nodes new-node subplan (plan-steps plan+) before))
               (multiple-value-bind
                    (before-nodes* not-between*)
                    (add-before *finish* n subplan before not-between)
                    (when (and (null before-nodes*) (null not-between*)) (return-from extend-embellished-plan nil))
                    (setf before before-nodes* not-between not-between*)))
           (dolist (x (call-set *finish* subplan))
               (when (and (not (eq (causal-link-root x) *start*))
                                   (not (member (causal-link-root x) (preceding-nodes new-node subplan before))))
                    (multiple-value-bind
                         (before-nodes* not-between*)
                         (add-before (causal-link-root x) new-node subplan before not-between)
                         (when (and (null before-nodes*) (null not-between*)) (return-from extend-embellished-plan nil))
                         (setf before before-nodes* not-between not-between*))))
           (setf causal-links (order causal-links #'causal-link-order))
           (setf before (order before #'before-order))
           (setf not-between (order not-between #'not-between-order))
           (let ((plan*
                     (find-if #'(lambda (p)
                                       (and
                                         (equal (plan-steps p) (plan-steps plan+))
                                         (equal (plan-goal p) goal)
                                         (equal (causal-links p) causal-links)
                                         (equal (before-nodes p) before)
                                         (equal (not-between p) not-between))) *plans*)))
             (when (null plan*)
                  (setf plan*
                           (make-plan
                             :plan-number (incf *plan-number*)
                             :plan-steps (plan-steps plan+)
                             :plan-goal goal
                             :causal-links causal-links
                             :before-nodes before
                             :not-between not-between))
                  (push plan* *plans*))
             plan*))))

#| This is like match, but instead of listing the variables it identifies them from their p-lists. |#
(defunction match+ (pattern expression)
    (labels ((match* (pattern expression bindings)
                      (cond ((atom pattern)
                                  (cond ((equal pattern expression) t)
                                            ((and (symbolp pattern) (eq (var-kind pattern) :variable))
                                              (let ((assoc (assoc pattern bindings :test 'equal)))
                                                (cond (assoc (equal expression (cdr assoc)))
                                                          (t (list (cons pattern expression))))))))
                                ((listp pattern)
                                  (when (listp expression)
                                       (let ((m (match* (car pattern) (car expression) bindings)))
                                         (cond ((eq m t) (match* (cdr pattern) (cdr expression) bindings))
                                                   (m (let ((m* (match* (cdr pattern) (cdr expression) (append m bindings))))
                                                           (cond ((eq m* t) m)
                                                                     (m* (union= m m*))))))))))))
      (match* pattern expression nil)))

#| order will have *finish* in it.  node2 can be *finish* if node1 is not nil.  As we regress backsards, we
add constraints to before and not-between.  When we get to a null-plan, we have all the constraints.
We move *finish* to the right place at that time.  Then as we walk back up the regression (using extend-
embellished-plan) we move *finish* just as we do using extend-plan, but we also place *finish* as early as
possible, i.e., before all possibly-succeeding-nodes of new-node. |#
(def-backwards-reason EMBEDDED-GOAL-REGRESSION
    :conclusions "(embellished-protoplan-for plan plan+ goal node1 node2 before not-between)"
    :condition (and (not (eq goal 'true)) (interest-variable plan))
    :forwards-premises
    	"((& precondition action) => goal)"
        (:condition (temporally-projectible precondition))
        "(define possible-nodes
                     (if node1
                       (possibly-intermediate-nodes node1 node2 plan+ (plan-steps plan+) before not-between)
                       (possibly-preceding-nodes node2 plan+ (plan-steps plan+) before)))"
        (:condition (not (null possible-nodes)))
        "(plan-node new-node action)"
        (:condition (member new-node possible-nodes))
        "(define new-order
            (multiple-value-bind
                 (before* not-between*)
                 (catch 'merge-plans
                    (add-befores (if node1 (list (cons node1 new-node) (cons new-node node2))
                                               (list (cons new-node node2)))
                                          before not-between plan+))
                 (list before* not-between*)))"
        (:condition (car new-order))
        "(define new-before (mem1 new-order))"
        "(define new-between (mem2 new-order))"
    :backwards-premises
        "(embellished-protoplan-for subplan plan+ precondition nil new-node new-before new-between)"
        "(define plan
             (extend-embellished-plan new-node goal subplan plan+))"
        (:condition (not (null plan)))
    :variables plan plan+ subplan goal node1 node2 new-node precondition before not-between 
                     new-order new-before new-between possible-nodes action)

#| This moves *finish* to the right place, ie., preceding all nodes of plan+. |#
(defunction embedded-null-plan (goal plan+ before not-between)
    ; (when (eq plan+ (plan 5)) (setf g goal p plan+ n2 node2 o order)  (break))
    ;;(step (embedded-null-plan g p n2 o))
    (setf before (remove-finish before))
    (setf not-between (remove-not-between-finish before not-between))
    (dolist (n (plan-steps plan+))
        (multiple-value-bind
             (before-nodes* not-between*)
             (add-before *finish* n plan+ before not-between)
             (when (and (null before-nodes*) (null not-between*)) (return-from embedded-null-plan nil))
             (setf before before-nodes* not-between not-between*)))
    (setf before (order before #'before-order))
    (setf not-between (order not-between #'not-between-order))
    (or
      (find-if
        #'(lambda (p)
              (and (equal (plan-goal p) goal)
                       (equal (plan-steps p) (plan-steps plan+))
                       (equal (before-nodes p) before)
                       (equal (not-between p) not-between)))
        *plans*)
      (let ((plan (make-plan
                         :plan-number (incf *plan-number*)
                         :plan-steps (plan-steps plan+)
                         :plan-goal goal
                         :before-nodes before
                         :not-between not-between
                         :causal-links (list (build-causal-link *start* goal *finish*)))))
        (push plan *plans*)
        plan)))

(def-backwards-reason EMBEDDED-NULL-PLAN
    :conclusions 
        "(embellished-protoplan-for plan plan+ goal node1 node2 before not-between)"
    :condition (and (interest-variable plan) (null node1) (not (equal goal 'true)) (not (conjunctionp goal)))
    :backwards-premises
        "goal"
        "(define plan (embedded-null-plan goal plan+ before not-between))"
        (:condition (not (null plan)))
    :variables plan+ goal plan node node1 node2 before not-between)

(def-backwards-reason EMBEDDED-THE-TRUE
    :conclusions "(embellished-protoplan-for plan plan+ true node1 node2 before not-between)"
    :condition (interest-variable plan)
    :backwards-premises
        "(define plan (embedded-null-plan 'true plan+ before not-between))"
    :variables plan+ plan node node1 node2 before not-between)

(defunction merge-embellished-plans (plan1 plan2 goal1 goal2)
    ; (when (eq *plan-number* 27) (setf p1 plan1 p2 plan2 g1 goal1 g2 goal2) (break))
    ; (setf p1 plan1 p2 plan2 g1 goal1 g2 goal2)
    ;; (step (merge-plans p1 p2 g1 g2))
    (let* ((g (conj goal1 goal2))
              (causal-links (union (causal-links plan1) (causal-links plan2)))
              (before1 (subset #'(lambda (b) (eq (cdr b) *finish*)) (before-nodes plan1)))
              (before2 (subset #'(lambda (b) (eq (cdr b) *finish*)) (before-nodes plan2)))
              (not-between (remove-not-between-finish (before-nodes plan2) (not-between plan2)))
              (before (union= before1 (union= before2 (remove-finish (before-nodes plan2))))))
      (dolist (n (possibly-succeeding-nodes *finish* plan2 (plan-steps plan2) before))
          (multiple-value-bind
               (before-nodes* not-between*)
               (add-before *finish* n plan2 before not-between)
               (when (and (null before-nodes*) (null not-between*)) (return-from merge-embellished-plans nil))
               (setf before before-nodes* not-between not-between*)))
      (build-plan (plan-steps plan1) g causal-links before not-between)))

(def-backwards-reason SPLIT-EMBEDDED-CONJUNCTIVE-GOAL
    :conclusions 
        "(embellished-protoplan-for plan& plan+ (goal1 & goal2) node1 node2 before not-between)"
    :condition
        (and (interest-variable plan&) (null node1) (temporally-projectible goal1) (temporally-projectible goal2))
    :backwards-premises
        "(embellished-protoplan-for plan1 plan+ goal1 node1 node2 before not-between)"
        "(define before1 (before-nodes plan1))"
        "(define not-between1 (not-between plan1))"
        "(embellished-protoplan-for plan2 plan+ goal2 node1 node2 before1 not-between1)"
        "(define plan& (merge-embellished-plans plan1 plan2 goal1 goal2))"
        (:condition (not (null plan&)))
    :variables
	plan+ plan& plan1 plan2 nodes goal1 goal2 node1 node2 before not-between before1 not-between1)

;(def-backwards-undercutter UNDERMINE-EMBEDDED-CAUSAL-LINKS
;    :defeatee   embellished-proto-plan
;    :backwards-premises
;    "(define links (set-difference (causal-links plan) (causal-links subplan)))"
;    "(plan-undermines-causal-links plan links)"
;    :variables plan subplan links)

;(def-backwards-reason PLAN-NODE-RESULT
;    :conclusions  "(node-result node R Q)"
;    :condition  (interest-variable node)
;    :conclusions-function
;    (let ((conclusions nil))
;      (let ((m (match+ action (plan-node-action node*))))
;        (when m (push (cons `(node-result ,node* ,(match-sublis m R) ,Q) nil) conclusions)))
;      conclusions)
;    :backwards-premises
;    	"(=> (& R action) Q)"
;        "(plan-node node*)"
;    :variables  action node node* R Q)

(def-backwards-reason  =>-neg1
    :conclusions  "(P => ~(Q & R))"
    :condition (and (not (interest-variable Q)) (not (interest-variable R)))
    :backwards-premises
        "(define -Q (neg Q))"
    	"(P => -Q)"
    :variables  P Q -Q R)

(def-backwards-reason  =>-neg2
    :conclusions  "(P => ~(Q & R))"
    :condition (and (not (interest-variable Q)) (not (interest-variable R)))
    :backwards-premises
        "(define -R (neg R))"
    	"(P => -R)"
    :variables  P Q R -R)

(def-backwards-reason  =>-disj1
    :conclusions  "(P => (Q v R))"
    :condition (and (not (interest-variable Q)) (not (interest-variable R)))
    :backwards-premises
    	"(P => Q)"
    :variables  P Q R)

(def-backwards-reason  =>-disj2
    :conclusions  "(P => (Q v R))"
    :condition (and (not (interest-variable Q)) (not (interest-variable R)))
    :backwards-premises
    	"(P => R)"
    :variables  P Q R)

(def-forwards-reason SIMPLIFY-=>
    :forwards-premises "(P => (Q & R))"
    :conclusions  "(P => Q)" "(P => R)"
    :variables P Q R)

(def-backwards-reason =>-ADJUNCTION
    :conclusions "(P => (Q & R))"
    :backwards-premises  "(P => Q)" "(P => R)"
    :variables P Q R)

(def-backwards-reason =>-TRANSITIVITY
    :conclusions "(P => Q)"
    :forwards-premises  "(R => Q)" 
    :backwards-premises  "(P => R)"
    :variables P Q R)

;;===================== IMPOSING ORDERING CONSTRAINTS ==========================

#| Add an ordering constraint. |#
(defunction add-not-between (node link plan record?)
    ; (when (eq plan (plan 15)) (setf n node l link p plan r record?) (break))
   ; (setf n node l link p plan r record?)
    ;; (step (add-not-between n l p r))
    (let ((node1 (causal-link-root link))
            (node2 (causal-link-target link)))
      (when (or (not (eq node1 *start*)) (and (plan-node-p node2) (not (eq node2 *finish*))))
           (multiple-value-bind
                (before not-between)
                (add-<> node node1 node2 plan (before-nodes plan) (not-between plan))
                (cond
                  ((or before not-between)
                    (setf before (order before #'before-order))
                    (setf not-between (order not-between #'not-between-order))
                    (let ((plan*
                              (find-if #'(lambda (p)
                                                (and (equal (plan-steps p) (plan-steps plan))
                                                         (equal (plan-goal p) (plan-goal plan))
                                                         (equal (causal-links p) (causal-links plan))
                                                         (equal (before-nodes p) before)
                                                         (equal (not-between p) not-between)))
                                          *plans*)))
                      (when (null plan*)
                           (setf plan*
                                    (make-plan
                                      :plan-number (incf *plan-number*)
                                      :plan-steps (plan-steps plan)
                                      :plan-goal (plan-goal plan)
                                      :causal-links (causal-links plan)
                                      :before-nodes before
                                      :not-between not-between))
                           (push plan* *plans*))
                      #| The following is a kludge.  It will not work if new information is imported during the
				processing and it can lead to additional undermining.  The purpose of this code
				is to prevent rechecking previously checked causal-links in the plan produced
				by adding ordering-constraints. |#
                      (when record?
                           (setf (live-links? plan*) t)
                           (setf (live-causal-links plan*)
                                    (subset
                                      #'(lambda (L)
                                            (let
                                              ((interest (interest-for `(nil (plan-undermines-causal-link ,plan x y ,L z)) '(x y z) nil)))
                                              (or (null interest) (live-interest interest))))
                                     ; (remove link (if (live-links? plan) (live-causal-links plan) (causal-links plan))))))
                                      (if (live-links? plan) (live-causal-links plan) (causal-links plan)))))
                      plan*)))))))

(defunction add-<> (node node1 node2 plan before not-between)
     ;(when (eq plan (plan 32)) (setf n node n1 node1 n2 node2 p plan) (break))
    ;; (step (add-<> n n1 n2 p b nb))
    (let* ((preceding-nodes1 (preceding-nodes node1 plan before))
              (preceding-nodes2 (preceding-nodes node2 plan before))
              (succeeding-nodes1 (succeeding-nodes node1 plan before))
              (succeeding-nodes2 (succeeding-nodes node2 plan before))
              (possibly-preceding-nodes
                (if (not (eq node *start*))
                  (subset #'(lambda (x)
                                     (and
                                       (not (eq x node1))
                                       (not (member x succeeding-nodes1))))
                                (plan-steps plan))))
              (possibly-succeeding-nodes
                (subset #'(lambda (x)
                                   (and
                                     (not (eq x node2))
                                     (not (member x preceding-nodes2))))
                              (plan-steps plan))))
      (cond ((member node possibly-preceding-nodes)
                  (cond ((member node possibly-succeeding-nodes)   ;; add new not-between constraint
                              ;; remove contained not-between intervals
                              (dolist (b not-between)
                                  (when (and (eq (car b) node)
                                                      (or (eq node1 (cadr b))
                                                            (member node1 (preceding-nodes (cadr b) plan before)))
                                                      (or (eq node2 (cddr b))
                                                            (member node2 (succeeding-nodes (cddr b) plan before))))
                                       (pull b not-between)))
                              ;; adjoin overlapping left and right intervals
                              (let ((left
                                        (find-if
                                          #'(lambda (b)
                                                (and (eq (car b) node)
                                                         (member (cadr b) preceding-nodes1)
                                                         (or (eq node1 (cddr b))
                                                               (member (cddr b) succeeding-nodes1))))
                                          not-between))
                                      (right
                                        (find-if
                                          #'(lambda (b)
                                                (and (eq (car b) node)
                                                         (or (eq node2 (cadr b))
                                                               (member (cadr b) preceding-nodes2))
                                                         (member (cddr b) succeeding-nodes2)))
                                          not-between)))
                                (cond (left
                                            (pull left not-between)
                                            (cond (right
                                                        (pull right not-between)
                                                        (push (cons node (cons (cadr left) (cddr right))) not-between))
                                                      (t (push (cons node (cons (cadr left) node2)) not-between))))
                                          (t
                                            (cond (right
                                                        (pull right not-between)
                                                        (push (cons node (cons node1 (cddr right))) not-between))
                                                      (t (push (cons node (cons node1 node2)) not-between)))))
                                (values before not-between)))
                            (t (add-before node node1 plan before not-between))))
                ((member node possibly-succeeding-nodes) (add-before node2 node plan before not-between)))))

(def-forwards-reason ADD-ORDERING-CONSTRAINTS
    :conclusions
    "(protoplan-for plan goal goals nil nil nil nil)"
    :forwards-premises
        "(plan-undermines-causal-link plan- R node link e-plan)"
        (:clue? t)
        "(protoplan-for plan- goal goals nil nil nil nil)"
        "(define plan (add-not-between node link plan- t))"
        (:condition (not (null plan)))
    :variables  plan plan- node link goal goals R e-plan)

;;================ defeating the defeaters ========================

(def-forwards-reason ADD-EMBEDDED-ORDERING-CONSTRAINTS
    :conclusions "(embellished-protoplan-for plan plan+ goal node1 node2 before not-between)"
    :condition (interest-variable plan)
    :forwards-premises
        "(plan-undermines-causal-link plan- R node link e-plan)"
        (:clue? t)
        "(embellished-protoplan-for plan- plan+ goal node1 node2 before not-between)"
        "(define plan (add-not-between node link plan- nil))"
        (:condition (not (null plan)))
    :variables  plan- plan+ plan goal node1 node2 before not-between R node link e-plan)

;;========================= patching plans ===========================

#| This computes whether an interest in plan& relative to the goal-stack goals0 generates
an interest in plan relative to the goal-stack goals. |#
(defunction goal-stack-extension (plan& goals goals0 link)
    (let ((n (length goals))
            (m (length goals0)))
      (and (>= n m)
               (let ((used-goals nil)
                       (unused-goals goals))
                 (dotimes (x (- n m))
                     (push (car unused-goals) used-goals)
                     (setf unused-goals (cdr unused-goals)))
                 (and (equal goals0 unused-goals)
                          (goals-used (reverse used-goals) plan& link))))))

(defunction goals-used (goals plan link)
    ; (setf g goals p plan l link)
    (and
      (some #'(lambda (L)
                       (mem (car goals) (conjuncts (causal-link-goal L))))
                  (call-set (causal-link-target link) plan))
      (or (and (mem (car goals) (conjuncts (plan-goal plan)))
                    (null (cdr goals)))
            (some #'(lambda (L)
                             (and (eq (causal-link-root L) (causal-link-target link))
                                      (goals-used (cdr goals) plan L)))
                        (causal-links plan)))))

(defunction remove-subplan (plan+ bad-link)
    (let ((nodes nil)
            (links nil)
            (causal-links (causal-links plan+))
            (new-nodes (list *finish*)))
      (loop
        (when (null new-nodes) (return))
        (dolist (node new-nodes)
            (pull node new-nodes)
            (dolist (link causal-links)
                (when (eq (causal-link-target link) node)
                     (pull link causal-links)
                     (when (not (eq link bad-link))
                                 (when (and (not (eq (causal-link-root link) *start*))
                                                     (not (member (causal-link-root link) nodes)))
                                      (push (causal-link-root link) nodes)
                                      (pushnew (causal-link-root link) new-nodes))
                                 (pushnew link links))))))
      (values nodes links)))

(defunction replace-subplan (new-plan0 plan+ bad-link)
    ; (when (and (eq plan+ (plan 26)) (eq new-plan0 (plan 35))) (setf  np new-plan0 p+ plan+ bl bad-link) (break))
    ;; (step (replace-subplan np p+ bl))
    (multiple-value-bind
         (nodes links)
         (remove-subplan plan+ bad-link)
         (let ((plan-steps (union nodes (plan-steps new-plan0)))
                 (before-nodes
                   (subset #'(lambda (x) (and (member (car x) nodes)
                                                                 (or (eq (cdr x) *finish*) (member (cdr x) nodes))))
                                 (before-nodes plan+)))
                 (not-between-nodes
                   (subset #'(lambda (x) (and (member (car x) nodes)
                                                                 (member (cadr x) nodes) (member (cddr x) nodes)))
                                 (not-between plan+))))
           (dolist (node nodes)
               (when (null (assoc node before-nodes)) (push (cons node *finish*) before-nodes)))
           (multiple-value-bind
                (before not-between)
                (add-constraints
                  (before-nodes new-plan0) (not-between new-plan0)
                  before-nodes not-between-nodes new-plan0)
                (when (or before not-between
                                  (and (null (before-nodes new-plan0)) (null (not-between new-plan0))
                                           (null before-nodes) (null not-between-nodes)))
                     (dolist (link (causal-links new-plan0))
                         (cond ((eq (causal-link-target link) *finish*)
                                     (pushnew
                                       (build-causal-link 
                                         (causal-link-root link) (causal-link-goal link) (causal-link-target bad-link))
                                       links)
                                     (multiple-value-bind
                                          (before+ not-between+)
                                          (add-before (causal-link-root link) (causal-link-target bad-link)
                                                               plan+ before not-between)
                                          (setf before before+ not-between not-between+)
                                          (when (null before) (return-from replace-subplan))))
                                   (t (pushnew link links))))
                     (let ((plan
                               (build-plan plan-steps (plan-goal plan+) links before not-between)))
                       (when plan
                            (let ((live-links 
                                      (subset
                                        #'(lambda (L)
                                              (let
                                                ((interest
                                                   (interest-for `(nil (plan-undermines-causal-link ,plan+ x y ,L z)) '(x y z) nil)))
                                                (or (null interest) (live-interest interest))))
                                        (remove bad-link
                                                       (or (live-causal-links plan+) (causal-links plan+)))))
                                    (nodes (set-difference (plan-steps plan) (plan-steps plan+))))
                              (setf (live-causal-links plan)
                                       (append
                                        ; (intersection live-links (causal-links plan))
                                         (subset #'(lambda (L) (member L (causal-links plan))) live-links)
                                         (set-difference (causal-links plan) (causal-links plan+))
                                         (subset
                                           #'(lambda (L)
                                                 (some
                                                   #'(lambda (n)
                                                         (possibly-preceding-node n (causal-link-target L) plan ))
                                                   nodes))
                                          ; (set-difference (remove bad-link (causal-links plan)) live-links))))
                                           (set-difference (causal-links plan) live-links))))
                              (setf (live-links? plan) t)))
                       plan))))))

(defunction possibly-preceding-node (node1 node2 plan)
    (and
      (not (eq node1 node2))
      (not (member node1 (succeeding-nodes node1 plan (before-nodes plan))))))

(def-forwards-reason REUSE-NODES
    :conclusions
    "(protoplan-for plan goal nil nil nil nil nil)"
    :forwards-premises
         "(plan-undermines-causal-link plan+ R node bad-link e-plan)"
         (:clue? t)
         "(protoplan-for plan+ goal nil nil nil nil nil)"
         (:node node1)
         "(define goal0 (causal-link-goal bad-link))"
         "(protoplan-for plan0 goal0 goals nodes nil links0 link0)"
         (:node node2)
         (:condition (and (subplan plan0 plan+)
                                    (member node2 (node-ancestors node1))
                                    (some #'(lambda (L)
                                                     (and (eq (causal-link-target L) *finish*)
                                                              (eq (causal-link-root L) (causal-link-root bad-link))
                                                              (equal (causal-link-goal L) goal0)))
                                                (causal-links plan0))
                                   ; (goals-used (cons goal0 goals) plan+ bad-link)
                                    ))
         (:clue? t)
         "(define new-nodes
                 (cons node (possibly-preceding-nodes node plan+ (plan-steps plan+) (before-nodes plan+))))"
         "(define links (remove bad-link (causal-links plan+)))"
    :backwards-premises
         "(protoplan-for new-plan0 goal0 goals new-nodes nil links bad-link)"
         (:condition
           (and (not (some
                             #'(lambda (L) (and (eq (causal-link-target L) *finish*)
                                                             (eq (causal-link-root L) (causal-link-root bad-link))))
                             (causal-links new-plan0)))
                    (some #'(lambda (n) (member n new-nodes)) (plan-steps new-plan0))))
         "(define plan (replace-subplan new-plan0 plan+ bad-link))"
         (:condition (not (null plan)))
    :variables
          plan goal goal0 goals nodes plan+ R node new-nodes 
          links bad-link plan0 new-plan0 links0 link0 node1 node2  e-plan)

(def-backwards-reason REUSE-PLANS
   :conclusions 
   	(protoplan-for plan goal goals nodes nodes-used links bad-link)
   :condition (and (interest-variable plan) (not (null nodes)))
   :forwards-premises
   	"(protoplan-for plan goal goals0 nodes0 nodes-used0 links0 bad-link0)"
        (:condition (and (subsetp (plan-steps plan) nodes)
                                   (not (member bad-link (causal-links plan)))
                                   (not (some
                                             #'(lambda (L)
                                                   (let ((g (causal-link-goal L)))
                                                     (or (equal g goal) (not (mem g goals)))))
                                             (causal-links plan)))
                                   (or (not (equal goal (causal-link-goal bad-link)))
                                         (mem goal goals)
                                         (not (some
                                                   #'(lambda (L) (and (equal goal (causal-link-goal bad-link))
                                                                                   (eq (causal-link-root L) (causal-link-root bad-link))
                                                                                   (eq (causal-link-target L) *finish*)))
                                                   (causal-links plan))))
                                   (or (plan-steps plan)
                                         (null bad-link)
                                         (not (eq (causal-link-target bad-link) *start*))
                                         (not (equal goal (causal-link-goal bad-link))))
                                   ))
    :variables plan goal goals nodes nodes-used links bad-link goals0 nodes0 nodes-used0 links0 bad-link0)

(defunction extend-plan-with-node (node goal plan bad-link)
    ; (when (eq plan (plan 13)) (setf n node g goal p plan) (break))
    ; (setf n node g goal p plan)
    ;; (step (extend-plan n g p))
    (let* ((plan-steps (cons node (plan-steps plan)))
              (causal-links
                (cons
                  (build-causal-link node goal *finish*)
                  (mapcar
                    #'(lambda (x)
                          (cond ((eq (causal-link-target x) *finish*)
                                      (let ((L (build-causal-link (causal-link-root x) (causal-link-goal x) node)))
                                        (if (eq L bad-link) (return-from extend-plan-with-node nil) L)))
                                    (t x)))
                    (causal-links plan))))
              (before (cons (cons node *finish*) (before-nodes plan)))
              (not-between (not-between plan)))
      (dolist (x (call-set *finish* plan))
          (when (and (not (eq (causal-link-root x) *start*))
                              (not (member (causal-link-root x) (preceding-nodes node plan before))))
               (multiple-value-bind
                    (before-nodes* not-between*)
                    (add-before (causal-link-root x) node plan before not-between)
                    (when (and (null before-nodes*) (null not-between*)) (return-from extend-plan-with-node nil))
                    (setf before before-nodes* not-between not-between*))))
      (build-plan plan-steps goal causal-links before not-between)))

#|
(def-backwards-reason REUSE-NODE
    :conclusions "(protoplan-for plan goal goals nodes nodes-used links bad-link)"
    :condition (and (interest-variable plan) (not (null nodes)) (not (conjunctionp goal)))
    :forwards-premises
    	"(=> (& R action) goal)"
        "(plan-node node action)"
        (:condition 
          (and (member node nodes)
                   (or (null bad-link)
                         (not (equal goal (causal-link-goal bad-link)))
                         (mem goal goals)
                         (not (equal (plan-node-action (causal-link-root bad-link)) action)))
          ))
        "(define precondition
            (let ((m (match+ action (plan-node-action node))))
              (when m (match-sublis m R))))"
        (:condition (not (null precondition)))
        "(define new-nodes (remove node nodes))"
        "(define new-nodes-used (cons node nodes-used))"
    :backwards-premises
        "(protoplan-for subplan precondition goals new-nodes new-nodes-used links bad-link)"
        "(define plan (extend-plan-with-node node goal subplan bad-link))"
        (:condition (not (null plan)))
    :variables R action precondition plan goal goals nodes node new-nodes
                     subplan nodes-used new-nodes-used links bad-link)
|#

(def-backwards-reason REUSE-NODE
    :conclusions "(protoplan-for plan goal goals nodes nodes-used links bad-link)"
    :condition (and (interest-variable plan) (not (null nodes)) (not (conjunctionp goal)))
    :forwards-premises
    	"(=> (& R action) goal)"
        "(plan-node node action)"
        (:condition 
          (and (member node nodes)
                   (or (null bad-link)
                         (not (equal goal (causal-link-goal bad-link)))
                         (mem goal goals)
                         (not (equal (plan-node-action (causal-link-root bad-link)) action)))
          ))
        "(define new-nodes (remove node nodes))"
        "(define new-nodes-used (cons node nodes-used))"
    :backwards-premises
        "(protoplan-for subplan R goals new-nodes new-nodes-used links bad-link)"
        "(define plan (extend-plan-with-node node goal subplan bad-link))"
        (:condition (not (null plan)))
    :variables R action plan goal goals nodes node new-nodes
                     subplan nodes-used new-nodes-used links bad-link)

;;========================= confrontation ===========================

(defunction make-confrontation-plan (repair-plan plan -R node links e-plan)
   ; (when (and (eq repair-plan (plan 4)) (eq plan (plan 10))) (setf rp repair-plan p plan r* -r n node l links) (break))
   ; (setf rp repair-plan p plan r* -r n node l links) (break)
    ;; (step (make-confrontation-plan rp p r* n l))
    (when
         (some
           #'(lambda (L)
                 (not (some
                           #'(lambda (L*)
                                 (and
                                   (eq (causal-link-root L) (causal-link-root L*))
                                   (equal (causal-link-goal L) (causal-link-goal L*))))
                           (call-set node plan))))
           (call-set *finish* repair-plan))
         (let* ((before-nodes (before-nodes plan))
                   (not-between (not-between plan))
                   (plan-steps (union (plan-steps plan) (plan-steps repair-plan)))
                   (succeeding-nodes (succeeding-nodes node plan before-nodes))
                   (new-befores nil)
                   (causal-links
                     (mapcar
                       #'(lambda (link)
                             (cond ((eq (causal-link-target link) *finish*)
                                         (let ((L (build-causal-link (causal-link-root link) -R node)))
                                           (when 
                                                (or
                                                  (member L links)
                                                  (eq (causal-link-root link) node)
                                                  (mem (causal-link-root link) succeeding-nodes))
                                                (return-from make-confrontation-plan nil))
                                           (push (cons (causal-link-root link) node) new-befores)
                                           L))
                                       (t link)))
                       (causal-links repair-plan))))
           (multiple-value-bind
                (before not-between)
                (add-constraints
                  (append new-befores (before-nodes repair-plan))
                  (not-between repair-plan) before-nodes not-between plan)
                (when before
                     (let ((plan
                               (build-plan plan-steps (plan-goal plan) (union causal-links (causal-links plan))
                                                 before not-between)))
                       (setf (fixed-links plan) (causal-links e-plan))
                       plan))))))

(def-forwards-reason CONFRONTATION
    :conclusions
    "(protoplan-for plan goal goals nodes nodes-used links bad-link)"
    :forwards-premises
        "(plan-undermines-causal-link plan- R node link e-plan)"
        (:condition (not (null R)))
        (:clue? t)
        "(protoplan-for plan- goal goals nodes nodes-used links bad-link)"
    :backwards-premises
        "(define -R (neg R))"
        "(protoplan-for repair-plan -R nil nodes nodes-used links bad-link)"
        "(define plan (make-confrontation-plan repair-plan plan- -R node links e-plan))"
        (:condition (not (null plan)))
    :variables  plan plan- R -R repair-plan node link goal goals nodes nodes-used links bad-link e-plan)

(def-forwards-reason EMBEDDED-CONFRONTATION
    :conclusions "(embellished-protoplan-for plan plan+ goal node1 node2 before not-between)"
    :forwards-premises
        "(plan-undermines-causal-link plan+ R node link   e-plan)"
        (:condition (not (null R)))
        (:clue? t)
        "(embellished-protoplan-for subplan plan+ goal node1 node2 before not-between)"
    :backwards-premises
        "(define -R (neg R))"
        "(embellished-plan-for repair-plan plan+ -R node1* node2* new-before new-not-between)"
        "(define plan (make-confrontation-plan repair-plan subplan -R node (list link)  e-plan))"
        (:condition (not (null plan)))
    :variables  plan plan+ goal node1 node2 before not-between R node link subplan precondition
                     new-node new-before new-not-between -R node1* node2* repair-plan  e-plan)

;;============================ plan histories ================================

(defunction plan-parents (plan)
    (when (numberp plan) (setf plan (plan plan)))
    (let ((nodes (supporting-inference-nodes plan))
            (parents nil)
            (generators nil))
      (dolist (node nodes)
          (dolist (link (support-links node))
              (when (eq (support-link-rule link) REUSE-NODES)
                   (pushnew
                     (list (support-link-rule link) plan (mem2 (node-formula (mem1 (support-link-clues link)))))
                     generators :test 'equal))
              (cond ((eq (support-link-rule link) add-ordering-constraints)
                          (pushnew (list (list add-ordering-constraints)
                                                   (mem2 (node-formula (mem1 (support-link-clues link)))))
                                            parents :test '==))
                        ((or (eq (support-link-rule link) null-plan) (eq (support-link-rule link) embedded-null-plan))
                          (pushnew nil parents))
                        (t
                          (let ((X nil))
                            (dolist (b (support-link-basis link))
                                (let ((formula (node-formula b)))
                                  (when (and (listp formula)
                                                      (not (eq plan (mem2 formula)))
                                                      (or (equal (car formula) 'protoplan-for)
                                                            (equal (car formula) 'embellished-protoplan-for)
                                                            (equal (car formula) 'plan-for)
                                                            (equal (car formula) 'embellished-plan-for)))
                                       (pushnew (mem2 formula) X))))
                            (if X
                              (let ((X* (find-if #'(lambda (z) (== (cdr z) X)) parents)))
                                (cond (X* (pushnew (support-link-rule link) (car X*) :test 'equal))
                                          (t (push (cons (list (support-link-rule link)) X) parents)))))
                            )))))
      (values parents generators)))

(defunction plans-for (goal &optional display? show-supporting-nodes)
    (when (stringp goal) (setf goal (reform goal)))
    (let ((plans
              (subset 
                #'(lambda (p)
                      (and (equal (plan-goal p) goal)
                               (some #'(lambda (n) (equal (car (node-formula n)) 'protoplan-for))
                                                (supporting-inference-nodes p)))) 
                *plans*)))
      (when display?
           (dolist (p plans)
               (let* ((status (some #'(lambda (n) (not (zerop (undefeated-degree-of-support n))))
                                                (supporting-inference-nodes p)))
                         (msg (if status " is undefeated" " is defeated")))
                 (show-plan p msg show-supporting-nodes))))
      plans))

(defunction plan-status (plan)
    (when (numberp plan) (setf plan (plan plan)))
    (some #'(lambda (n) (not (zerop (undefeated-degree-of-support n))))
                (supporting-inference-nodes plan)))

(defunction plan-histories (plan)
    (when (numberp plan) (setf plan (plan plan)))
    (multiple-value-bind
         (parents generators)
         (plan-parents plan)
         (values
           (unionmapcar
             #'(lambda (x)
                   (if x
                     (mapcar
                       #'(lambda (z) (cons (car x) z))
                       (gencrossproduct
                         (mapcar
                           #'(lambda (p)
                                 (multiple-value-bind
                                      (histories p-generators)
                                      (plan-histories p)
                                      (mapcar
                                        #'(lambda (h)
                                              (dolist (g p-generators) (pushnew g generators :test 'equal))
                                              (if h (list p h) (list p))) histories)))
                           (cdr x))))
                     (list nil)))
             parents)
           generators)))

(defunction plan-history (plan &optional full (indent 1) used-generators)
    (when (numberp plan) (setf plan (plan plan)))
    (terpri) (space-indent (1- indent)) (princ "Plan history for Plan #") (princ (plan-number plan)) (terpri)
    (space-indent (1- indent)) (princ "---------------------------------") (terpri)
    (multiple-value-bind
         (histories generators)
         (plan-histories plan)
    (dolist (H histories)
        (display-plan-history plan H (list indent) full nil ) (terpri))
    (dolist (g (setdifference generators used-generators))
        (terpri) (terpri) (space-indent (1- (+ indent 40)))
        (princ "Plan #") (princ (plan-number (mem2 g))) (princ " was generated from Plan #")
        (princ (plan-number (mem3 g))) (princ " using ") (princ (mem1 g)) (terpri)
        (space-indent (1- (+ indent 40)))
        (princ "---------------------------------------------------------------------------------------") (terpri)
        (plan-history (mem3 g) full (+ indent 40) (union generators used-generators)))))

(defun space-indent (depth &optional stream)
    (dotimes (i depth) (princ " " stream)))

(defunction display-plan-history (plan H indents full bar)
    (let ((length (1- (length H))))
      (line-indentations indents) (if bar (princ "|")) (princ plan)
      (when H (princ " by ")
                  (princ (caar H))
                  (when (cdar H) (dolist (x (cdar H)) (princ ", ") (princ x))))
      (terpri)
      (when full (display*-plan plan indents))
      (when full (line-indentations indents) (terpri))
      (let* ((reverse-indents (reverse indents))
                (new-indents0 (reverse (cons (+ (car reverse-indents) (if full 10 5)) (cdr reverse-indents))))
                (new-indents 
                  (cond ((> length 1)
                              (setf bar t)
                              (reverse (cons 0 (cons (+ (car reverse-indents) (if full 10 5)) (cdr reverse-indents)))))
                            (t (setf bar nil) new-indents0))))
        (let ((count length))
          (dolist (X (cdr H))
              (display-plan-history
                (car X) (mem2 X)
                (if (eql count 1) new-indents0 new-indents)
                full (if (eql count 1) bar))
              (decf count))))))

#| This prints vertiical bars at the positions of the indents, except for the last one.  It prints the
indicated number of spaces for the last indent.  To finish with a bar, use 0 for the last indent. |#
(defun line-indentations (indents)
    (let ((n (car indents))
            (rest-of-indents (cdr indents)))
      (dotimes (x n) (princ " "))
      (when rest-of-indents
           (princ "|")
           (line-indentations rest-of-indents))))

;;============================ running a plan-set ================================

(defmacro make-planning-problem-list (&rest body)
    (setf body (remove-if #'(lambda (x) (equal x '(SOLVE-PLANNING-PROBLEM))) body))
    `(progn (setf *planning-problems* ',body)
                 "plan-list loaded"))

(defunction P-TEST ()
    (terpri) (princ "(") (terpri)
    (setf *test-log* nil)
    (dolist (P *planning-problems*)
        (eval P)
        (solve-planning-problem))
    (setf *test-log* (list *planner* *test-log*))
    (when (not *display?*) (display-plan-test-log))
    (terpri)
    (princ *test-log*)
    (terpri) (princ ")")
    (terpri))

(defunction display-plan-test-log ()
    (princ "=========================== TEST RESULTS ===========================")
    (terpri) (terpri)
    (princ "                                                         ") (princ (mem1 *test-log*))
    (when *plan-comparison-log*
         (princ "          ") (princ (mem1 *plan-comparison-log*))
         (princ "                   ratio of run times"))
    (terpri) (terpri)
    (let ((ratios nil))
      (dolist (L (reverse (mem2 *test-log*)))
          (let* ((n (mem1 L))
                    (L* (assoc n (mem2 *plan-comparison-log*) :test 'equal)))
            (princ "#") (princ n) (princ "                                                                          ")
            (display-run-time-in-seconds (mem2 L))
            (when L* (princ "                            ") (display-run-time-in-seconds (mem2 L*))
                        (cond ((and (not (zerop (mem3 L))) (not (zerop (mem3 L*))))
                                    (let ((ratio (/ (mem2 L) (mem2 L*))))
                                      (push ratio ratios)
                                      (princ "                            ")
                                      (princ
                                        (if (< (abs (- (mem2 L) (mem2 L*))) 15) 1.0
                                             (float (/ (truncate (* 100 ratio)) 100))))))
                                  (t (princ "                            ##"))))
            (terpri)
            (princ "           plan found:                                                     ") (princ (mem6 L))
            (when L* (princ "                                              ") (princ (mem6 L*))) (terpri)
            (princ "           cumulative  argument length:                 ") (princ (mem3 L))
            (when L* (princ "                                           ") (princ (mem3 L*))
                        (cond ((and (not (zerop (mem3 L))) (not (zerop (mem3 L*))))
                                    (princ "                                      ")
                                    (let ((d (- (mem3 L) (mem3 L*))))
                                      (cond ((> d 0) (princ "+") (princ d))
                                                ((< d 0) (princ d))
                                                (t (princ "  --")))))
                                  (t (princ "                            --"))))
            (terpri)
            (princ "           total number of inferences:                     ") (princ (mem4 L))
            (when L* (princ "                                          ") (princ (mem4 L*))
                        (cond ((and (not (zerop (mem3 L))) (not (zerop (mem3 L*))))
                                    (princ "                                      ")
                                    (let ((d (- (mem4 L) (mem4 L*))))
                                      (cond ((> d 0) (princ "+") (princ d))
                                                ((< d 0) (princ d))
                                                (t (princ "  --")))))
                                  (t (princ "                            --"))))
            (terpri)
            (princ "           plans constructed:                                     ") (princ (mem5 L))
            (when L* (princ "                                           ") (princ (mem5 L*))
                        (cond ((and (not (zerop (mem5 L))) (not (zerop (mem5 L*))))
                                    (princ "                                      ")
                                    (let ((d (- (mem5 L) (mem5 L*))))
                                      (cond ((> d 0) (princ "+") (princ d))
                                                ((< d 0) (princ d))
                                                (t (princ "  --")))))
                                  (t (princ "                            --"))))
            (terpri) (terpri))
          (terpri))
      (when ratios
           (princ "geometric average ratio of run times = ")
           (let ((average (expt (apply '* ratios) (/ 1 (length ratios)))))
             (princ (float (/ (truncate (* 10000 average)) 10000))))
           (terpri))))

(setf *plan-comparison-log* '(Non-Linear-Planner-42
 ((14 174 24 44 16 t) (12 716 94 133 39 t) (11 700 57 121 36 t) (10 148 26 37 12 t) (9 317 43 72 27 t) (8 158 29 41 14 t) (6 223 43 62 20 t)
  (5 193 44 57 20 t) (4 78 23 28 8 t) (3 69 20 25 8 t) (2 416 59 85 29 t) (1 105 36 45 15 t))))

#|
(setf *plan-comparison-log* '(Non-Linear-Planner-36
 ((14 253 49 58 16 t) (12 994 177 199 53 t) (11 1144 125 194 54 t) (10 183 38 51 13 t) (9 380 58 83 21 t) (8 212 44 57 15 t) (6 268 54 65 20 t)
  (5 253 56 67 21 t) (4 87 26 29 8 t) (3 72 23 26 8 t) (2 664 101 111 29 t) (1 100 36 45 15 t))))

(setf *plan-comparison-log* '(Non-Linear-Planner-35
 ((14 305 49 58 16 t) (12 1414 177 199 53 t) (11 1911 125 194 54 t) (10 203 38 51 13 t) (9 476 58 83 21 t) (8 250 44 57 15 t) (6 290 54 65 20 t)
  (5 284 56 67 21 t) (4 94 26 29 8 t) (3 77 23 26 8 t) (2 677 101 111 29 t) (1 104 36 45 15 t))))

(setf *plan-comparison-log* '(Non-Linear-Planner-34
 ((14 323 51 69 17 t) (13 1033 109 157 36 t) (12 1083 116 169 42 t) (11 2651 123 237 60 t) (10 225 34 54 12 t) (9 521 50 93 20 t) (8 287 42 63 14 t)
  (7 363 64 90 25 t) (6 1522 93 155 35 t) (5 339 64 90 25 t) (4 93 24 32 8 t) (3 81 21 29 8 t) (2 1263 110 148 29 t) (1 132 35 54 15 t))))
|#
