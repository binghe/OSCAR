#| this file contains the beginning part of OSCAR_3.31, before loading Assignment-trees_3.26 |#

;                                                                                OSCAR_3.31

#|This is the  agent-architecture OSCAR, described in chapter nine of COGNITIVE
CARPENTRY.|#

#| This is based upon OSCAR_3.30.  It converts variables between conclusions and interests, and
fixes some errors in the use of the match in discharging reductios. |#

(in-package "OSCAR")

(if (not (fboundp 'gc)) (defun gc () t))

;========================== OSCAR =========================

;---------------------------------  support-linkS ----------------------------------

(defstruct (support-link (:print-function print-support-link)
                                           (:conc-name nil))
    (support-link-number 0)
    (support-link-target nil)   ;; the node supported by the link
    (support-link-basis nil)   ;; a list of inference-nodes
    (support-link-rule nil)  ;; a substantive reason or a string describing an inference rule
    (defeasible? nil)  ;; t if the inference is a defeasible one
    (support-link-defeaters nil)
    (defeating-assignment-trees nil)
    (support-link-discount-factor 1.0)  ;; This is the discount-factor provided by the link-rule.
    (support-link-nearest-defeasible-ancestors nil)
    (support-link-reason-strength 1.0)  ;; the strength of the reason
    (support-link-strength nil)  ;; min of reason-strength and undefeated-degrees-of-support for basis
    (support-link-binding nil)
    (support-link-conclusive-defeat-status nil)
    (temporal-link nil)
    (generating-interest-link nil)
    (support-link-clues nil))

(defun print-support-link (x stream depth)
    (declare (ignore depth))
    (princ "#<" stream) (princ "support-link #" stream)
    (princ (support-link-number x) stream) (princ " for node " stream)
    (princ (inference-number (support-link-target x)) stream)
    (princ ">" stream))

#| This finds the support-link with support-link-number n. |#
(defunction support-link (n)
    (find-if #'(lambda (L) (equal (support-link-number L) n))
                 *support-links*))

; -------------------------------------- INFERENCE-NODES --------------------------------------

(defstruct (inference-node (:print-function print-inference-node)
                                                     (:conc-name nil))
    (inference-number 0)
    (node-sequent nil)
    (node-formula nil)
    (node-supposition nil)
    (node-kind nil)   ;;:percept, :desire, or :inference
    (support-links nil)
    (node-justification nil)  ;; a keyword if the node is given or a supposition
    (consequent-links nil)
    (old-undefeated-degree-of-support nil) ;; the degree prior to the last computation of defeat statuses
    (reductio-ancestors nil)
    (non-reductio-supposition nil)
    (maximal-degree-of-support 0)  ;; maximal strength of support-links
    (node-defeatees nil)
    (undefeated-degree-of-support nil)
    (node-ancestors nil)
    (nearest-defeasible-ancestors nil)
    (answered-queries nil)
    (deductive-only nil)   ;; If conclusion is for deductive purposes only, this is t.
    (generated-interests nil)
    (generating-interests nil);; interest generating sup
    (cancelled-node nil)
    (discounted-node-strength nil)
    (processed? nil)  ;;  T if node has been processed.
    (node-variables nil)
    (discharged-interests nil)  ;; triples (interest unifier unifiers) where unifiers is produced by
                                                     ;; appropriately-related-suppositions.  unifier and unifiers are
                                                     ;; left nil in cases where they will not be used.
    (node-supposition-variables nil)
    (interests-discharged? nil)   ;; records whether interests have been discharged
    (reductios-discharged (not *use-reductio*))  ;; records whether reductio-interests have been discharged
    (readopted-supposition 0)  ;; number of times the node has been readopted as a supposition
    (node-discount-factor 1.0)  ;; This is the discount-factor provided by the node-rule.
                                                ;;  it's only use is in ei.
    (node-c-list nil)
    (node-queue-node nil)
    (enabling-interests nil)  ;; if the node is obtained by discharging inference-links, this is the
                                                   ;; list of resultant-interests of the links.
    (motivating-nodes nil)  ;; nodes motivating the inference, not included in the basis.
    (generated-direct-reductio-interests nil)
    (generated-defeat-interests nil)
    (generating-defeat-interests nil)  ;; interest in defeaters discharged by this node
    (temporal-node nil)  ;; nil or the cycle on which the node was constructed
   (background-knowledge nil)
    (non-reductio-supposition? nil)
    (anchoring-interests nil)
    )

(defun print-inference-node (x stream depth)
    (declare (ignore depth))
    (princ "#<" stream) (princ "Node " stream)
    (princ (inference-number x) stream) (princ ">" stream))

(defunction nf (n)
    (when (numberp n) (setf n (node n)))
    (prinp (node-formula n))
    (node-formula n))

(defunction udos (n) (undefeated-degree-of-support n))

(defunction mdos (n) (maximal-degree-of-support n))

(defunction adjust-for-time (strength node)
    (let ((delta (- *cycle* (temporal-node node))))
      (cond ((>= delta *temporal-decay-minimum*) 0.0)
                ((zerop strength) 0.0)
                (t (- (* (+ strength 1) (expt *temporal-decay* delta)) 1)))))

;(defunction adjust-for-time (strength node)
;    (let* ((t0 (temporal-node node))
;              (decay (expt *temporal-decay* (- *cycle* t0))))
;      (if (< decay strength) decay strength)))

(defunction adjust-for-decay (strength decay)
    (if (or (zerop strength) (< decay .5)) 0.0 (- (* (+ strength 1) decay) 1)))

(defunction compute-maximal-degree-of-support (node)
    (cond
      (*deductive-only* 1.0)
      ((temporal-node node)
        (adjust-for-time (maximal-degree-of-support node) node))
      (t (maximal-degree-of-support node))))

(defunction compute-undefeated-degree-of-support (node)
    (cond
      (*deductive-only* 1.0)
      ((temporal-node node)
        (adjust-for-time (undefeated-degree-of-support node) node))
      (t (undefeated-degree-of-support node))))

(defunction compute-old-undefeated-degree-of-support (node)
    (if (and (temporal-node node) (old-undefeated-degree-of-support node))
      (adjust-for-time (old-undefeated-degree-of-support node) node)
      (old-undefeated-degree-of-support node)))

(defunction compute-discounted-node-strength (node)
    (if (temporal-node node)
      (adjust-for-time (discounted-node-strength node) node)
      (discounted-node-strength node)))

(defunction deductive-node (n)
   (and (not (background-knowledge n))
            (member nil (nearest-defeasible-ancestors n))))

(defunction node-consequences (n)
    (mapcar #'support-link-target (consequent-links n)))

(defunction node (n)
    (find-if #'(lambda (node) (equal (inference-number node) n))
                 *inference-graph*))

(defunction display-inference-node (n )
    (if (numberp n) (setf n (node n)))
    (princ "  # ") (princ (inference-number n)) (princ "   ")
    (when (not (equal (node-kind n) :inference)) (princ (node-kind n)) (princ "         "))
    (prinp (node-formula n))
    (when (node-supposition n)
         (princ "    supposition: ") (set-prinp (node-supposition n)))
    (if (zerop (undefeated-degree-of-support n)) (princ "                  DEFEATED"))
    (terpri)
    (cond ((node-justification n) (princ "  ") (princ (node-justification n)) (terpri))
                ((support-links n)
                  (princ "  Inferred by:") (terpri)
                  (dolist (L* (support-links n))
                      (princ "                support-link #") (princ (support-link-number L*))
                      (princ " from ") (princ-set (mapcar #'inference-number (support-link-basis L*)))
                      (princ " by ") (princ (support-link-rule L*))
                      (when (support-link-defeaters L*)
                           (princ "  defeaters: ")
                           (princ-set (mapcar #'inference-number (support-link-defeaters L*))))
                      (when (defeating-assignment-trees L*) (princ "   DEFEATED"))
                      (terpri))))
    (princ "  undefeated-degree-of-support: ") (princ (undefeated-degree-of-support n)) (terpri)
    (cond ((deductive-node n)
                 (princ "  This node encodes a deductive argument.") (terpri)))
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
         (princ " }")
         (terpri)))

(defunction display-support-link (L)
   (if (numberp L) (setf L (support-link L)))
    (let ((n (support-link-target L)))
     (princ "  # ") (princ (inference-number n)) (princ "   ")
     (when (not (equal (node-kind n) :inference)) (princ (node-kind n)) (princ "         "))
     (prinp (node-formula n))
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

(defunction display-unsupported-node (n )
    (if (numberp n) (setf n (node n)))
    (terpri) (princ "  # ") (princ (inference-number n)) (princ "   ")
    (when (not (equal (node-kind n) :inference)) (princ (node-kind n)) (princ "         "))
    (prinp (node-formula n))
    (when (node-supposition n)
         (princ "    supposition: ") (set-prinp (node-supposition n)))
    (if (zerop (undefeated-degree-of-support n)) (princ "                  DEFEATED"))
    (terpri)
    (when (keywordp (node-justification n)) (princ "  ") (princ (node-justification n)) (terpri))
    ; (princ "  maximal-degree-of-support: ") (princ (compute-maximal-degree-of-support n)) (terpri)
    ; (princ "  undefeated-degree-of-support: ") (princ (compute-undefeated-degree-of-support n)) (terpri)
    (when (and *display?* *graphics-on*)
         (when *graphics-pause* (pause-graphics))
         (draw-n n *og* *nodes-displayed*)
         (push n *nodes-displayed*)))

(defunction subsumes (sequent1 sequent2)
   (and (equal (sequent-formula sequent1) (sequent-formula sequent2))
            (subsetp= (sequent-supposition sequent1) (sequent-supposition sequent2))))
