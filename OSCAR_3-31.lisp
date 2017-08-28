
(in-package "OSCAR")

;======================================================
; -------------------------------------- CONCLUSIONS --------------------------------------

(defstruct (d-node (:conc-name nil) (:print-function print-d-node))
    d-node-number
    (d-node-description nil)
    (discrimination-tests nil)
    (d-node-c-lists nil)
    (d-node-i-lists nil)
    (parent-d-node nil)
    (d-node-forwards-reasons nil)  ;; a list of partially-instantiated-premises
    (d-node-backwards-reasons nil)  ;; a list of non-degenerate backwards-reasons
    (d-node-interest-schemes nil)  ;; a list of partially-instantiated-premises
    (d-node-degenerate-backwards-reasons nil)
    )

(defunction print-d-node (x stream depth)
    (declare (ignore depth))
    (princ "#<" stream) (princ "d-node: " stream)
    (princ (d-node-number x) stream) (princ ">" stream))

(defunction d-node (n)
    (find-if #'(lambda (dn) (eql (d-node-number dn) n)) *discrimination-net*))

(defunction display-d-node (dn depth test)
   ; (setf d dn de depth te test)
    ;; (step (display-d-node d de te))
    (let ((pp *print-pretty*))
      (setf *print-pretty* nil)
      (line-indent depth)
      (princ "--")
      (if test (prinp-test test) (princ dn))
      (princ "   ")
      (terpri)
      (dolist (cl (d-node-c-lists dn)) (line-indent depth) (princ "       ") (princ cl) (terpri))
      (dolist (il (d-node-i-lists dn)) (line-indent depth) (princ "       ") (princ il) (terpri))
      (dolist (ip (d-node-forwards-reasons dn))
          (line-indent depth)
          (cond ((ip-basis ip) (princ "       instantiated-premise ") (princ (ip-number ip)) (princ " for "))
                      (t (princ "       first premise for ")))
          (princ (ip-reason ip))
          (princ ": ")
          (let ((p (match-sublis (ip-binding ip) (fp-formula (ip-premise ip)))))
            (if (and (negationp p) (negationp (negand p))) (setf p (negand (negand p))))
            (prinp p))
          (terpri))
      (dolist (br (d-node-backwards-reasons dn)) (line-indent depth) (princ "       conclusion for ")
                 (princ br) (terpri))
      (dolist (br (d-node-degenerate-backwards-reasons dn)) (line-indent depth) (princ "       conclusion for ")
                 (princ br) (terpri))
      (dolist (is (d-node-interest-schemes dn))
          (line-indent depth)
          (princ "       interest-scheme ") (princ (is-number is)) (princ " for interest ")
          (princ (interest-number (is-target-interest is)))
          (princ " by ")
          (princ (is-reason is))
          (princ ": ")
          (let ((p (match-sublis (is-binding is) (fp-formula (is-premise is)))))
            (if (and (negationp p) (negationp (negand p))) (setf p (negand (negand p))))
            (prinp p))
          (terpri))
      (setf *print-pretty* pp)))

(defunction formula-code (P)
    (setf *quantifier-number* 0)
    (multiple-value-bind (code term-list) (formula-code* P nil)
         (values (reverse code) term-list)))

(defunction formula-code* (P descriptor)
    (cond ((listp P)
                 (let ((description nil) (elt-num 1) (term-list nil))
                    (cond
                      ;; This handles notational variants.
                      ((or (eq (car p) 'all) (eq (car P) 'some))
                        (setf P
                                 (cons (car P) (subst (list 'q-var (incf *quantifier-number*)) (mem2 P) (cddr P)))))
                      ((eq (car P) 'at)
                        (setf term-list (cddr P))
                        (setf P (list (car P) (cadr P))))
                      ((eq (car P) 'throughout)
                        (setf term-list (cdr (mem3 P)))
                        (setf P (list (car P) (cadr P) (list (car (mem3 P))))))
                      ((and (symbolp (car P))
                                 (not (member (car P) *operators*))
                                 (not (member (car P) '(~ & v -> <-> all some ? @))))
                        (setf term-list (cdr P))
                        (setf P (list (car P)))))
                    (dolist (Q P)
                        (let ((Q-descriptor (cons elt-num descriptor)))
                           (cond ((not (listp Q))
                                        (push (cons (reverse Q-descriptor) Q) description))
                                       (t
                                         (multiple-value-bind (d tl) (formula-code* Q Q-descriptor)
                                              (setf term-list (append tl term-list))
                                              (setf description (append d description))
                                              )))
                           (incf elt-num)))
                    (values description term-list)))
                (t (values (list (cons descriptor P)) nil))))

(defun display-discrimination-net (&optional (nodes *discrimination-net*))
    (setf *callees* nil)
    (setf *blank-line* nil)
    (setf *line-columns* nil)
    (display-discrimination-node *top-d-node* nil 0 t nodes)
    nil)

(defun ddn (&optional (nodes *discrimination-net*)) (display-discrimination-net nodes))

(defun display-discrimination-node (d-node listees depth last? nodes &optional test)
    (when (member d-node nodes)
         (when (null depth)
              (setf depth 0) (setf listees nil))
         (cond ((or (mem d-node listees) (mem d-node *callees*))
                     (line-indent depth)
                     (when (not (mem depth *line-columns*)) (princ "|"))
                     (princ "--") (princ d-node) (princ " .....") (terpri)
                     (setf *blank-line* nil)
                     (cond (last? (pull depth *line-columns*))
                               (t (pushnew depth *line-columns* :test 'eql))))
                   (t
                     (let* ((DC (discrimination-tests d-node))
                               (number (length (discrimination-tests d-node)))
                               (number* (round (/ number 2)))
                               (draw-line?
                                 (or (mem d-node listees)
                                       (mem d-node *callees*)
                                       (some #'(lambda (C) (not (mem c listees))) (discrimination-tests d-node)))))
                       (pushnew d-node listees :test 'equal)
                       (push d-node *callees*)
                       (when (and (not *blank-line*) (> number* 0))
                            (line-indent depth) (terpri) (setf *blank-line* t))
                       (dotimes (n number*)
                           (let ((test (mem1 DC)))
                             (cond
                               ((zerop n)
                                 (display-discrimination-node (cdr test) listees (1+ depth) nil nodes test))
                               ((cdr DC) (display-discrimination-node (cdr test) listees (1+ depth) nil nodes test))
                               (t (display-discrimination-node (cdr test) listees (1+ depth) t nodes test))))
                           (setf DC (cdr DC)))
                       (pushnew depth *line-columns* :test 'eql)
                       (display-d-node d-node depth test)
                       (setf *blank-line* nil)
                       (when last? (pull depth *line-columns*))
                       (when (> number 0) (pushnew (1+ depth) *line-columns* :test 'eql))
                       (dolist (test DC)
                           (cond
                             ((cdr DC)
                               (display-discrimination-node (cdr test) listees (1+ depth) nil nodes test))
                             (t (display-discrimination-node (cdr test) listees (1+ depth) t nodes test)))
                           (setf DC (cdr DC)))
                       (when
                            (and (not *blank-line*) draw-line?)
                            (line-indent depth) (terpri) (setf *blank-line* t))
                       )))))

#| The list of instantiated-premises for a forwards-reason. |#
(defunction reason-ips (reason)
    (let ((ips nil))
      (dolist (dn *discrimination-net*)
          (dolist (ip (d-node-forwards-reasons dn))
              (when (equal (ip-reason ip) reason) (push ip ips))))
      ips))

#| The list of interest-schemes for a backwards-reason. |#
(defunction reason-iss (reason)
    (let ((iss nil))
      (dolist (dn *discrimination-net*)
          (dolist (is (d-node-interest-schemes dn))
              (when (equal (ip-reason is) reason) (push is iss))))
      iss))

(defunction d-node-ancestors (dn)
    (let ((pn (parent-d-node dn)))
      (when pn (cons pn (d-node-ancestors pn)))))

(defunction d-node-descendants (dn)
    (when (discrimination-tests dn)
         (let ((nodes (a-range (discrimination-tests dn))))
           (append nodes (unionmapcar #'d-node-descendants nodes)))))

#| Display the part of the discrimination-net that contains d-node number n. |#
(defunction show-d-node (n)
    (let* ((dn (if (numberp n) (d-node n) n))
              (nodes (cons dn (append (d-node-ancestors dn) (d-node-descendants dn)))))
      (display-discrimination-net nodes)))

(defunction show-interest (n)
    (let* ((in (if (numberp n) (interest n) n))
              (dn (i-list-d-node (interest-i-list in)))
              (nodes (cons dn (append (d-node-ancestors dn) (d-node-descendants dn)))))
      (display-discrimination-net nodes)))

(defunction show-node (n)
    (let* ((node (if (numberp n) (node n) n))
              (dn (c-list-d-node (node-c-list node)))
              (nodes (cons dn (append (d-node-ancestors dn) (d-node-descendants dn)))))
      (display-discrimination-net nodes)))

#| This displays all d-nodes directly relevant to the reason. |#
(defunction show-reason (reason)
    (let ((nodes nil))
      (cond ((forwards-reason-p reason)
                  (dolist (dn *discrimination-net*)
                      (when (some #'(lambda (ip) (equal (ip-reason ip) reason)) (d-node-forwards-reasons dn))
                           (push dn nodes))))
                ((backwards-reason-p reason)
                  (dolist (dn *discrimination-net*)
                      (when
                           (or (member reason (d-node-backwards-reasons dn))
                                 (member reason (d-node-degenerate-backwards-reasons dn))
                                 (some #'(lambda (is) (equal (is-reason is) reason)) (d-node-interest-schemes dn)))
                           (push dn nodes)))))
      (setf nodes
               (unionmapcar+
                 #'(lambda (dn) (cons dn (append (d-node-ancestors dn) (d-node-descendants dn))))
                 nodes))
      (display-discrimination-net nodes)))

(defunction prinp-test (test)
    (princ "(") (princ (caar test)) (princ " . ") (prinp (cdar test)) (princ ") : ") (princ (cdr test)))

(defstruct (c-list (:print-function print-c-list)
                              (:conc-name nil))
    (c-list-formula nil)
    (corresponding-i-lists nil)
    (c-list-nodes nil)
    (c-list-processed-nodes nil)
    (link-defeatees nil)
    (reductio-interests nil)
    (c-list-variables nil)
    (c-list-contradictors nil)
    (c-list-term-list nil)
    (c-list-d-node nil)
    (generated-instantiated-premises nil)
    (supported-interest-schemes nil))

(defun print-c-list (x stream depth)
    (declare (ignore depth))
    (princ "#<c-list for " stream)
    (prinp (c-list-formula x) stream) (princ ">" stream))

(defunction processed-c-list-for (formula)
    (cdr (find-if #'(lambda (cl) (notational-variant formula (car cl))) *processed-conclusions*)))

(defunction notational-variant (p q &optional vars)
    (cond ((null p) (null q))
                ((listp p)
                  (and (listp q)
                            (cond ((and (or (eq (car p) 'some) (eq (car p) 'all))
                                                  (eq (car p) (car q)))
                                                        (notational-variant (cdr p) (cdr q)
                                                                                          (cons (cons (cadr p) (cadr q)) vars)))
                                        ((listp (car q)) (and (notational-variant (car p) (car q) vars)
                                                                    (notational-variant (cdr p) (cdr q) vars)))
                                        ((or (eql (car p) (car q))
                                                (and vars
                                                          (mem (cons (car p) (car q)) vars)))
                                          (notational-variant (cdr p) (cdr q) vars)
                                          ))))
                (t (and (not (listp q))
                             (or (eql p q)
                                   (mem (cons p q) vars))))))

(defunction nodes-for (formula)
    (let ((c-list (c-list-for formula)))
       (if c-list (c-list-nodes c-list))))

(defunction processed-nodes-for (formula)
    (let ((c-list (processed-c-list-for formula)))
       (if c-list (c-list-nodes c-list))))

(defunction display-conclusions ()
    (princ "(") (terpri)
    (princ "================== CONCLUSIONS ===================")
    (let* ((**conclusions**
               (unionmapcar
                 #'(lambda (dn)
                       (unionmapcar
                         #'(lambda (cl) (c-list-nodes cl)) (d-node-c-lists dn)))
                 *discrimination-net*))
              (conclusions
                (order **conclusions**
                            #'(lambda (c1 c2)
                                  (< (inference-number c1) (inference-number c2))))))
       (dolist (conclusion conclusions)
           (display-conclusion conclusion)
           (terpri) (princ "---------------------------------------------------")))
    (princ ")") (terpri))

(defunction display-conclusion (n)
    (terpri) (princ n)
    (when (not (equal (node-kind n) :inference))
         (terpri) (princ "  kind: ") (princ (node-kind n)))
    ; (terpri) (princ "  maximal-degree-of-support: ") (princ (compute-maximal-degree-of-support n))
    (terpri) (princ "  undefeated-degree-of-support: ") (princ (compute-undefeated-degree-of-support n))
    (dolist (Q (answered-queries n))
        (terpri) (princ "  This answers ") (princ Q)))

(defunction display-conclusions-by-supposition ()
    (princ "(") (terpri)
    (let ((suppositions nil))
       (dolist (dn *discrimination-net*)
           (dolist (cl (d-node-c-lists dn))
               (dolist (c (c-list-nodes cl))
                   (pushnew (node-supposition c) suppositions :test '==)
                   (setf suppositions
                            (order suppositions
                                        #'(lambda (s1 s2)
                                              (or (< (length s1) (length s2))
                                                    (and (= (length s1) (length s2))
                                                              (lessp s1 s2)))))))))
       (let* ((**conclusions**
                  (unionmapcar
                    #'(lambda (dn)
                          (unionmapcar
                            #'(lambda (cl) (c-list-nodes cl)) (d-node-c-lists dn)))
                    *discrimination-net*)))
          (dolist (sup suppositions)
              (princ "==========================================") (terpri)
              (princ "Conclusions with supposition ") (set-prinp sup) (princ ":") (terpri)
              (let* ((sup-conclusions
                         (subset #'(lambda (c) (== (node-supposition c) sup))
                                        **conclusions**))
                        (conclusions
                          (order sup-conclusions
                                      #'(lambda (c1 c2)
                                            (< (inference-number c1) (inference-number c2))))))
                 (dolist (c conclusions)
                     (when (== (node-supposition c) sup)
                          (princ "    #") (princ (inference-number c)) (princ "  ")
                          (prinp (node-formula c)) (terpri)))))))
    (princ ")") (terpri))

(defunction display-c-lists ()
    (princ "(") (terpri)
    (dolist (dn *discrimination-net*)
        (dolist (cl (d-node-c-lists dn))
            (princ "==========================================") (terpri)
            (princ "c-list-formula: ") (prinp (c-list-formula cl)) (terpri)
            (let ((conclusions
                      (order (c-list-nodes cl)
                                  #'(lambda (c1 c2)
                                        (let ((s1 (node-supposition c1))
                                                (s2 (node-supposition c2)))
                                           (or (< (length s1) (length s2))
                                                 (and (= (length s1) (length s2))
                                                           (lessp s1 s2))))))))
               (dolist (c conclusions)
                   (princ "    #") (princ (inference-number c))
                   (princ "   sup = ") (set-prinp (node-supposition c))
                   (terpri)))))
    (princ ")") (terpri))

(defunction display-processed-c-lists ()
    (princ "(") (terpri)
    (dolist (cl *processed-conclusions*)
        (princ "==========================================") (terpri)
        (princ "c-list-formula: ") (prinp (car cl)) (terpri)
        (let ((conclusions
                  (order (c-list-nodes (cdr cl))
                              #'(lambda (c1 c2)
                                    (let ((s1 (node-supposition c1))
                                            (s2 (node-supposition c2)))
                                       (or (< (length s1) (length s2))
                                             (and (= (length s1) (length s2))
                                                       (lessp s1 s2))))))))
           (dolist (c conclusions)
               (princ "    #") (princ (inference-number c))
               (princ "   sup = ") (set-prinp (node-supposition c))
               (terpri))))
    (princ ")") (terpri))

(defunction ?-variables (formula)
    (cond ((and formula (listp formula))
                (union (?-variables (car formula)) (?-variables (cdr formula))))
              ((atom formula)
                (if (equal (car (explode (write-to-string formula))) "?") (list formula)))))

#| (? formula), where formula can contain variables of the form "?x",  returns a list of all
known conclusions matching the formula. |#
(defunction ? (formula)
    (when (stringp formula) (setf formula (reform formula)))
    (let* ((d-node (d-node-for formula))
              (nodes (search-d-nodes formula d-node)))
      (cond (nodes
                  (terpri)
                  (princ "The following answers are known for the query (? ") (prinp formula) (princ "):") (terpri)
                  (princ "------------------------------------------------------------------------------------------------------------------------------------------------------------")
                  (terpri)
                   (dolist (node nodes)
                       (princ "    ") (princ (node-formula node)) (princ "    by node #")
                       (princ (inference-number node)) (terpri))
                   (terpri))
                (t
                  (terpri) (princ "No answers are known for the query (? ") (prinp formula) (princ ").") (terpri)
                  (princ "------------------------------------------------------------------------------------------------------------------------------------------------------------")
                  (terpri)
                  (terpri)))
      nodes))

(defunction search-d-nodes (formula d-node)
    (let ((nodes nil)
            (?-vars (?-variables formula)))
      (dolist (c-list (d-node-c-lists d-node))
          (dolist (node (c-list-nodes c-list))
              (when (and (null (node-supposition node))
                                  (match formula (node-formula node) ?-vars))
                   (push node nodes))))
      (append nodes
                     (unionmapcar #'(lambda (dt) (search-d-nodes formula (cdr dt)))
                                             (discrimination-tests d-node)))))

(defunction ?interests (formula)
    (when (stringp formula) (setf formula (reform formula)))
    (let* ((d-node (d-node-for formula))
              (interests (search-d-node-interests formula d-node)))
      (cond (interests
                  (terpri)
                  (princ "The following interests were adopted for the query (? ") (prinp formula) (princ "):") (terpri)
                  (princ "------------------------------------------------------------------------------------------------------------------------------------------------------------")
                  (terpri)
                   (dolist (interest interests)
                       (princ "    ") (princ (interest-formula interest)) (princ "    by interest #")
                       (princ (interest-number interest)) (terpri))
                   (terpri))
                (t
                  (terpri) (princ "No interests were adopted for the query (? ") (prinp formula) (princ ").") (terpri)
                  (princ "------------------------------------------------------------------------------------------------------------------------------------------------------------")
                  (terpri)
                  (terpri)))
      interests))

(defunction search-d-node-interests (formula d-node)
    (let ((interests nil)
            (?-vars (?-variables formula)))
      (dolist (i-list (d-node-i-lists d-node))
          (dolist (interest (i-list-interests i-list))
              (when (and (null (node-supposition interest))
                                  (match formula (interest-formula interest) ?-vars))
                   (push interest interests))))
      (append interests
                     (unionmapcar #'(lambda (dt) (search-d-node-interests formula (cdr dt)))
                                             (discrimination-tests d-node)))))

; ---------------------------- ULTIMATE-EPISTEMIC-INTERESTS -----------------------------

(defstruct (query (:print-function print-query)
                                (:conc-name nil))
   (query-number 0)
   (query-formula nil)
   (query-strength 0)
   (query-queue-node nil)
   (deductive-query nil)  ;; t if the query is whether the query formula is deductively provable
   (positive-query-instructions nil) ;; a list of functions applicable to an inference-node
   (negative-query-instructions nil) ;; a list of functions applicable to an inference-node
   (query-answers nil)  ;;a list of inference-nodes
   (answered? nil)  ;; t if some answer is justified to degree greater than or equal
                                   ;; to the degree of interest, nil otherwise
   (query-interest nil)   ;; the interest recording the query
   (negative-query-interest nil)  ;; the negative-interest for a whether-query
   (?-constraint nil))  ;; a function which when applied to the ?-vars yields a discharge-condition
                                    ;; for the query-interest, constraining the instantiating terms.

(defun print-query (x stream depth)
    (declare (ignore depth))
    (princ "#<" stream) (princ "Query " stream) (princ (query-number x) stream)
    (princ ": " stream) (princ (pretty (query-formula x)) stream)
    (princ ">" stream))

(defunction ?-query-p (Q)
    (and (query-p Q) (?-genp (query-formula Q))))

#| This returns two values: the matrix, and the list of ?-variables. |#
(defunction ?-matrix (p &optional vars)
    (push (q-variable p) vars)
    (let ((formula (q-matrix p)))
       (cond ((?-genp formula) (?-matrix formula vars))
                   (t (values formula vars)))))

(defunction whether-query-p (Q)
    (and (query-p Q) (whether-formula (query-formula Q))))

(defunction query (n)
    (find-if #'(lambda (c) (equal (query-number c) n))
                 *ultimate-epistemic-interests*))

(defunction show-query (Q)
    (if (numberp Q) (setf Q (query Q)))
    (princ Q) (terpri))

(defunction show-queries ()
    (terpri)
    (princ
      "================== ULTIMATE EPISTEMIC INTERESTS ===================")
    (terpri)
    (dolist (Q *ultimate-epistemic-interests*)
        (show-query Q)))

(defunction inclusive-node-ancestors (node)
    (cons node (node-ancestors node)))

(defunction ancestral-links (node)
    (unionmapcar+ #'support-links (inclusive-node-ancestors node)))

(defunction display-query (Q)
    (princ "  Interest in ") (prinp (query-formula Q)) (terpri)
    (cond ((null (answered? Q))
                 (princ "  is unsatisfied.")
                 (when (null (query-answers Q)) (princ "  NO ARGUMENT WAS FOUND."))
                 (terpri))
                ((or (whether-query-p Q) (?-query-p Q))
                  (dolist (C (query-answers Q))
                      (when (>= (compute-undefeated-degree-of-support C) (query-strength Q))
                           (princ "  is answered by node ")
                           (princ (inference-number C)) (princ ":  ")
                           (princ (pretty (node-formula C))) (terpri)
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

(defunction display-queries ()
    (terpri)
    (princ
      "================== ULTIMATE EPISTEMIC INTERESTS ===================")
    (terpri)
    (dolist (Q *ultimate-epistemic-interests*)
        (display-query Q)))

(defunction answers (formula query)
   (let ((query-formula (query-formula query)))
     (if (?-genp query-formula)
       (instance-of formula query-formula)
       (equal formula query-formula))))

#| This assumes that formula2 is indefinite. |#
(defunction instance-of (formula1 formula2)
    (match (mem2 formula2) formula1 (list (mem2 (mem1 formula2)))))

(defunction in-interest (sequent)
    (let ((interests (interests-for (sequent-formula sequent) nil)))
       (when interests
            (some #'(lambda (interest) (null (interest-supposition interest)))
                         interests))))

(defunction adopt-ultimate-interest (query)
    (push query *ultimate-epistemic-interests*)
    (when (not (in-interest (list nil (query-formula query))))
         (queue-query-for-interest query)))

(defunction queue-query-for-interest (query)
    (let ((node
              (make-inference-queue-node
                :queue-number (incf *queue-number*)
                :enqued-item query
                :item-kind :query
                :item-complexity (complexity (query-formula query))
                :discounted-strength (query-strength query)
                :degree-of-preference (query-preference query))))
       (setf (query-queue-node query) node)
       (setf *inference-queue* (ordered-insert node *inference-queue* #'i-preferred))))

; -------------------------------------- INTERESTS --------------------------------------

(defstruct (instantiated-premise (:print-function print-instantiated-premise) (:conc-name ip-))
    (reason nil)
    (binding nil)  ;; cumulative binding prior to this premise
    (basis nil)
    (premise nil)
    (remaining-premises nil)  ;; premises left to be instantiated
    (instantiations nil)  ;; instantiations of node-variables in previous premises
    (used-premise-variables nil)  ;; premise-variables bound in earlier premises
    (used-variables nil)  ;; conclusion-variables occurring in basis
    (derived-premises nil)  ;; instantiated-premises immediately following this one
    (d-node nil)
    (number 0)
    (clues nil)
     (initial?  nil))   ;; records whether the premise is the initial premise of the reason

(defun print-instantiated-premise (x stream depth)
    (declare (ignore depth))
    (princ "<instantiated-premise " stream) (princ (ip-number x) stream) (princ " for " stream)
    (princ (ip-reason x) stream)
    (princ ">" stream))

(defstruct (interest-scheme (:include instantiated-premise)
                                                    (:print-function print-interest-scheme) (:conc-name is-))
    (target-interest nil)
    (supposition nil)
    (supposition-variables nil)
    (instance-function nil)
    (generating-node nil))

(defun print-interest-scheme (x stream depth)
    (declare (ignore depth))
    (princ "<<interest-scheme " stream) (princ (is-number x) stream) (princ " for " stream)
    (princ (is-target-interest x) stream) (princ " by " stream) (princ (ip-reason x) stream) (princ ">>" stream))

#| This finds the interest-scheme with is-number n. |#
(defunction interest-scheme (n)
    (let ((is nil))
      (some #'(lambda (dn)
                       (find-if #'(lambda (i)
                                         (and (equal (is-number i) n)
                                                  (setf is i)))
                                   (d-node-interest-schemes dn)))
                  *discrimination-net*)
      is))

#| This finds the instantiated-premise with ip-number n. |#
(defunction instantiated-premise (n)
    (let ((ip nil))
      (some #'(lambda (dn)
                       (find-if #'(lambda (i)
                                         (and (equal (ip-number i) n)
                                                  (setf ip i)))
                                   (d-node-forwards-reasons dn)))
                  *discrimination-net*)
      ip))

(defmacro is-derived-interest-schemes (is) `(is-derived-premises ,is))

(defstruct (interest-link (:print-function print-interest-link)
                                           (:conc-name nil))   ; "An interest-graph-link"
    (link-number 0)
    (resultant-interest nil)
    (link-interest nil)
    (link-interest-formula nil)
    (link-interest-condition nil)
    (link-binding nil)
    (link-rule nil)
    (remaining-premises nil)
    (supporting-nodes nil)
    (link-instantiations nil)
    (link-supposition nil)
    (link-defeaters nil)
    (link-defeat-status nil)
    (link-strength 0)  ; maximum-degree-of-interest conveyed
    (link-generating-node nil)
    (discharged-link nil)
    (interest-match nil)
    (interest-reverse-match nil)
    (generating-link nil)
    (link-premise nil)
    (link-clues nil)
    )

(defun print-interest-link (x stream depth)
    (declare (ignore depth))
    (princ "#<" stream) (princ "Link " stream)
    (princ (link-number x) stream)
    (when (resultant-interest x)
      (princ ": for  interest #" stream) (princ (interest-number (resultant-interest x)) stream))
    (princ " by " stream) (princ (link-rule x) stream)
    (princ ">" stream))

(defunction link (n)
    (find-if #'(lambda (node) (equal (link-number node) n)) *interest-links*))

(defunction display-links ()
    (dolist (L *interest-links*) (princ L) (terpri)))

(defunction display-link (L)
    (princ "INTEREST-LINK #") (princ (link-number L)) (terpri)
    (princ "  resultant-interest: ") (princ (resultant-interest L)) (terpri)
    (princ "  supporting-nodes: ") (princ (supporting-nodes L)) (terpri)
    (princ "  link-interest: ") (princ (link-interest L)) (terpri)
    (princ "  remaining-premises: ") (princ (remaining-premises L)) (terpri)
    (princ "  reason: ") (princ (link-rule L)) (terpri)
    (princ "  link-interest: ") (princ (link-interest L)) (terpri)
    )

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
    (reductio-interest nil)  ;; is the interest partly for reductio?
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
   (non-reductio-interest t)  ;; is the interest partly for non-reductio?
    (anchored-nodes nil)
    (text-discharge-condition nil)  ;; a text statement of the discharge condition
    (enabled-nodes nil)  ;; the nodes for which this is an enabling-interest
    )

#|
(defun print-interest (x stream depth)
    (declare (ignore depth))
    (princ "#<" stream) (princ "Interest " stream)
    (princ (interest-number x) stream)
    (princ ": " stream) (prinp-sequent (interest-sequent x) stream)
    (princ ">" stream))
|#

(defun print-interest (x stream depth)
    (declare (ignore depth))
    (princ "#<" stream) (princ "Interest " stream)
    (princ (interest-number x) stream)
   ; (princ ": " stream) (prinp-sequent (interest-sequent x) stream)
    (princ ">" stream))

(defunction ifm (n)
    (when (numberp n) (setf n (interest n)))
    (prinp (interest-formula n))
    (interest-formula n))

(defstruct (i-list (:print-function print-i-list)
                              (:conc-name nil))
    (i-list-formula nil)
    (corresponding-c-lists nil)
    (i-list-interests nil)
    (i-list-queries nil)
    (reductio-trigger nil)
    (i-list-reductio-supposition nil)
    (i-list-variables)
    (i-list-term-list nil)
    (i-list-d-node nil))

(defun print-i-list (x stream depth)
    (declare (ignore depth))
    (princ "#<i-list for " stream)
    (prinp (i-list-formula x) stream) (princ ">" stream))

#| This returns three values -- the i-list and the match and its reverse. |#
(defunction i-list-for (formula i-vars)
    (multiple-value-bind (profile term-list) (formula-code formula)
         (let ((d-node (pursue-d-node-for profile *top-d-node*)))
           (when d-node
                (some
                  #'(lambda (il)
                        (multiple-value-bind
                             (match match*)
                             (one-one-match term-list (i-list-term-list il) i-vars (i-list-variables il))
                             (when match
                                  (return-from i-list-for (values il match match*)))))
                  (d-node-i-lists d-node))))))

#| If p and q match one-one, this returns the match and its reverse-match. |#
(defunction one-one-match (p q p-vars q-vars)
    (let* ((match (match p q p-vars))
              (match* (reverse-match match)))
       (when
            (and match
                      (or (eq match t)
                            (and
                              (subsetp (a-range match) q-vars)
                              (equal (match-sublis match* q) p))))
            (values match match*))))

#| This returns two values -- the list of interests, and the match |#
(defunction interests-for (formula i-vars)
    (multiple-value-bind
         (i-list match)
         (i-list-for formula i-vars)
         (if i-list (values (i-list-interests i-list) match))))

#| c-variables is the list of node-variables. |#
(defunction matching-i-lists-for (term-list c-variables d-node)
    (let ((i-lists nil))
       (dolist (il (d-node-i-lists d-node))
           (let ((unifier (unifier term-list (i-list-term-list il) c-variables (i-list-variables il))))
              (if unifier (push (list il unifier) i-lists))))
       i-lists))

#| c-variables is the list of node-variables. |#
(defunction matching-c-lists-for (term-list i-variables d-node)
    (let ((c-lists nil))
       (dolist (cl (d-node-c-lists d-node))
           (let ((unifier (unifier  (c-list-term-list cl) term-list (c-list-variables cl) i-variables)))
              (if unifier (push (list cl unifier) c-lists))))
       c-lists))

(defunction store-interest (interest &optional i-list)
   ; (when (eq (interest-number interest) 11) (setf i interest il i-list) (break))
    ;; (step (store-interest i il))
    (push interest *interests*)
    (cond (i-list
                 (push interest (i-list-interests i-list))
                 (let ((reductio-sup (i-list-reductio-supposition i-list)))
                    (when reductio-sup
                         (push interest  (generating-interests reductio-sup))
                         (push reductio-sup (generated-suppositions interest))))
                 (setf (interest-i-list interest) i-list))
                (t
                  (multiple-value-bind (profile term-list) (formula-code (interest-formula interest))
                       (index-interest interest profile term-list *top-d-node*)))))

#| (descrimination-tests d-node) is an a-list of pairs (test . dn), where test has the form of the
car of a formula-code, and dn is a d-node. |#
(defunction index-interest (interest profile term-list d-node)
    (let ((dn (e-assoc (car profile) (discrimination-tests d-node)))
            (new-profile (cdr profile)))
      (cond (dn
                  (if new-profile (index-interest interest new-profile term-list dn)
                       (store-interest-at-d-node interest term-list dn)))
                (new-profile
                  (index-interest-at-new-nodes interest term-list d-node new-profile (car profile)))
                (t (store-interest-at-new-d-node
                      interest term-list d-node (car profile))))))

(defunction fetch-I-list-for (term-list d-node)
    (find-if #'(lambda (il)
                      (equal term-list (i-list-term-list il)))
                 (d-node-i-lists d-node)))

(defunction store-interest-at-d-node (interest term-list dn)
   ; (when (eq interest (interest 11)) (setf i interest tl term-list d dn) (break))
    ;; (step (store-interest-at-d-node i tl d))
    (let* ((formula (interest-formula interest))
              (i-variables (interest-variables interest))
              (i-list (fetch-i-list-for term-list dn)))
       (cond (i-list
                    (push interest (i-list-interests i-list))
                    (let ((reductio-sup (i-list-reductio-supposition i-list)))
                       (when reductio-sup
                            (push interest  (generating-interests reductio-sup))
                            (push reductio-sup (generated-suppositions interest)))))
                   (t (let ((c-lists (matching-c-lists-for term-list i-variables dn)))
                         (setf i-list (make-i-list
                                            :i-list-formula formula
                                            :corresponding-c-lists c-lists
                                            :i-list-interests (list interest)
                                            :reductio-trigger
                                            (appropriate-for-reductio-supposition formula)
                                            :i-list-variables i-variables
                                            :i-list-term-list term-list
                                            :i-list-d-node dn
                                            ))
                         (push i-list (d-node-i-lists dn))
                         (dolist (cl c-lists)
                             (push (cons i-list (cdr cl)) (corresponding-i-lists (mem1 cl)))))))
       (setf (interest-i-list interest) i-list)))

#| Test is the final member of the formula-profile for the node-formula. |#
(defunction store-interest-at-new-d-node (interest term-list d-node test)
   ; (when (eq interest (interest 7)) (setf i interest tl term-list d d-node ts test) (break))
    ;; (step (store-interest-at-new-node i tl d ts))
    (let* ((i-variables (interest-variables interest))
              (formula (interest-formula interest))
              (dn (make-d-node
                       :d-node-number (incf *d-node-number*)
                       :d-node-description (cons test (d-node-description d-node))
                       :parent-d-node d-node))
              (i-list (make-i-list
                          :i-list-formula formula
                          :i-list-interests (list interest)
                          :reductio-trigger
                          (appropriate-for-reductio-supposition formula)
                          :i-list-variables i-variables
                          :i-list-term-list term-list
                          :i-list-d-node dn
                          )))
       (push dn *discrimination-net*)
       (push (cons test dn) (discrimination-tests d-node))
       (setf (d-node-i-lists dn) (list i-list))
       (setf (interest-i-list interest) i-list)))

(defunction find-matching-i-lists-for (formula variables)
    (multiple-value-bind (profile term-list) (formula-code formula)
         (pursue-i-lists-for formula profile term-list variables *top-d-node*)))

(defunction pursue-i-lists-for (formula profile term-list variables d-node)
    (let ((dn (e-assoc (car profile) (discrimination-tests d-node))))
       (when dn
            (let ((new-profile (cdr profile)))
               (cond
                 (new-profile (pursue-i-lists-for formula new-profile term-list variables dn))
                 (t (matching-i-lists-for term-list variables dn)))))))

(defunction index-interest-at-new-nodes (interest term-list d-node profile test)
    (let ((dn (make-d-node
                     :d-node-number (incf *d-node-number*)
                     :d-node-description (cons test (d-node-description d-node))
                     :parent-d-node d-node)))
       (push (cons test dn) (discrimination-tests d-node))
       (push dn *discrimination-net*)
       (let ((desc (cdr profile)))
          (cond (desc (index-interest-at-new-nodes interest term-list dn desc (car profile)))
                      (t (store-interest-at-new-d-node interest term-list dn (car profile)))))))

(defunction pursue-d-node-for (profile d-node)
    (let ((dn (e-assoc (car profile) (discrimination-tests d-node))))
       (when dn
            (let ((new-profile (cdr profile)))
               (cond
                 (new-profile (pursue-d-node-for new-profile dn))
                 (t dn))))))

(defunction store-interest-with-c-lists (interest c-lists)
  ;  (when (eq (interest-number interest) 25) (setf i interest cl c-lists) (break))
    ;; (step (store-interest-with-c-lists i cl))
    (multiple-value-bind (profile term-list) (formula-code (interest-formula interest))
         (declare (ignore profile))
         (cond
           (c-lists
             (push interest *interests*)
             (let* ((formula (interest-formula interest))
                       (dn (c-list-d-node (caar c-lists)))
                       (i-list (fetch-i-list-for term-list dn))
                       (i-variables (interest-variables interest)))
                (cond (i-list
                             (push interest (i-list-interests i-list))
                             (let ((reductio-sup (i-list-reductio-supposition i-list)))
                                (when reductio-sup
                                     (push interest  (generating-interests reductio-sup))
                                     (push reductio-sup (generated-suppositions interest)))))
                            (t (setf i-list (make-i-list
                                                  :i-list-formula formula
                                                  :corresponding-c-lists c-lists
                                                  :i-list-interests (list interest)
                                                  :reductio-trigger
                                                  (appropriate-for-reductio-supposition formula)
                                                  :i-list-variables i-variables
                                                  :i-list-term-list term-list
                                                  :i-list-d-node dn
                                                  ))
                                (push i-list (d-node-i-lists dn))
                                (dolist (cl c-lists)
                                    (push (cons i-list (cdr cl)) (corresponding-i-lists (mem1 cl))))))
                (setf (interest-i-list interest) i-list)))
           (t (store-interest interest)))))

(defunction appropriate-for-reductio-supposition (formula)
    (and
      (not (conjunctionp formula))
      (not (conditionalp formula))
      (not (biconditionalp formula))
      (not (disjunctionp formula))
      (not (u-genp formula))
      (not (undercutterp formula))
      (or (not (negationp formula))
            (atomic-formula (mem2 formula)))))

(defunction store-inference-node (node formula)
   ; (when (eql (inference-number node) 14) (setf n node f formula) (break))
    ;; (step (store-inference-node n f))
    (multiple-value-bind (profile term-list) (formula-code formula)
         (index-inference-node node profile term-list *top-d-node*)))

#| (descrimination-tests d-node) is an a-list of pairs (test . dn), where test has the form of the
car of a formula-code, and dn is a d-node. |#
(defunction index-inference-node (node profile term-list d-node)
    (let ((dn (e-assoc (car profile) (discrimination-tests d-node)))
            (new-profile (cdr profile)))
       (cond (dn
                    (if new-profile (index-inference-node node new-profile term-list dn)
                         (store-inference-node-at-d-node node term-list dn)))
                   (new-profile
                     (index-inference-node-at-new-nodes node term-list d-node new-profile (car profile)))
                   (t
                     (store-inference-node-at-new-d-node
                        node term-list d-node (car profile))))))

(defunction fetch-c-list-for (formula d-node)
    (find-if #'(lambda (cl) (notational-variant formula (c-list-formula cl)))
                 (d-node-c-lists d-node)))

(defunction store-inference-node-at-d-node (node term-list dn)
    (let* ((formula (node-formula node))
              (c-list (fetch-c-list-for formula dn))
              (c-variables (node-variables node)))
       (cond (c-list
                    (if (is-inference node) (push node (c-list-nodes c-list))))
                   (t (let ((i-lists (matching-i-lists-for term-list c-variables dn)))
                         (setf c-list (make-c-list
                                             :c-list-formula formula
                                             :corresponding-i-lists i-lists
                                             :c-list-nodes (if (is-inference node) (list node))
                                             :reductio-interests
                                             (appropriate-for-reductio-interest formula)
                                             :c-list-variables c-variables
                                             :c-list-term-list term-list
                                             :c-list-d-node dn
                                             ))
                         (push c-list (d-node-c-lists dn))
                         (dolist (il i-lists)
                             (push (cons c-list (cdr il)) (corresponding-c-lists (mem1 il)))))
                       (when
                            (appropriate-for-contradictors formula)
                            (setf (c-list-contradictors c-list)
                                     (find-matching-c-lists-for (neg formula) (c-list-variables c-list)))
                            (dolist (cl (c-list-contradictors c-list))
                                (push (list c-list (reverse (mem2 cl)))
                                            (c-list-contradictors (mem1 cl)))))))
       (setf (node-c-list node) c-list)))

#| Test is the final member of the formula-profile for the node-formula. |#
(defunction store-inference-node-at-new-d-node (node term-list d-node test)
    (let* ((c-variables (node-variables node))
              (dn (make-d-node
                       :d-node-number (incf *d-node-number*)
                       :d-node-description (cons test (d-node-description d-node))
                       :parent-d-node d-node))
              (formula (node-formula node))
              (c-list (make-c-list
                          :c-list-formula formula
                          :c-list-nodes (list node)
                          :reductio-interests
                          (appropriate-for-reductio-interest formula)
                          :c-list-variables c-variables
                          :c-list-term-list term-list
                          :c-list-d-node dn
                          )))
       (push dn *discrimination-net*)
       (push (cons test dn) (discrimination-tests d-node))
       (setf (d-node-c-lists dn) (list c-list))
       (when
            (appropriate-for-contradictors formula)
            (setf (c-list-contradictors c-list)
                     (find-matching-c-lists-for (neg formula) (c-list-variables c-list)))
            (dolist (cl (c-list-contradictors c-list))
                (push (list c-list (reverse (mem2 cl)))
                            (c-list-contradictors (mem1 cl)))))
       (setf (node-c-list node) c-list)))

(defunction find-matching-c-lists-for (formula variables)
    (multiple-value-bind (profile term-list) (formula-code formula)
         (pursue-c-lists-for formula profile term-list variables *top-d-node*)))

(defunction pursue-c-lists-for (formula profile term-list variables d-node)
    (let ((dn (e-assoc (car profile) (discrimination-tests d-node))))
       (when dn
            (let ((new-profile (cdr profile)))
               (cond
                 (new-profile (pursue-c-lists-for formula new-profile term-list variables dn))
                 (t (matching-c-lists-for term-list variables dn)))))))

(defunction index-inference-node-at-new-nodes (node term-list d-node profile test)
    (let ((dn (make-d-node
                     :d-node-number (incf *d-node-number*)
                     :d-node-description (cons test (d-node-description d-node))
                     :parent-d-node d-node)))
       (push (cons test dn) (discrimination-tests d-node))
       (push dn *discrimination-net*)
       (let ((desc (cdr profile)))
          (cond (desc (index-inference-node-at-new-nodes node term-list dn desc (car profile)))
                      (t (store-inference-node-at-new-d-node node term-list dn (car profile)))))))

(defunction d-node-for (formula)
    (let ((profile (formula-code formula)))
         (pursue-d-node-for profile *top-d-node*)))

(defunction c-list-for (formula)
    (let ((d-node (d-node-for formula)))
       (if d-node
          (fetch-c-list-for formula d-node))))

(defunction pursue-c-list-for (formula profile d-node)
    (let ((dn (e-assoc (car profile) (discrimination-tests d-node))))
       (when dn
            (let ((new-profile (cdr profile)))
               (cond
                 (new-profile (pursue-c-list-for formula new-profile dn))
                 (t (fetch-c-list-for formula dn)))))))

(defunction store-inference-node-with-c-list (node formula c-list)
    ; (when (equal *inference-number* 31) (setf c node f formula cl c-list) (break))
    ;; (step (store-inference-node-with-c-list c f cl))
    (cond (c-list
                 (push node (c-list-nodes c-list))
                 (setf (node-c-list node) c-list))
                (t (store-inference-node node formula))))

(defunction appropriate-for-reductio-interest (formula)
    (and
      (not (conjunctionp formula))
      (not (disjunctionp formula))   ;; if we use disj-simp
      (not (biconditionalp formula))
      (or (not (conditionalp formula))                                         ;; these assume:
            (and (not (conjunctionp (antecedent formula)))       ;; exportation
                      (not (disjunctionp (antecedent formula)))        ;; disj-antecedent-simp
                      (not (conditionalp (antecedent formula)))))     ;; cond-antecedent-simp
      (not (u-genp formula))
      (not (e-genp formula))
      (or (not (negationp formula))
            (atomic-formula (negand formula))
            (undercutterp (negand formula)))))

(defunction appropriate-for-contradictors (formula)
    (and
      (not (conjunctionp formula))
      (not (disjunctionp formula))   ;; if we use disj-simp
      (not (biconditionalp formula))
      (not (u-genp formula))
      (not (e-genp formula))
      (or (not (negationp formula))
            (atomic-formula (mem2 formula))
            (undercutterp (mem2 formula))
            (conditionalp (mem2 formula)))))

(defunction cancelled-c-list-for (formula)
    (e-assoc formula *cancelled-c-lists*))

(defunction store-processed-inference-node (node)
    (setf (processed? node) T)
    (push node (c-list-processed-nodes (node-c-list node))))

#| This finds the interest with interest-number n. |#
(defunction interest (n)
    (find-if #'(lambda (i) (eql (interest-number i) n)) *interests*))

#| This returns the degree of interest for either an interest or a query. |#
(defunction degree-of-interest* (n)
    (if (interest-p n) (degree-of-interest n) (query-strength n)))

(defunction interest-sequent* (n)
    (if (interest-p n) (interest-sequent n) (list nil (query-formula n))))

(defunction display-interest (interest)
    (if (numberp interest) (setf interest (interest interest)))
    (princ "                                        # ") (princ (interest-number interest)) (princ "  ")
    (when (deductive-interest interest) (princ "deductive "))
    (when (reductio-interest interest) (princ "reductio "))
    (princ "interest:")
    (terpri)
    (princ "                                           ") (prinp  (interest-formula interest))
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

(defunction display-discharge-condition (interest link)
    (let ((binding
              (mapcar
                #'(lambda (x) (cons (car x) (if (and (cdr x) (listp (cdr x))) (list 'quote (cdr x)) (cdr x))))
                (link-binding link))))
      (print-pretty  (sublis binding (text-discharge-condition interest)))))

(defunction display-interests ()
    (princ "(") (terpri)
    (princ "================== INTERESTS ===================")
    (terpri)
    (let* ((**interests**
                (unionmapcar
                  #'(lambda (dn)
                        (unionmapcar #'(lambda (il) (i-list-interests il)) (d-node-i-lists dn)))
                  *discrimination-net*))
              (interests
                (order **interests**
                           #'(lambda (c1 c2)
                                 (< (interest-number c1) (interest-number c2))))))
      (dolist (interest interests)
          (princ "#") (princ (interest-number interest))
          (cond ((deductive-interest interest) (princ "  deductive interest: "))
                    ((reductio-interest interest) (princ "  reductio interest: "))
                    (t (princ "  interest: ")))
          (prinp (interest-formula interest))
          (when (interest-supposition interest)
               (princ "    supposition: ")
               (set-prinp (interest-supposition interest)))
          (terpri)
          (when
               (some #'(lambda (L) (query-p (resultant-interest L)))
                           (right-links interest))
               (princ "     This is of ultimate interest") (terpri))
          (dolist (L (right-links interest))
              (when (not (query-p (resultant-interest L)))
                   (princ "     For ")
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
          (when (interest-defeatees interest)
               (princ "     For the defeat of ")
               (print-list (mapcar #'inference-number (interest-defeatees interest)))
               (terpri))
          (princ "---------------------------------------------------") (terpri)))
    (princ ")") (terpri))

#| This builds chains of inference-ancestors. |#
(defunction interest-ancestor-chains (interest)
    (cond ((interest-p interest)
                 (let ((links (right-links interest)))
                    (cond ((null links) (list (list (list interest))))
                                (t
                                  (unionmapcar
                                    #'(lambda (L)
                                          (mapcar
                                            #'(lambda (c)
                                                  (cons (list interest L) c))
                                            (interest-ancestor-chains (resultant-interest L))))
                                    links)))))
                (t (list nil))))

#| This is like interest-ancestor-chains, but leaves out the links. |#
(defunction right-branches (interest)
    (if (interest-p interest)
       (let ((links (right-links interest)))
          (cond ((null links) (list (list interest)))
                      (t
                        (unionmapcar
                          #'(lambda (L)
                                (mapcar
                                  #'(lambda (c)
                                        (cons interest c))
                                  (right-branches (resultant-interest L))))
                           links))))))

(defunction good-interest-ancestor-chains (interest)
    (if (interest-p interest)
       (let ((links (right-links interest)))
          (cond ((null links) (list (list (list interest))))
                      (t
                        (let ((i-list (interest-i-list interest)))
                        (unionmapcar
                          #'(lambda (L)
                                (remove nil
                                (mapcar
                                  #'(lambda (c)
                                        (when
                                             (and
                                               (not
                                                 (and
                                                   (equal (link-rule L) reductio)
                                                   (or
                                                     (and
                                                       (mem2 (mem1 c))
                                                       (equal (link-rule (mem2 (mem1 c))) reductio))
                                                     (some #'(lambda (x)
                                                                       (and (mem2 x)
                                                                                 (equal (link-rule (mem2 x)) reductio)
                                                                                 (equal (interest-i-list (mem1 x))
                                                                                              i-list)))
                                                                  c)))))
                                             (cons (list interest L) c)))
                                  (good-interest-ancestor-chains (resultant-interest L)))))
                           links)))))))

;(defun display-good-interest-map ()
;    (terpri)
;    (let ((endpoints nil))
;       (dolist (i-list *interests*)
;           (dolist (interest (i-list-interests (cdr i-list)))
;               (when (null (left-links interest))
;                    (push interest endpoints))))
;       (princ "Endpoints of interest map: ")
;       (print-list (mapcar #'interest-number endpoints) 40) (terpri)
;      ; (setf *endpoints* endpoints)
;       (setf *interest-map* nil)
;       (dolist (i endpoints)
;           (princ "==============") (terpri)
;           (let ((chains (good-interest-ancestor-chains i)))
;              (cond (chains
;                           (princ "Chains for ") (princ i) (terpri)
;                           (dolist (c chains)
;                               (push c *interest-map*)
;                               (display-interest-ancestor-chain c)))
;                          (t (princ "No chains for ") (princ i) (terpri))))))
;    (princ "==============") (terpri) (terpri))
;
;(defun circular-chain (c)
;    (some #'(lambda (x)
;                        (some #'(lambda (y)
;                                            (equal (interest-i-list (mem1 x)) (interest-i-list (mem1 y))))
;                                      (cdr (mem x c))))
;                  c))
;
;(defun nested-reductio (c)
;    (some #'(lambda (x)
;                        (and
;                          (mem2 x)
;                          (equal (link-rule (mem2 x)) reductio)
;                          (let ((y (mem2 (car (cdr (mem x c))))))
;                             (and y (equal (link-rule y) reductio)))))
;                  c))
;
;(defun display-interest-ancestor-chain (c)
;    (dolist (n c)
;        (print-sequent (interest-sequent (mem1 n)))
;        (when (mem2 n)
;             (princ " <=") (princ (link-number (mem2 n))) (princ "= ")))
;    (terpri))
;
;(defun display-interest-ancestor-chains (n)
;    (dolist (c (interest-ancestor-chains (interest n)))
;        (display-interest-ancestor-chain c)))
;
;#| This builds chains of interests derived from interest. |#
;(defunction interest-chains (interest)
;    (if (interest-p interest)
;       (let ((links (left-links interest)))
;          (cond ((null links) (list (list (interest-number interest))))
;                      (t (mapcar #'(lambda (c) (cons (interest-number interest) c))
;                                          (unionmapcar=
;                                            #'(lambda (L) (interest-chains (link-interest L)))
;                                            links)))))))
;
;(defun display-interest-chain (c)
;    (print-sequent (interest-sequent (interest (mem1 c))))
;    (dolist (n (cdr c))
;        (princ " => ") (print-sequent (interest-sequent (interest n))))
;    (terpri))
;
;(defun interest-map ()
;    (let ((endpoints nil))
;                     (dolist (i-list *interests*)
;                         (dolist (interest (i-list-interests (cdr i-list)))
;                             (when (null (right-links interest))
;                                  (push interest endpoints))))
;       (unionmapcar #'interest-chains endpoints)))
;
;(defun display-interest-map (&optional n)
;    (terpri)
;    (let ((endpoints nil))
;       (cond (n (setf endpoints (list (interest n))))
;                   (t
;                     (dolist (i-list *interests*)
;                         (dolist (interest (i-list-interests (cdr i-list)))
;                             (when (null (right-links interest))
;                                  (push interest endpoints))))))
;       (cond ((null n)
;                    (princ "Endpoints of interest map: ")
;                    (print-list (mapcar #'interest-number endpoints) 40) (terpri))
;                   (t (princ "Interest-chains for interest #") (princ n) (terpri)))
;       (setf *interest-map* nil)
;       (dolist (i endpoints)
;           (princ "==============") (terpri)
;           (dolist (c (interest-chains i))
;               (push c *interest-map*)
;              ; (display-interest-chain c)
;               )))
;    (princ "==============") (terpri)
;    (terpri))

(defun derived-interests (interest)
    (mapcar #'link-interest (left-links interest)))

(defun print-sequent (S)
    (prinp (sequent-formula S)) (princ "/") (set-prinp (sequent-supposition S)))

(defunction display-interests-by-supposition ()
    (princ "(") (terpri)
    (let ((suppositions nil))
       (dolist (dn *discrimination-net*)
           (dolist (il (d-node-i-lists dn))
               (dolist (c (i-list-interests il))
                   (pushnew (interest-supposition c) suppositions :test '==)
                   (setf suppositions
                            (order suppositions
                                        #'(lambda (s1 s2)
                                              (or (< (length s1) (length s2))
                                                    (and (= (length s1) (length s2))
                                                              (lessp s1 s2)))))))))
       (let* ((**interests**
                  (unionmapcar
                    #'(lambda (dn)
                          (unionmapcar #'(lambda (il) (i-list-interests il)) (d-node-i-lists dn)))
                    *discrimination-net*)))
          (dolist (sup suppositions)
              (princ "==========================================") (terpri)
              (princ "Interests with supposition ") (set-prinp sup) (princ ":") (terpri)
              (let* ((sup-interests
                         (subset #'(lambda (c) (== (interest-supposition c) sup))
                                        **interests**))
                        (interests
                          (order sup-interests
                                      #'(lambda (c1 c2)
                                            (< (interest-number c1) (interest-number c2))))))
                 (dolist (c interests)
                     (when (== (interest-supposition c) sup)
                          (princ "    #") (princ (interest-number c)) (princ "  ")
                          (prinp (interest-formula c)) (princ "     ")
                          (when (reductio-interest c) (princ "reductio "))
                          (princ "for  ")
                          (print-list
                            (remove-duplicates=
                              (mapcar
                                #'(lambda (L) (interest-number (resultant-interest L)))
                                (right-links c))) 40)
                          (terpri)))))))
    (princ ")") (terpri))

(defunction display-i-lists ()
    (princ "(") (terpri)
    (dolist (dn *discrimination-net*)
        (dolist (il (d-node-i-lists dn))
            (princ "==========================================") (terpri)
            (princ "i-list-formula: ") (prinp (i-list-formula il)) (terpri)
            (let ((interests
                      (order (i-list-interests il)
                                  #'(lambda (c1 c2)
                                        (let ((s1 (interest-supposition c1))
                                                (s2 (interest-supposition c2)))
                                           (or (< (length s1) (length s2))
                                                 (and (= (length s1) (length s2))
                                                           (lessp s1 s2))))))))
               (dolist (c interests)
                   (princ "    #") (princ (interest-number c)) (princ "  ")
                   (princ "   sup = ") (set-prinp (interest-supposition c)) (princ "     ")
                   (when (reductio-interest c) (princ "reductio "))
                   (princ "for  ")
                   (print-list
                     (remove-duplicates=
                       (mapcar
                         #'(lambda (L) (interest-number (resultant-interest L)))
                         (right-links c))) 40)
                   (let ((derived-interests (derived-interests c)))
                      (when derived-interests
                           (princ "  generates ")
                           (print-list (mapcar #'interest-number derived-interests) 40)))
                   (terpri)))))
    (princ ")") (terpri))

; --------------------------------------  FORWARDS-REASONS --------------------------------------

#| This defines a generic structure whose slots are those used in common by both
backwards and forwards reasons.  If use-basis is nil, when a support-link is constructed,
the basis is nil.  This is used by def-prob-rule. |#

(defstruct (reason (:print-function print-reason) (:conc-name nil))
    (reason-name nil)
    (reason-function nil)
    (reason-conclusions nil)
    (conclusions-function nil)
    (forwards-premises nil)
    (backwards-premises nil)
    (reason-variables nil)
    (defeasible-rule nil)
    (reason-strength 1.0)
    (discount-factor 1.0)
    (reason-description nil)
    (reason-instantiated-premise nil)
    (backwards-premises-function nil)
    (temporal? nil)
    (undercutting-defeaters nil)
    (reason-defeatees)
    )

(defun print-reason (x stream depth)
    (declare (ignore depth)) (princ (reason-name x) stream))

;(defunction reason-strength+ (reason)
;    (if (stringp reason) 1.0 (reason-strength reason)))

(defunction reason (name)
    (let ((R (find-if #'(lambda (x) (equal (reason-name x) name)) *forwards-reasons*)))
       (when (null R)
            (setf R (find-if #'(lambda (x) (equal (reason-name x) name)) *backwards-reasons*)))
       R))

(defstruct (forwards-premise (:print-function print-f-premise) (:conc-name fp-))
    (formula nil)
    (kind :inference)
    (condition nil)
    (binding-function nil)
    (variables nil)
    (instantiator nil)
    (clue? nil)
    (node-specifier nil)  ;; bound to the node instantiating the premise in a link
    )

#| Condition1 is a predicate that an existing interest must satisfy to be used in
backwards reasoning as the left terminus of a link encoding this reason, and condition2
is a function which is applied to a new interest constructed for that purpose.
The application of this condition will normally be such as to set the values of slots
so that the resulting interest satisffies condition1. |#
(defstruct (backwards-premise (:print-function print-b-premise) (:conc-name bp-))
    (formula nil)
    (condition1 nil)
    (condition2 nil)
    (instantiator nil)
    (clue? nil)
    (text-condition nil)  ;; text specification of the discharge condition
    (node-specifier nil)  ;; bound to the node instantiating the premise in a link
    )

(defunction premise-node-specifier (premise)
    (cond ((backwards-premise-p premise) (bp-node-specifier premise))
              ((forwards-premise-p premise) (fp-node-specifier premise))))

(defunction print-f-premise (premise stream depth)
    (declare (ignore depth))
    (princ "#<premise: " stream)
    (prinp (fp-formula premise) stream)
    (princ ">" stream))

(defunction print-b-premise (premise stream depth)
    (declare (ignore depth))
    (princ "#<premise: " stream)
    (prinp (bp-formula premise) stream)
    (princ ">" stream))

(defunction clue? (premise)
    (cond ((forwards-premise-p premise) (fp-clue? premise))
              ((backwards-premise-p premise) (bp-clue? premise))))

(defunction construct-forwards-premise (P C V &optional B)
    (make-forwards-premise
      :formula P
      :condition C
      :binding-function B
      :variables V
      :instantiator (reason-instantiator P V)))

(defmacro cfp (P V &optional B) `(construct-forwards-premise ,P nil ,V ,B))

(defunction construct-backwards-premise (P C1 C2 V)
    (let ((V* (subset #'(lambda (x) (occur* x P)) V)))
      (make-backwards-premise
        :formula P
        :condition1 C1
        :condition2 C2
        :instantiator (reason-instantiator P V*))))

(defmacro cbp (P C1 C2 V) `(construct-backwards-premise ,P ,C1 ,C2 ,V))

(defstruct (forwards-reason (:include reason) (:print-function print-reason)
                                                       (:conc-name nil)))

(defun is-inference (c &rest r) (declare (ignore r)) (eq (node-kind c) :inference))

(defun is-desire (c &rest r) (declare (ignore r)) (eq (node-kind c) :desire))

(defun is-percept (c &rest r) (declare (ignore r)) (eq (node-kind c) :percept))

(setf is-inference #'is-inference)

(setf is-desire #'is-desire)

(setf is-percept #'is-percept)

#| This produces a match equivalent to applying m1 first and then m2. |#
(defunction merge-matches* (m1 m2)
    (cond ((null m1) m2)
                ((null m2) m1)
                ((eq m1 t) m2)
                ((eq m2 t) m1)
                (t
                  (let* ((m1* (mapcar #'(lambda (x) (cons (car x) (match-sublis m2 (cdr x)))) m1))
                            (domain (domain m1*))
                            (m2* (subset #'(lambda (x) (not (member (car x) domain))) m2)))
                     (append m1* m2*)))))

; --------------------------------------  BACKWARDS-REASONS --------------------------------------

(defstruct (backwards-reason (:include reason) (:print-function print-reason)
                                                           (:conc-name nil))
   (reason-condition nil)  ;; this is a predicate applied to the binding
   (reason-discharge nil)
   (reason-length 1)  ;; this is the number of backwards-premises
   (conclusions-binding-function nil)
   (conclusion-variables nil)
   (immediate-reason nil))

#| This can be blocked by a prior reductio-supposition, but this then converts it so that it is
no longer deductive-only.  Any node-descendants not inferred from other deductive-only
nodes are made not deductive-only, and all defeasible forwards-rules are applied to them. |#
(defunction queue-supposition (supposition instance-supposition e-vars discount-factor interest)
    ; (when (eq interest (interest 36)) (setf s supposition i instance-supposition e e-vars d discount-factor in interest) (break))
    ;; (step (queue-supposition s i e d in))
    (let ((sup (find-if #'(lambda (N) (equal (node-formula N) supposition))
                        *non-reductio-supposition-nodes*)))
     (cond (sup
              (incf (readopted-supposition sup))
              (push interest (generating-interests sup))
              (push sup (generated-suppositions interest))
              (when (and (deductive-only sup) (not (deductive-interest interest)))
                  (let ((nodes (convert-from-deductive-only sup)))
                    (dolist (C nodes)
                       (apply-forwards-defeasible-reasons C))))
              (values sup nil))
             (t
              (setf sup (subsuming-supposition supposition))  ;; an inference-node
              (cond ((null sup)
                       (queue-non-reductio-supposition
                        supposition instance-supposition e-vars discount-factor interest))
                      ((reductio-supposition sup)
                       (incf (readopted-supposition sup))
                       (push interest (generating-interests sup))
                       (convert-reductio-supposition sup discount-factor)
                       (values sup t)))))))

(defunction queue-non-reductio-supposition
    (supposition instance-supposition e-vars discount-factor interest)
    (let* ((sequent (list instance-supposition supposition))
              (deductive-only (deductive-interest interest)))
       (when (skolem-free supposition) (push supposition *skolem-free-suppositions*))
       (let* ((complexity
                   (max 1 (* 2 (formula-complexity supposition))))
                 (priority (* discount-factor (interest-priority interest)))
                 (node
                   (make-inference-node
                     :inference-number (incf *inference-number*)
                     :node-sequent sequent
                     :node-formula supposition
                     :node-supposition instance-supposition
                     :node-kind :inference
                     :nearest-defeasible-ancestors (list nil)
                     :node-justification :supposition
                     :maximal-degree-of-support 1.0
                     :undefeated-degree-of-support 1.0
                     :discounted-node-strength priority
                     :deductive-only deductive-only
                     :node-variables e-vars
                     :node-supposition-variables e-vars
                     :node-discount-factor discount-factor
                     :generating-interests (list interest)
                     :non-reductio-supposition? t))
                 (queue-node
                   (make-inference-queue-node
                     :queue-number (incf *queue-number*)
                     :enqued-item node
                     :item-kind :conclusion
                     :discounted-strength priority
                     :item-complexity complexity
                     :degree-of-preference (/ discount-factor complexity))))
          (setf (non-reductio-supposition node) (list (cons (mem1 instance-supposition) node)))
          (setf (node-queue-node node) queue-node)
          (store-inference-node node (sequent-formula sequent))
          (push node (generated-suppositions interest))
          (push node *inference-graph*)
          (push node *non-reductio-supposition-nodes*)
          (if *log-on* (push node *reasoning-log*))
          (when (not *deductive-only*)
               (setf (node-UDs *assignment-tree*) (cons (cons node 1.0) (node-UDs *assignment-tree*)))
               (setf (node-MPUDs *assignment-tree*) (cons (cons node 1.0) (node-MPUDs *assignment-tree*))))
          (when *display?* (display-unsupported-node node))
          (discharge-interest-in node (corresponding-i-lists (node-c-list node)) nil t 1 nil)
          (setf *inference-queue* (ordered-insert queue-node *inference-queue* #'i-preferred))
          (when (and *display?* *graphics-on*)
               (when *graphics-pause* (pause-graphics))
               (draw-n node *og* *nodes-displayed*) (push node *nodes-displayed*))
          (values node t))))

#| This converts the supporting-nodes of node and its descendants to non-deductive-only
provided they are not inferred from other deductive-only conclusions.  It returns the list of
converted nodes. |#
(defunction convert-from-deductive-only (node)
    (setf (deductive-only node) nil)
    (let ((nodes (list node)))
       (dolist (L (consequent-links node))
           (let ((N (support-link-target L)))
              (when
                   (and (deductive-only N)
                             (not (some
                                       #'(lambda (L)
                                             (some
                                               #'(lambda (b) (deductive-only b))
                                               (support-link-basis L)))
                                       (support-links N))))
                   (setf nodes
                            (union nodes (convert-from-deductive-only N))))))
       nodes))

(defunction subsuming-supposition (supposition)
    (let* ((sup
              (find-if
                #'(lambda (N)
                      (let* ((P (node-formula N))
                                (f-vars (node-variables N))
                                (m (match P supposition f-vars)))
                         (and m (equal supposition (match-sublis m P)))))
                *non-reductio-supposition-nodes*)))
       (when (null sup)
            (setf sup
                     (find-if
                       #'(lambda (N)
                             (let* ((P (node-formula N))
                                       (f-vars (node-variables N))
                                       (m (match P supposition f-vars)))
                                (and m (equal supposition (match-sublis m P)))))
                       *reductio-supposition-nodes*)))
       sup))

; --------------------------------------  THE INFERENCE-QUEUE --------------------------------------

(defstruct (inference-queue-node (:print-function print-inference-queue-node)
                                                                (:conc-name nil))
   (queue-number 0)
   (enqued-item nil)  ;; either an interest or a conclusion or a query
   (item-kind nil)   ;; this will be :conclusion, :interest, or :query
   (item-complexity 0)
   (discounted-strength 0)
   (degree-of-preference 0))

(defun print-inference-queue-node (x stream depth)
    (declare (ignore depth))
    (princ "#<" stream) (princ "Item " stream)
    (princ (queue-number x) stream) (princ ">" stream))

#| *inference-queue* is ordered by i-preference: |#
(defunction i-preferred (node1 node2)
    (> (degree-of-preference node1) (degree-of-preference node2)))

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
                          ;; the following handles functions that occur within their own scopes
                          ((and (not (null (cdr x)))
                                    (symbolp (car x))
                                    (not (member (mem1 x) *logical-constants*))
                                    (occur (car x) (cdr x)))
                            (* *skolem-multiplier* (1+ (complexity (cdr x)))))
                          ((or (u-genp x) (e-genp x)) (* *quantifier-discount* (complexity (q-matrix x))))
                          ((consp (cdr x)) (apply #'+ (mapcar #'complexity x)))
                          (t (+ (complexity (car x)) (complexity (cdr x))))))))

(defunction formula-complexity (formula)
    (cond ((mem formula *skolem-free-suppositions*) 0)
                (t (complexity formula))))

(defunction sequent-complexity (sequent)
    (let* ((sup (sequent-supposition sequent))
            (formula (sequent-formula sequent))
            (complexity
              (cond (sup
                          (+ (max 1 (formula-complexity formula))
                               (apply
                                 '+ (mapcar
                                      #'(lambda (P)
                                            (cond ((mem P *skolem-free-suppositions*) 0)
                                                      (t (complexity P))))
                                      sup))))
                        (t (max 1 (formula-complexity formula))))))
      ;  (when *display?*
      ;       (princ "The complexity of ") (print-sequent sequent) (princ " is ") (princ complexity) (terpri))
      complexity))

#|
(defunction sequent-complexity (sequent)
    (let ((sup (sequent-supposition sequent))
            (formula (sequent-formula sequent))
            (length 0))
       (let ((complexity
                 (cond (sup
                              (+ (max 1 (formula-complexity formula))
                                   (apply
                                     '+ (mapcar
                                           #'(lambda (P)
                                                 (cond ((mem P *skolem-free-suppositions*) 0)
                                                             (t (incf length) (complexity P))))
                                           sup))))
                             (t (max 1 (formula-complexity formula))))))
          ;  (when *display?*
          ;       (princ "The complexity of ") (print-sequent sequent) (princ " is ") (princ complexity) (terpri))
          (if (> length 2) (* complexity (expt 10 (* length length))) complexity))))
|#

#| This is the default computation of degree-of-preference for premises.  Premises
are triples consisting of a formula, a supposition, and a degree-of-support.
Premises are queued for immediate retrieval. |#
(defunction premise-preference (premise)
    (/ (mem2 premise) (complexity (mem1 premise))))

(defstruct (goal (:print-function print-goal) (:conc-name nil))
    (goal-number 0)
    (goal-formula nil)
    (goal-strength 1)
    (supporting-goal-node nil)  ;; the node supporting this as a suitable goal
    (goal-generating-desire nil)  ;; the desire, if there is on, that generates the goal
    (plans-for nil)  ;; the list of candidate plans that aim at the satisfaction of this goal
    (user-question-asked? nil))

(defunction print-goal (goal stream depth)
    (declare (ignore depth))
    (princ "#<goal: " stream)
    (princ (pretty (goal-formula goal)) stream)
    (princ ">" stream))

(defstruct (desire (:print-function print-desire) (:conc-name nil))
    (desire-number 0)
    (desire-content nil)
    (desire-object nil)  ;; the object of a desire will be a goal
    (desire-strength 0)
    (generated-plans nil)
    (desire-generating-interest nil)  ;; for epistemic-desires
    (desire-inference-node nil))  ;; the inference-node recording the desire

(defunction print-desire (desire stream depth)
    (declare (ignore depth))
    (princ "#<desire: " stream)
    (princ (pretty (desire-content desire)) stream)
    (princ ">" stream))

(defunction goal-generating-interest (goal)
    (let ((desire (goal-generating-desire goal)))
       (when desire (desire-generating-interest desire))))

(defstruct (percept (:print-function print-percept) (:conc-name nil))
    (percept-number 0)
    (percept-content nil)
    (percept-clarity 0)
    (percept-date 0))

(defunction print-percept (percept stream depth)
    (declare (ignore depth))
    (princ "#<percept: " stream)
    (princ (pretty (percept-content percept)) stream)
    (princ ">" stream))

#| This is the default computation of degree-of-preference for desires. |#
(defunction desire-preference (desire)
    (/ (desire-strength desire) (complexity (desire-content desire))))

#| This is the default computation of degree-of-preference for percepts. |#
(defunction percept-preference (percept)
    (/ (percept-clarity percept) (complexity (percept-content percept))))

(defunction discharged? (interest degree)
    (let ((discharged-degree (discharged-degree interest)))
       (and discharged-degree
                 (>= discharged-degree degree))))

#| The following is the default computation of interest-priority for defeaters. |#
(defunction defeater-priority (interest)
    (declare (ignore interest))
    *base-priority*)

#| The following is the default computation of the degree-of-preference for queries. |#
(defunction query-preference (query)
    (let ((complexity (complexity (query-formula query)))
            (strength
              (cond ((member query *permanent-ultimate-epistemic-interests*)
                           (query-strength query))
                          ((answered? query)
                            (* (query-strength query) *answered-discount*))
                          (t (query-strength query)))))
       (/ strength complexity)))

#| This is the default computation of degree-of-preference for an interest, where
priority is the interest-priority and complexity is the complexity of the interest-sequent. |#
(defunction interest-preference (priority complexity)
    (if (zerop complexity) priority (/ priority complexity)))

#| This reverses the default computation of degree-of-preference to compute priority
from preference. |#
(defunction retrieved-interest-priority (preference complexity)
    (* complexity preference))

(defunction interest-link-priority (link interest-priority interest)
    (if (or (link-defeat-status link)
               (let ((rn (resultant-interest link)))
                  (discharged? rn (maximum-degree-of-interest rn)))
               (and interest (discharged? interest (maximum-degree-of-interest interest))))
       *base-priority*
       interest-priority))

#| The following is the default computation of interest-priority for an interest on
the inference-queue that is concluded. |#
(defunction concluded-interest-priority (Q)
    (declare (ignore Q))
    *concluded-interest-priority*)

#| This must recompute reductio-ancestors, non-reductio-suppositions, deductive-only-status,
and apply forwards defeasible reasons. |#
(defunction convert-reductio-supposition (sup discount-factor)
    (setf (reductio-ancestors sup) (list (cons (node-formula sup) sup)))
   ; (setf (non-reductio-supposition sup) nil)
    (setf (non-reductio-supposition? sup) t)
    (let ((Q (node-queue-node sup)))
       (when Q
            (setf (degree-of-preference Q) (* discount-factor (/ 1 (item-complexity Q))))
            (setf *inference-queue*
                     (ordered-insert Q (remove Q *inference-queue*) #'i-preferred))))
    (let ((nodes
              (convert-from-deductive-only sup)))
       (dolist (C nodes)
           (when (deductive-in C sup)
                (let ((nr (find-if #'(lambda (x) (equal (cdr x) sup)) (non-reductio-supposition C))))
                   (when nr
                        (pull nr (non-reductio-supposition C))
                        (push nr (reductio-ancestors C))))))
       (dolist (C nodes)
           (apply-forwards-defeasible-reasons C))))

;======================================================
;------------------------------------------- REASONING ---------------------------------------

#| The following turn various displays on and off. |#
(defunction trace-on () (setf *display?* t) (setf *trace* t))
(defunction trace-off () (setf *trace* nil *start-trace* nil))
(defunction trace-from (n) (setf *start-trace* n *display?* nil *trace* nil))
(defun display-on () (setf *display?* t))
(defun display-off () (setf *display?* nil *trace* nil *start-trace* nil *start-display* nil))
(defun display-from (n) (setf *display?* nil *trace* nil *start-trace* nil *start-display* n))
(defun proof-on () (setf *proofs?* t))
(defun proof-off () (setf *proofs?* nil))
(defun logic-on () (setf *use-logic* t) (setf *use-reductio* t))
(defun logic-off () (setf *use-logic* nil) (setf *use-reductio* nil))
(defun reductio-on () (setf *use-reductio* t) (setf *use-logic* t))
(defun reductio-off () (setf *use-reductio* nil))
(defun log-on () (setf *log-on* t))
(defun log-off () (setf *log-on* nil))
(defun IQ-on () (setf *display-inference-queue* t))
(defun IQ-off () (setf *display-inference-queue* nil))
(defunction graph-log-on ()
    (setf *graph-log* t))
(defunction graph-log-off ()
    (setf *graph-log* nil))

#| When graphics-pause is on, the reasoning-display pauses after printing the node display
and before graphing the node, and waits for a character (preferably a space) to be typed
in the Listener. |#
(defunction graphics-pause-on ()
    (setf *graphics-pause* t))
(defunction graphics-pause-off ()
    (setf *graphics-pause* nil))

#| The following does not perform the operations in parallel as it should, because
this program is designed to run in serial LISP.  The functions update-environmental-
input and update-percepts are extrinsic to the reasoner,
and are supplied by the operating environment of the reasoner.
Optative dispositions are functions from inputs to desires.  This code allows
us to have premises supplied artificially rather than by perception.
Premises are triples (formula, supposition, degree-of-justification).
Premises can be defeated by rebutting defeaters, but there is no way
to have an undercutting defeater.  |#
(defunction OSCAR ()
    (initialize-reasoner)
   (dolist (query *ultimate-epistemic-interests*)
      (reason-backwards-from-query query (query-strength query) 0))
    (setf *cycle* 0)
    (loop
      (update-environmental-input)
      (update-percepts)
      (dolist (input *environmental-input*)
          (dolist (disposition *optative-dispositions*)
              (pull input *environmental-input*)
              (queue-desire (funcall disposition input))))
      (dolist (percept *percepts*)
          (pull percept *percepts*)
          (queue-percept percept))
     (dolist (premise *premises*)
        (when (eql (mem3 premise) *cycle*)
            (pull premise *premises*)
            (queue-premise (list (mem1 premise) nil (mem2 premise)))))
       (think)
       (initiate-actions)
       (incf *cycle*)))

(defun initialize-reasoner ()
    (setf *new-links* nil)
    (setf *inference-graph* nil)
    (setf *processed-desires* nil)
    (setf *desires* nil)
    (setf *percepts* nil)
    (setf *interest-links* nil)
    (setf *inference-queue* nil)
    (setf *support-links* nil)
    (setf *interests* nil)
    (setf *interest-schemes* nil)
    (setf *reductio-supposition-nodes* nil)
    (setf *non-reductio-supposition-nodes* nil)
    (setf *altered-nodes* nil)
    (setf *reasoning-log* nil)
    (setf *direct-reductio-interests* nil)
    (setf *assignment-tree* (make-assignment-tree))
    (setf *Q&I-modules* nil)
    (setf *inherited-non-reductio-suppositions* nil)
    (setf *skolem-free-suppositions* nil)
    (setf *constructed-plans* nil)
    (setf *constructed-goals* nil)
    (setf *constructed-desires* nil)
    (setf pause-flag nil)
    (setf *cycle* 0)
    (setf *inference-number* 0)
    (setf *support-link-number* 0)
    (setf *interest-number* 0)
    (setf *interest-scheme-number* 0)
    (setf *queue-number* 0)
    (setf *link-number* 0)
    (setf *tree-number* 1)
    (setf *triangle-number* 0)
    (setf *unused-suppositions* 0)
    (setf *gensym-counter* 0)
    (setf *ip-number* 0)
    (setf *is-number* 0)
    (setf *plan-number* 0)
    (setf *goal-number* 0)
    (setf *executable-operations* nil)
    (setf *deleted-arguments* nil)
    (setf *forwards-reasons*
             (if *use-logic*
               (append *forwards-logical-reasons* *forwards-substantive-reasons*)
               *forwards-substantive-reasons*))
    (setf *backwards-reasons*
             (if *use-logic*
               (append *backwards-logical-reasons* *backwards-substantive-reasons*)
               *backwards-substantive-reasons*))
    (initialize-discrimination-net)
    (when (and *display?* *graphics-on*) (make-oscar-window))
    (setf *query-number* (length *fixed-ultimate-epistemic-interests*))
    (dolist (query *fixed-ultimate-epistemic-interests*)
        (setf (answered? query) nil)
        (setf (query-answers query) nil)
        (setf (query-interest query) nil)
        (setf (negative-query-interest query) nil)
        (setf (query-queue-node query) nil))
    (dolist (premise *premises*)
        (when (null (mem3 premise)) (pull premise *premises*) (queue-premise premise)))
    (setf *ultimate-epistemic-interests* *fixed-ultimate-epistemic-interests*)
    (when (and *display?* *graphics-on*)
         (dolist (node (reverse *inference-graph*))
             (draw-n node *og* *nodes-displayed*) (push node *nodes-displayed*)))
   ; (dolist (query *ultimate-epistemic-interests*)
   ;     (reason-backwards-from-query query (query-strength query) 0))
    (if (not (boundp '*display?*)) (setf *display?* nil)))

(defunction initialize-discrimination-net ()
    (setf *top-d-node* (make-d-node :d-node-number (setf *d-node-number* 1)))
    (setf *conditional-node*
             (make-d-node :d-node-number (incf *d-node-number*) :parent-d-node *top-d-node*))
    (setf *undercutter-node*
             (make-d-node :d-node-number (incf *d-node-number*) :parent-d-node *top-d-node*))
    (setf *conjunctive-undercutter-node*
             (make-d-node :d-node-number (incf *d-node-number*) :parent-d-node *undercutter-node*))
    (setf (discrimination-tests *top-d-node*)
             (list (cons '((1) . ->) *conditional-node*)
                     (cons '((1) . @) *undercutter-node*)))
    (setf *discrimination-net*
             (list *top-d-node* *conditional-node* *undercutter-node* *conjunctive-undercutter-node*))
    (setf (discrimination-tests *undercutter-node*)
             (list (cons '((2 1) . &) *conjunctive-undercutter-node*)))
    (compute-forwards-reason-d-nodes)
    (compute-backwards-reason-d-nodes))

(defunction premise-code (P variables)
    (when P
         (setf *quantifier-number* 0)
         (multiple-value-bind (code term-list) (premise-code* P variables nil)
              (values (reverse code) term-list))))

(defunction premise-code* (P variables descriptor)
    (cond ((listp P)
                 (let ((description nil) (elt-num 1) (term-list nil))
                    (cond
                      ;; This handles notational variants.
                      ((or (eq (car p) 'all) (eq (car P) 'some))
                        (setf P
                                 (cons (car P) (subst (list 'q-var (incf *quantifier-number*)) (mem2 P) (cddr P)))))
                      ((and (symbolp (car P))
                                 (not (member (car P) *operators*))
                                 (not (member (car P) '(~ & v -> <-> all some ? @))))
                        (setf term-list (cdr P))
                        (setf P (list (car P)))))
                    (dolist (Q P)
                        (when (not (member Q variables))
                             (let ((Q-descriptor (cons elt-num descriptor)))
                                (cond ((not (listp Q))
                                             (when (not (member Q variables))
                                                  (push (cons (reverse Q-descriptor) Q) description)))
                                            (t
                                              (multiple-value-bind (d tl) (premise-code* Q variables Q-descriptor)
                                                   (setf term-list (append tl term-list))
                                                   (setf description (append d description))
                                                   )))))
                        (incf elt-num))
                    (values description term-list)))
                ((not (member P variables)) (values (list (cons descriptor P)) nil))))

#| This is like premise-code, but it stops producing code when it comes to the first variable. |#
(defunction reason-code (P variables)
    (when P
         (setf *quantifier-number* 0)
         (reverse (reason-code* P variables nil))))

(defunction reason-code* (P variables descriptor)
    (cond ((listp P)
                 (let ((description nil) (elt-num 1) (stop nil))
                    (cond
                      ;; This handles notational variants.
                      ((or (eq (car p) 'all) (eq (car P) 'some))
                        (setf P
                                 (cons (car P) (subst (list 'q-var (incf *quantifier-number*)) (mem2 P) (cddr P)))))
                      ((and (symbolp (car P))
                                 (not (member (car P) *operators*))
                                 (not (member (car P) '(~ & v -> <-> all some ? @ at throughout))))
                        (setf P (list (car P)))))
                    (block stop-here
                        (dolist (Q P)
                            (cond
                              ((member Q variables)
                                (setf stop t)
                                (return-from stop-here))
                              (t
                                (let ((Q-descriptor (cons elt-num descriptor)))
                                   (cond ((not (listp Q))
                                                (push (cons (reverse Q-descriptor) Q) description))
                                               (t
                                                 (multiple-value-bind (d st) (reason-code* Q variables Q-descriptor)
                                                      (setf description (append d description))
                                                      (when st (setf stop t) (return-from stop-here))))))))
                            (incf elt-num)))
                    (values description stop)))
                ((not (member P variables)) (values (list (cons descriptor P)) nil))))

(defunction compute-forwards-reason-d-nodes ()
    (dolist (reason *forwards-reasons*)
        (let* ((premise (mem1 (forwards-premises reason)))
                  (profile (reason-code (fp-formula premise) (fp-variables premise)))
                  (ip (store-forwards-reason reason premise profile)))
           (setf (reason-instantiated-premise reason) ip))))

#| This returns the ip at which the premise is stored. |#
(defunction store-forwards-reason (reason premise profile)
    (cond
      (profile (index-forwards-reason reason premise profile *top-d-node*))
      (t (store-forwards-reason-at-d-node reason premise *top-d-node*))))

(defunction store-forwards-reason-at-d-node (reason premise d-node)
    (let ((ip
              (make-instantiated-premise
                :reason reason
                :premise premise
                :remaining-premises (cdr (forwards-premises reason))
                :used-premise-variables (fp-variables premise)
                :d-node d-node
                :number (incf *ip-number*)
                :initial? t)))
       (push ip (d-node-forwards-reasons d-node))
       ip))

(defunction index-forwards-reason (reason premise profile d-node)
    (let ((dn (e-assoc (car profile) (discrimination-tests d-node)))
            (new-profile (cdr profile)))
       (cond (dn
                    (cond
                      (new-profile (index-forwards-reason reason premise new-profile dn))
                      (t (store-forwards-reason-at-d-node reason premise dn))))
                   (new-profile
                     (index-forwards-reason-at-new-nodes
                       reason premise d-node new-profile (car profile)))
                   (t
                     (store-forwards-reason-at-new-d-node reason premise d-node (car profile))))))

#| Test is the final member of the formula-profile for the node-formula. |#
(defunction store-forwards-reason-at-new-d-node (reason premise d-node test)
    (let ((dn (make-d-node
                     :d-node-number (incf *d-node-number*)
                     :d-node-description (cons test (d-node-description d-node))
                     :parent-d-node d-node)))
       (push dn *discrimination-net*)
       (push (cons test dn) (discrimination-tests d-node))
       (store-forwards-reason-at-d-node reason premise dn)))

(defunction index-forwards-reason-at-new-nodes
    (reason premise d-node profile test)
    (let ((dn (make-d-node
                     :d-node-number (incf *d-node-number*)
                     :d-node-description (cons test (d-node-description d-node))
                     :parent-d-node d-node)))
       (push (cons test dn) (discrimination-tests d-node))
       (push dn *discrimination-net*)
       (let ((desc (cdr profile)))
          (cond (desc (index-forwards-reason-at-new-nodes reason premise dn desc (car profile)))
                      (t (store-forwards-reason-at-new-d-node reason premise dn (car profile)))))))

(defunction def-instantiator (def vars)
    (eval
      `#'(lambda (binding)
             (let* ((new-binding binding)
                       (new-vars nil)
                       ,@
                       (mapcar
                         #'(lambda (v)
                               `(,v
                                  (let ((v* (assoc ',v binding)))
                                    (cond
                                      (v* (cdr v*))
                                      (t
                                        (setf v* (make-interest-variable))
                                        (push v* new-vars)
                                        (push (cons ',v v*) new-binding)
                                        v*)))))
                         vars))
               (values ,def new-binding new-vars)))))

(defunction set-def-binding (def-instantiator var binding)
    (multiple-value-bind
         (val binding new-vars)
         (funcall def-instantiator binding)
         (values
           (cons (cons var val) (remove (assoc var binding) binding :test 'equal))
           new-vars (cons (e-assoc var binding) val))))

#| This returns the instantiated-premise. |#
(defunction store-instantiated-premise
    (reason node c-list binding instantiations ip remaining-premises &optional profile)
    ; (setf r reason rp remaining-premises pr profile n node cl c-list b binding in instantiations i ip) ;(break)
    ;; (step (store-instantiated-premise r n cl b in i rp pr))
    (cond
      ((and (forwards-premise-p (car remaining-premises))
                (listp (fp-formula (car remaining-premises)))
                (equal (car (fp-formula (car remaining-premises))) 'define))
        (let* ((var (mem2 (fp-formula (car remaining-premises))))
                  (def-instantiator (fp-instantiator (car remaining-premises)))
                  (new-binding (set-def-binding def-instantiator var binding)))
          (cond ((cdr remaining-premises)
                      (when (funcall** (fp-condition (car remaining-premises)) nil new-binding)
                           (store-instantiated-premise
                             reason node c-list new-binding instantiations ip (cdr remaining-premises))))
                    ((funcall** (fp-condition (car remaining-premises)) nil new-binding)
                      (make-forwards-inference
                          new-binding instantiations
                          (if (clue? (ip-premise ip)) (ip-basis ip) (cons node (ip-basis ip)))
                          (if (clue? (ip-premise ip)) (cons node (ip-clues ip)) (ip-clues ip))
                          0 ip)))))
      (t
        (let ((premise (mem1 remaining-premises)))
          (when (null profile)
               (setf profile (reason-code (funcall (fp-instantiator premise) binding) (fp-variables premise))))
          (cond (profile
                      (index-instantiated-premise
                        reason premise profile node c-list binding instantiations
                        ip *top-d-node* (cdr remaining-premises)))
                    (t (store-instantiated-premise-at-d-node
                          reason premise node c-list binding instantiations
                          ip *top-d-node* (cdr remaining-premises))))))))

#| (mem3 premise) will be a function which, when applied to a formua, returns a binding.
(mem4 premise) will be the list of premise-variables occurring therein. |#
(defunction store-instantiated-premise-at-d-node
    (reason premise node c-list binding instantiations ip0 d-node remaining-premises)
    (when node (setf c-list (node-c-list node)))
    (let* ((ip
                (make-instantiated-premise
                  :reason reason
                  :number (incf *ip-number*)
                  :premise premise
                  :binding binding
                  :basis (if (and ip0 (not (fp-clue? (ip-premise ip0))))
                       (cons node (ip-basis ip0)))
                  :remaining-premises remaining-premises
                  :clues (when ip0
                                 (if (fp-clue? (ip-premise ip0)) (cons node (ip-clues ip0)) (ip-clues ip0)))
                  :d-node d-node
                  :instantiations (if ip0 instantiations)
                  :used-premise-variables
                  (if ip0 (union (fp-variables premise) (ip-used-premise-variables ip0))
                       (fp-variables premise))
                  :used-variables (if ip0 (union (c-list-variables c-list) (ip-used-variables ip0)))
                  )))
       (push ip (d-node-forwards-reasons d-node))
       (setf (ip-d-node ip) d-node)
       (push ip (generated-instantiated-premises c-list))
       (if ip0 (push ip (ip-derived-premises ip0)))
       (when *display?* (display-instantiated-premise ip))
       ip))

(defunction index-instantiated-premise
    (reason premise profile node c-list binding instantiations ip d-node remaining-premises)
    (let ((dn (e-assoc (car profile) (discrimination-tests d-node)))
            (new-profile (cdr profile)))
       (cond (dn
                    (cond
                      (new-profile
                        (index-instantiated-premise
                          reason premise new-profile node c-list binding instantiations ip dn remaining-premises))
                      (t (store-instantiated-premise-at-d-node
                           reason premise node c-list binding instantiations ip dn remaining-premises))))
                   (new-profile
                     (index-instantiated-premise-at-new-nodes
                       reason premise new-profile node c-list binding instantiations ip d-node (car profile) remaining-premises))
                   (t
                     (store-instantiated-premise-at-new-d-node
                       reason premise node c-list binding instantiations ip d-node (car profile) remaining-premises)))))

#| Test is the final member of the formula-profile for the node-formula. |#
(defunction store-instantiated-premise-at-new-d-node
    (reason premise node c-list binding instantiations ip d-node test remaining-premises)
    (let ((dn (make-d-node
                     :d-node-number (incf *d-node-number*)
                     :d-node-description (cons test (d-node-description d-node))
                     :parent-d-node d-node)))
       (push dn *discrimination-net*)
       (push (cons test dn) (discrimination-tests d-node))
       (store-instantiated-premise-at-d-node
         reason premise node c-list binding instantiations ip dn remaining-premises)))

(defunction index-instantiated-premise-at-new-nodes
    (reason premise profile node c-list binding instantiations ip d-node test remaining-premises)
    (let ((dn (make-d-node
                     :d-node-number (incf *d-node-number*)
                     :d-node-description (cons test (d-node-description d-node))
                     :parent-d-node d-node)))
       (push (cons test dn) (discrimination-tests d-node))
       (push dn *discrimination-net*)
       (let ((desc (cdr profile)))
          (cond (desc (index-instantiated-premise-at-new-nodes
                                  reason premise desc node c-list binding instantiations ip dn (car profile) remaining-premises))
                      (t (store-instantiated-premise-at-new-d-node
                           reason premise node c-list binding instantiations ip dn (car profile) remaining-premises))))))

(defunction compute-backwards-reason-d-nodes ()
    (dolist (reason *backwards-reasons*)
        (when (reason-conclusions reason)
             (let ((profile (reason-code (mem1 (reason-conclusions reason)) (reason-variables reason))))
               (store-backwards-reason reason profile)))))

(defunction store-backwards-reason-at-d-node (reason d-node)
   ; (when (eq reason null-plan) (setf r reason d d-node) (break))
    (cond ((immediate-reason reason)
                (push reason (d-node-degenerate-backwards-reasons d-node)))
              ((backwards-premises reason)
                (push reason (d-node-backwards-reasons d-node)))
              (t (push reason (d-node-degenerate-backwards-reasons d-node))))
    d-node)

#| This returns the d-node at which the premise is stored. |#
(defunction store-backwards-reason (reason profile)
    (cond
      (profile (index-backwards-reason reason profile *top-d-node*))
      (t (store-backwards-reason-at-d-node reason *top-d-node*))))

(defunction index-backwards-reason (reason profile d-node)
    (let ((dn (e-assoc (car profile) (discrimination-tests d-node)))
            (new-profile (cdr profile)))
       (cond (dn
                    (cond
                      (new-profile (index-backwards-reason reason new-profile dn))
                      (t (store-backwards-reason-at-d-node reason dn))))
                   (new-profile
                     (index-backwards-reason-at-new-nodes
                       reason d-node new-profile (car profile)))
                   (t
                     (store-backwards-reason-at-new-d-node reason d-node (car profile))))))

#| Test is the final member of the formula-profile for the node-formula. |#
(defunction store-backwards-reason-at-new-d-node (reason d-node test)
    (let ((dn (make-d-node
                     :d-node-number (incf *d-node-number*)
                     :d-node-description (cons test (d-node-description d-node))
                     :parent-d-node d-node)))
       (push dn *discrimination-net*)
       (push (cons test dn) (discrimination-tests d-node))
       (store-backwards-reason-at-d-node reason dn)))

(defunction index-backwards-reason-at-new-nodes (reason d-node profile test)
    (let ((dn (make-d-node
                     :d-node-number (incf *d-node-number*)
                     :d-node-description (cons test (d-node-description d-node))
                     :parent-d-node d-node)))
       (push (cons test dn) (discrimination-tests d-node))
       (push dn *discrimination-net*)
       (let ((desc (cdr profile)))
          (cond (desc (index-backwards-reason-at-new-nodes reason dn desc (car profile)))
                      (t (store-backwards-reason-at-new-d-node reason dn (car profile)))))))

(defunction construct-interest-scheme
    (reason node interest binding instantiations remaining-premises is0
                  depth priority supposition)
     ;(when (and (eq reason repair-conjunct-2) (eq interest (interest 8))) (setf r reason n node i interest b binding in instantiations rp remaining-premises i* is0 d depth p priority s supposition) (break))
    ;; (step (construct-interest-scheme r n i b in rp i* d p s))
    (cond
      ((and (forwards-premise-p (car remaining-premises))
                (listp (fp-formula (car remaining-premises)))
                (equal (car (fp-formula (car remaining-premises))) 'define))
        (let* ((var (mem2 (fp-formula (car remaining-premises))))
                  (def-instantiator (fp-instantiator (car remaining-premises)))
                  (new-binding (set-def-binding def-instantiator var binding)))
          (when (funcall** (fp-condition (car remaining-premises)) nil new-binding)
               (cond ((cdr remaining-premises)
                           (construct-interest-scheme
                             reason node interest new-binding instantiations (cdr remaining-premises)
                             is0 depth priority supposition))
                         (is0
                           (make-backwards-inference
                             (is-reason is0) new-binding (is-target-interest is0) (1+ depth) priority
                             (if (fp-clue? (is-premise is0)) (is-basis is0) (cons node (is-basis is0)))
                             (if (fp-clue? (is-premise is0)) (cons node (is-clues is0)) (is-clues is0))
                             instantiations supposition (is-generating-node is0)))
                         (t
                           (make-backwards-inference
                             reason new-binding interest (1+ depth) priority nil nil instantiations supposition nil))))))
      (t
        (let* ((basis
                    (when is0
                         (cond ((fp-clue? (is-premise is0)) (is-basis is0))
                                   (t (if node (cons node (is-basis is0)) (is-basis is0))))))
                  (clues
                    (when is0
                         (cond ((fp-clue? (is-premise is0)) (if node (cons node (is-clues is0)) (is-clues is0)))
                                   (t (is-clues is0)))))
                  (discharge (if (and (null basis)
                                                 (null (if is0 (is-generating-node is0)))
                                                 (reason-discharge reason))
                                      (remove-double-negation
                                        (match-sublis binding (reason-discharge reason))))))
            (multiple-value-bind
                 (generating-node new-sup?)
                 (if discharge
                   (queue-supposition
                     discharge (list discharge)
                     (subset #'(lambda (v) (occur v discharge)) (interest-variables interest))
                     (discount-factor reason) interest))
                 (when (or new-sup? (null discharge))
                      (let* ((premise (mem1 remaining-premises))
                                (profile (reason-code (fp-formula premise) (reason-variables reason)))
                                (d-node (pursue-d-node-for profile *top-d-node*))
                                (generating-node
                                  (cond (new-sup? generating-node) (is0 (is-generating-node is0))))
                                (interest-scheme
                                  (when d-node
                                       (find-if
                                         #'(lambda (is)
                                               (and
                                                 (eq (is-reason is) reason)
                                                 (eq (is-premise is) premise)
                                                 (eq (is-target-interest is) interest)
                                                 (eq (is-basis is) basis)
                                                 (eq (is-remaining-premises is) (cdr remaining-premises))
                                                 (eq (is-binding is) binding)
                                                 (eq (is-supposition is) supposition)
                                                 (eq (is-generating-node is) generating-node)))
                                         (d-node-interest-schemes d-node)))))
                        (when (null interest-scheme)
                             (incf *interest-scheme-number*)
                             (setf interest-scheme
                                      (make-interest-scheme
                                        :reason reason
                                        :premise premise
                                        :number (incf *is-number*)
                                        :target-interest interest
                                        :basis basis
                                        :clues clues
                                        :remaining-premises (cdr remaining-premises)
                                        :binding binding
                                        :instantiations instantiations
                                        :supposition supposition
                                        :generating-node generating-node
                                        :supposition-variables (supposition-variables supposition)
                                        :used-premise-variables
                                        (if is0 (union (fp-variables premise) (is-used-premise-variables is0))
                                             (fp-variables premise))
                                        :used-variables
                                        (if is0 (union (node-variables node) (is-used-variables is0))
                                             (interest-variables interest))))
                             (if d-node
                               (store-interest-scheme-at-d-node interest-scheme d-node)
                               (store-interest-scheme interest-scheme profile *top-d-node*))
                             (when *display?* (display-interest-scheme interest-scheme))
                             (if node (pushnew interest-scheme (generated-instantiated-premises (node-c-list node))))
                             (when is0 (pushnew interest-scheme (is-derived-premises is0)))
                             (discharge-interest-scheme
                               interest-scheme (is-d-node interest-scheme) priority depth))
                        interest-scheme)))))))

(defunction display-interest-scheme (interest-scheme)
    (princ "  Constructing interest-scheme #") (princ (is-number interest-scheme))
    (princ " for ") (princ (is-target-interest interest-scheme)) (terpri)
    (princ "  next premise:  ")
    (prinp (match-sublis (is-binding interest-scheme) (fp-formula (is-premise interest-scheme))))
    (terpri) (princ "  by ")
    (princ (ip-reason interest-scheme)) (princ ",  basis = ")
    (print-list (mapcar #'inference-number (is-basis interest-scheme)))
    (princ " with clues ") (print-list (mapcar #'inference-number (is-clues interest-scheme)) nil)
    (terpri) (terpri))

#| This returns the ip at which the premise is stored. |#
(defunction store-interest-scheme (interest-scheme profile d-node)
    (cond
      (profile (index-interest-scheme interest-scheme profile d-node))
      (t (store-interest-scheme-at-d-node interest-scheme d-node))))

(defunction store-interest-scheme-at-d-node (interest-scheme d-node)
    (push interest-scheme (d-node-interest-schemes d-node))
    (setf (is-d-node interest-scheme) d-node)
    interest-scheme)

(defunction index-interest-scheme (interest-scheme profile d-node)
    (let ((dn (e-assoc (car profile) (discrimination-tests d-node)))
            (new-profile (cdr profile)))
       (cond (dn
                    (cond
                      (new-profile
                        (index-interest-scheme interest-scheme new-profile dn))
                      (t (store-interest-scheme-at-d-node interest-scheme  dn))))
                   (new-profile
                     (index-interest-scheme-at-new-nodes interest-scheme d-node new-profile (car profile)))
                   (t (store-interest-scheme-at-new-d-node interest-scheme d-node (car profile))))))

#| Test is the final member of the formula-profile for the node-formula. |#
(defunction store-interest-scheme-at-new-d-node (interest-scheme  d-node test)
    (let ((dn (make-d-node
                     :d-node-number (incf *d-node-number*)
                     :d-node-description (cons test (d-node-description d-node))
                     :parent-d-node d-node)))
       (push dn *discrimination-net*)
       (push (cons test dn) (discrimination-tests d-node))
       (store-interest-scheme-at-d-node interest-scheme dn)))

(defunction index-interest-scheme-at-new-nodes (interest-scheme d-node profile test)
    (let ((dn (make-d-node
                     :d-node-number (incf *d-node-number*)
                     :d-node-description (cons test (d-node-description d-node))
                     :parent-d-node d-node)))
       (push (cons test dn) (discrimination-tests d-node))
       (push dn *discrimination-net*)
       (let ((desc (cdr profile)))
          (cond (desc (index-interest-scheme-at-new-nodes interest-scheme dn desc (car profile)))
                      (t (store-interest-scheme-at-new-d-node interest-scheme dn (car profile)))))))

#| These are redefined in oscar-graphics in MCL. |#
(when (not (equal (lisp-implementation-type) "Macintosh Common Lisp"))
     (defun invalidate-view (x &optional y) (declare (ignore x y))))

(defun make-oscar-window () nil)
(defun draw-n (x y z) (declare (ignore x y z)))
(defun flash-nodes (x y z w) (declare (ignore x y z w)))
(defun node-position (x y) (declare (ignore x y)))
(defun interest-position (x y) (declare (ignore x y)))
(defun node-color (x y) (declare (ignore x y)))
(defun draw-just-node (x y z w) (declare (ignore x y z w)))
(defun draw-just-undefeated-node (x y z) (declare (ignore x y z)))
(defun draw-just-defeated-node (x y z) (declare (ignore x y z)))
(defun pause-graphics ())
(defun draw-i (x y) (declare (ignore x y)))
(defun draw-interest (x y z) (declare (ignore x y z)))
(defun speak-text (x) (declare (ignore x)))
(defun pranc-to-string (x) (declare (ignore x)))
(defun monitor-assignment-tree (x) (declare (ignore x)))

#| Premises are pairs (formula, degree-of-justification). |#
(defunction queue-premise (premise)
   ; (setf P premise)
    (let* ((formula (mem1 premise))
              (sequent (list nil formula))
              (node
                (make-inference-node
                  :inference-number (incf *inference-number*)
                  :node-sequent sequent
                  :node-formula formula
                  :node-variables (formula-node-variables formula)
                  :node-kind :inference
                  :node-justification :given
                  :nearest-defeasible-ancestors (list nil)
                  :maximal-degree-of-support (mem2 premise)
                  :undefeated-degree-of-support (mem2 premise)
                  :old-undefeated-degree-of-support (mem2 premise)
                  :discounted-node-strength (mem2 premise)
              :background-knowledge (mem4 premise)))
              (queue-node
                (make-inference-queue-node
                  :queue-number (incf *queue-number*)
                  :enqued-item node
                  :item-kind :conclusion
                  :discounted-strength (mem2 premise)
                  :item-complexity (complexity sequent)))
              (link (make-support-link
                        :support-link-number (incf *support-link-number*)
                        :support-link-basis nil
                        :support-link-rule :given
                        :support-link-target node
                        :defeasible? t
                        :support-link-strength (mem2 premise)
                        :support-link-nearest-defeasible-ancestors (list (list node)))))
       (setf (node-queue-node node) queue-node)
       (setf (support-links node) (list link))
       (when (not (eql (mem2 premise) 1.0))
            (setf (nearest-defeasible-ancestors node) (list (list node)))
            (when (not (mem4 premise))
                 (adopt-interest-in-premise-defeater sequent node))
            )
       (setf (degree-of-preference queue-node) (premise-preference premise))
       (push node *inference-graph*)
       (if *log-on* (push node *reasoning-log*))
       (when *display?* (display-unsupported-node node))
       (when (not *deductive-only*)
            (push (cons node (mem2 premise)) (node-UDs *assignment-tree*))
            (push (cons node (mem2 premise)) (node-MPUDs *assignment-tree*))
            (push (cons link (mem2 premise)) (link-UDs *assignment-tree*))
            (push (cons link (mem2 premise)) (link-MPUDs *assignment-tree*)))
       (store-inference-node node formula)
       (discharge-interest-in
         node (corresponding-i-lists (node-c-list node)) nil t 1 nil)
       (setf *inference-queue*
                (ordered-insert queue-node *inference-queue* #'i-preferred))
       ))

(defunction adopt-interest-in-premise-defeater (S node)
    (let* ((supposition (sequent-supposition S))
              (formula (sequent-formula S))
              (rebutting-interest
                (let ((interests (interests-for (neg formula) nil)))
                   (when interests
                        (find-if #'(lambda (i)
                                          (and (null (deductive-interest i))
                                                    (== (interest-supposition i) supposition)))
                                     interests)))))
       (cond ((null rebutting-interest)
                    (setf rebutting-interest
                             (make-interest
                               :interest-number (incf *interest-number*)
                               :interest-sequent (list supposition (neg formula))
                               :interest-formula (neg formula)
                               :interest-supposition supposition
                               :interest-priority *base-priority*
                               :interest-defeatees (support-links node)))
                    (store-interest rebutting-interest)
                    (when *display?*
                         (display-interest rebutting-interest)
                         (princ
                           "                                        Of interest as defeater for inference-node ")
                         (princ *inference-number*) (terpri))
                    (when *log-on*
                         (push rebutting-interest *reasoning-log*)
                         (when (and *display?* *graphics-on* *graph-interests*) (draw-i rebutting-interest *og*)))
                    (queue-interest rebutting-interest (defeater-priority rebutting-interest)))
                   (t
                     (readopt-interest rebutting-interest (list node))))))

#| The following introduces new nodes for a desire with a new content, resets the
desire-strength for a previous desire with an altered strength, and retracts desires
whose new desire-strengths are zero. |#
(defunction queue-desire (desire)
    (let* ((formula (desire-content desire))
              (sequent (list nil formula))
              (node (find-if
                           #'(lambda (node)
                                 (and (eq (node-kind node) :desire)
                                           (equal (node-sequent node) sequent)))
                           *desires*)))
       (cond (node
                    (let ((strength (maximal-degree-of-support node)))
                       (cond ((zerop strength)
                                    (pull node *desires*)
                                    (pull node *processed-desires*)
                                    (pull (cons formula (node-c-list node)) *inference-graph*)
                                    (let ((queue-node (node-queue-node node)))
                                       (when queue-node (pull queue-node *inference-queue*))))
                                   (t
                                     (let ((queue-node (node-queue-node node)))
                                        (when queue-node
                                             (setf (degree-of-preference queue-node)
                                                      (desire-preference desire))
                                             (setf *inference-queue*
                                                      (ordered-insert queue-node
                                                                                  (remove queue-node *inference-queue*)
                                                                                  #'i-preferred))))))))
                   (t
                     (let* ((node
                                (make-inference-node
                                  :inference-number (incf *inference-number*)
                                  :node-sequent sequent
                                  :node-formula formula
                                  :node-supposition nil
                                  :node-kind :desire
                                  :nearest-defeasible-ancestors (list nil)
                                  :maximal-degree-of-support (desire-strength desire)
                                  :undefeated-degree-of-support (desire-strength desire)
                                  :discounted-node-strength (desire-strength desire)))
                               (queue-node
                                 (make-inference-queue-node
                                   :queue-number (incf *queue-number*)
                                   :enqued-item node
                                   :item-kind :conclusion
                                   :discounted-strength 1.0
                                   :item-complexity (complexity sequent))))
                        (setf (node-queue-node node) queue-node)
                        (setf (degree-of-preference queue-node) (desire-preference desire))
                        (push node *inference-graph*)
                        (when *display?* (display-unsupported-node node))
                        (setf (node-UDs *assignment-tree*)
                                 (cons (cons node (desire-strength desire)) (node-UDs *assignment-tree*)))
                        (setf (node-MPUDs *assignment-tree*)
                                 (cons (cons node (desire-strength desire)) (node-MPUDs *assignment-tree*)))
                        (push node *desires*)
                        (setf *inference-queue*
                                 (ordered-insert queue-node *inference-queue* #'i-preferred)))))))

#| The following treats percepts as always new.  If they fade before they are retrieved
from the *inference-queue*, this has no effect.  They are left on the queue anyway
for subsequent processing. |#
(defunction queue-percept (percept)
    (let* ((formula (list 'throughout (percept-content percept)
                                    (list 'closed (percept-date percept) (percept-date percept))))
              (sequent (list nil formula))
              (node
                (make-inference-node
                  :inference-number (incf *inference-number*)
                  :node-sequent sequent
                  :node-formula formula
                  :node-supposition nil
                  :node-kind :percept
                  :nearest-defeasible-ancestors (list nil)
                  :node-justification percept
                  :maximal-degree-of-support (percept-clarity percept)
                  :undefeated-degree-of-support (percept-clarity percept)
                  :discounted-node-strength (percept-clarity percept)
              :background-knowledge t))
              (queue-node
                (make-inference-queue-node
                  :queue-number (incf *queue-number*)
                  :enqued-item node
                  :item-kind :conclusion
                  :discounted-strength 1.0
                  :item-complexity (sequent-complexity sequent))))
       (when *log-on* (push node *reasoning-log*))
       (setf (node-queue-node node) queue-node)
       (setf (degree-of-preference queue-node) (percept-preference percept))
       (push node *inference-graph*)
       (store-inference-node node (node-formula node))
       (when *display?* (display-unsupported-node node))
       (setf (node-UDs *assignment-tree*)
                (cons (cons node (percept-clarity percept)) (node-UDs *assignment-tree*)))
       (setf (node-MPUDs *assignment-tree*)
                (cons (cons node (percept-clarity percept)) (node-MPUDs *assignment-tree*)))
       (setf *inference-queue*
                (ordered-insert queue-node *inference-queue* #'i-preferred))))

(defunction think ()
    (when (read-char-no-hang) (clear-input) (throw 'die nil))
    (when (and *display-inference-queue* *display?*) (display-inference-queue))
    (when (eq *cycle* *start-trace*)
      (trace-on)
      #+MCL
      (when (equal (lisp-implementation-type) "Macintosh Common Lisp")
        (menu-item-disable (oscar-graphics-menu-item "Trace on"))
        (menu-item-enable (oscar-graphics-menu-item "Trace off"))
        (menu-item-enable (oscar-graphics-menu-item "Trace from"))
        (menu-item-disable (oscar-graphics-menu-item "Display on"))
        (menu-item-enable (oscar-graphics-menu-item "Display off"))
        (menu-item-enable (oscar-graphics-menu-item "Display from"))))
    (when (eq *cycle* *start-display*)
      (display-on)
      #+MCL
      (when (equal (lisp-implementation-type) "Macintosh Common Lisp")
        (menu-item-disable (oscar-graphics-menu-item "Display on"))
        (menu-item-enable (oscar-graphics-menu-item "Display off"))
        (menu-item-enable (oscar-graphics-menu-item "Display from"))))
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
                                     (let ((query (enqued-item Q)))
                                       (setf (query-queue-node query) nil)
                                       (reason-backwards-from-query query priority 0)))
                                   ((eq (item-kind Q) :interest)
                                     (let ((interest (enqued-item Q)))
                                       (setf (interest-queue-node interest) nil)
                                       (reason-backwards-from interest priority 0)
                                       (form-epistemic-desires-for interest)))))))))
    (when *new-links*
         (update-beliefs)
         (setf *new-links* nil)))

#| The following runs individual problems or lists of problems from the list *problems*.
(test) runs the entire set.  (test n) runs just problem n.  (test n t) starts with problem n
and runs the rest of the set.  (test n m) runs problems n through m.  (test n :skip '(i j k))
starts with problem n and runs the rest of the set except for i, j, and k.  (test n m :skip '(i j k))
runs problems n through m, skipping i, j, and k.  (test :skip i j k) runs all the problems
except i, j, k. |#
(defunction test (&rest rest)
    (terpri) (princ "(") (princ "                                 ") (princ *version*) (princ "          ")
    (let ((time (multiple-value-list (get-decoded-time))))
       (princ (mem5 time)) (princ "/") (princ (mem4 time)) (princ "/")
       (princ (mem6 time)) (princ "          ") (princ (mem3 time))
       (princ ":") (if (< (mem2 time) 10) (princ "0")) (princ (mem2 time))
       (princ ":") (if (< (mem2 time) 10) (princ "0")) (princ (mem1 time))
       (terpri) (terpri))
    (princ "*reductio-discount* = ") (princ *reductio-discount*) (terpri)
    (princ "*reductio-interest* = ") (princ *reductio-interest*) (terpri)
    (princ "*skolem-multiplier* = ") (princ *skolem-multiplier*) (terpri)
    (princ "*quantifier-discount* = ") (princ *quantifier-discount*) (terpri)
    (setf *test-log* nil)
    (cond ((null rest)
                 ;; (test)
                 (dolist (P *problems*)
                     (run-reasoning-problem P)
                     (when *pause*
                          (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                          (read-char))))
                ((equal (mem1 rest) :skip)
                  ;; (test :skip i j k)
                 (dolist (P *problems*)
                     (when (not (mem (car P) (cdr rest)))
                          (run-reasoning-problem P)
                          (when *pause*
                               (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                               (read-char)))))
                (t (let ((start (mem1 rest)))
                      (cond
                        ((null (cdr rest))
                          ;; (test n)
                          (run-reasoning-problem (assoc start *problems*)))
                        ((eq (mem2 rest) t)
                          ;; (test n t)
                          (dolist (P (mem (assoc start *problems*) *problems*))
                              (run-reasoning-problem P)
                              (when *pause*
                                   (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                                   (read-char))))
                        ((equal (mem2 rest) :skip)
                          ;; (test n :skip i j k)
                          (dolist (P (mem (assoc start *problems*) *problems*))
                              (when (not (mem (car P) (cdr rest)))
                                   (run-reasoning-problem P)
                                   (when *pause*
                                        (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                                        (read-char)))))
                        ((numberp (mem2 rest))
                          ;; (test n m) and (test n m :skip i j k)
                          (dolist (P (mem (assoc start *problems*) *problems*))
                              (when (and (not (mem (car P) (cdddr rest))) (not (> (car P) (mem2 rest))))
                                   (run-reasoning-problem P)
                                   (when (and *pause* (not (= (car P) (mem2 rest))))
                                        (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                                        (read-char)))))))))
    (setf *test-log*
          (list *version* *reductio-discount* *reductio-interest* *skolem-multiplier* *quantifier-discount*
                *test-log*))
    (when (not *display?*) (display-test-log))
    (terpri)
    (princ *test-log*)
    (terpri) (princ ")")
    (terpri))

(defun pause-on () (setf *pause* t))
(defun pause-off () (setf *pause* nil))

(defunction display-test-log ()
    (princ "=========================== TEST RESULTS ===========================")
    (terpri) (terpri)
    (princ "                                                                                ") (princ (mem1 *test-log*))
    (when *comparison-log*
      (princ "                        ") (princ (mem1 *comparison-log*))
      (princ "                   ratio of run times"))
    (terpri)
    (princ "          *reductio-discount*:                                 ") (princ (mem2 *test-log*))
    (when *comparison-log*
      (princ "                                      ") (princ (mem2 *comparison-log*)))
    (terpri)
    (princ "          *reductio-interest*:                                   ") (princ (mem3 *test-log*))
    (when *comparison-log*
      (princ "                                    ") (princ (mem3 *comparison-log*)))
    (terpri)
    (princ "          *skolem-multiplier*:                                   ") (princ (mem4 *test-log*))
    (when *comparison-log*
      (princ "                                    ") (princ (mem4 *comparison-log*)))
    (terpri)
    (princ "          *quantifier-discount*:                                   ") (princ (mem5 *test-log*))
    (when (and *comparison-log* (numberp (mem5 *comparison-log*)))
      (princ "                                    ") (princ (mem5 *comparison-log*)))
    (terpri) (terpri)
    (let ((ratios nil))
      (dolist (L (reverse (mem6 *test-log*)))
	(let* ((n (mem1 L))
	       (L* (assoc
		    n (if (numberp (mem5 *comparison-log*))
			  (mem6 *comparison-log*) (mem5 *comparison-log*)) :test 'equal)))
	  (princ "#") (princ n)
	  (princ "                                                                          ")
	  (display-run-time-in-seconds (mem2 L))
	  (when L* (princ "                            ") (display-run-time-in-seconds (mem2 L*))
	    (cond ((and (not (zerop (mem2 L))) (not (zerop (mem2 L*))))
		   (let ((ratio (/ (mem2 L) (mem2 L*))))
		     (push ratio ratios)
		     (princ "                            ")
		     (princ
                                            ; (if (< (abs (- (mem2 L) (mem2 L*))) 5) 1.0
                                            ;      (float (/ (truncate (* 100 ratio)) 100)))
		      (float (/ (truncate (* 1000 ratio)) 1000))
		      )))
                                       ; (let ((ratio
                                       ;           (if (< (abs (- (mem2 L) (mem2 L*))) 15) 1.0
                                       ;                (/ (mem2 L) (mem2 L*)))))
                                       ;    (push ratio ratios)
                                       ;    (princ "                            ")
                                       ;    (princ (float (/ (truncate (* 100 ratio)) 100)))))
		  (t (princ "                            ##"))))
	  (terpri)
	  (princ "           cumulative argument length:                 ") (princ (mem3 L))
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
	    (cond ((and (not (zerop (mem4 L))) (not (zerop (mem4 L*))))
		   (princ "                                      ")
		   (let ((d (- (mem4 L) (mem4 L*))))
		     (cond ((> d 0) (princ "+") (princ d))
			   ((< d 0) (princ d))
			   (t (princ "  --")))))
		  (t (princ "                            --"))))
	  (terpri) (terpri))
	(terpri))
      ; (when ratios
      ;      (princ "                                                                               average ratio of run times = ")
      ;      (let ((average (/ (apply '+ ratios) (length ratios))))
      ;         (princ (float (/ (truncate (* 10000 average)) 10000))))
      ;      (terpri))
      (when ratios
	(princ "geometric average ratio of run times = ")
	(setf ratios (remove 0 ratios))
	(let ((average (expt (apply '* ratios) (/ 1 (length ratios)))))
	  (princ (float (/ (truncate (* 10000 average)) 10000))))
	(terpri))))

(defunction rerun (&rest args)
    (progn
        (terpri) (princ "(") (princ "                                 ") (princ *version*) (princ "          ")
        (let ((time (multiple-value-list (get-decoded-time))))
           (princ (mem5 time)) (princ "/") (princ (mem4 time)) (princ "/")
           (princ (mem6 time)) (princ "          ") (princ (mem3 time))
           (princ ":") (if (< (mem2 time) 10) (princ "0")) (princ (mem2 time))
           (princ ":") (if (< (mem2 time) 10) (princ "0")) (princ (mem1 time))
           (terpri) (terpri))
        (princ "*reductio-discount* = ") (princ *reductio-discount*) (terpri)
        (princ "*reductio-interest* = ") (princ *reductio-interest*) (terpri)
        (princ "*skolem-multiplier* = ") (princ *skolem-multiplier*) (terpri)
        (princ "*quantifier-discount* = ") (princ *quantifier-discount*) (terpri))
    (if (stringp (mem1 *test-log*)) (setf *test-log* (cdr (mem6 *test-log*))))
    (let ((rest (cons *problem-number* args)))
       (cond ((equal (mem1 rest) :skip)
                    ;; (test :skip i j k)
                    (dolist (P *problems*)
                        (when (not (mem (car P) (cdr rest)))
                             (run-reasoning-problem P)
                             (when *pause*
                                  (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                                  (read-char)))))
                   (t (let ((start (mem1 rest)))
                         (cond
                           ((null (cdr rest))
                             ;; (test n)
                             (run-reasoning-problem (assoc start *problems*)))
                           ((eq (mem2 rest) t)
                             ;; (test n t)
                             (dolist (P (mem (assoc start *problems*) *problems*))
                                 (run-reasoning-problem P)
                                 (when *pause*
                                      (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                                      (read-char))))
                           ((equal (mem2 rest) :skip)
                             ;; (test n :skip i j k)
                             (dolist (P (mem (assoc start *problems*) *problems*))
                                 (when (not (mem (car P) (cdr rest)))
                                      (run-reasoning-problem P)
                                      (when *pause*
                                           (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                                           (read-char)))))
                           ((numberp (mem2 rest))
                             ;; (test n m) and (test n m :skip i j k)
                             (dolist (P (mem (assoc start *problems*) *problems*))
                                 (when (and (not (mem (car P) (cdddr rest))) (not (> (car P) (mem2 rest))))
                                      (run-reasoning-problem P)
                                      (when (and *pause* (not (= (car P) (mem2 rest))))
                                           (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                                           (read-char))))))))))
    (setf *test-log*
          (list *version* *reductio-discount* *reductio-interest* *skolem-multiplier* *quantifier-discount*
                *test-log*))
    (when (not *display?*) (display-test-log))
    (terpri)
    (princ *test-log*)
    (terpri) (princ ")") (terpri))

(defunction run (&rest args)
    (progn
        (terpri) (princ "(") (princ "                                 ") (princ *version*) (princ "          ")
        (let ((time (multiple-value-list (get-decoded-time))))
           (princ (mem5 time)) (princ "/") (princ (mem4 time)) (princ "/")
           (princ (mem6 time)) (princ "          ") (princ (mem3 time))
           (princ ":") (if (< (mem2 time) 10) (princ "0")) (princ (mem2 time))
           (princ ":") (if (< (mem2 time) 10) (princ "0")) (princ (mem1 time))
           (terpri) (terpri))
        (princ "*reductio-discount* = ") (princ *reductio-discount*) (terpri)
        (princ "*reductio-interest* = ") (princ *reductio-interest*) (terpri)
        (princ "*skolem-multiplier* = ") (princ *skolem-multiplier*) (terpri)
        (princ "*quantifier-discount* = ") (princ *quantifier-discount*) (terpri))
    (when (stringp (mem1 *test-log*)) (setf *test-log* (mem6 *test-log*)))
    (let ((rest (cons (1+ *problem-number*) args)))
       (cond ((equal (mem1 rest) :skip)
                    ;; (test :skip i j k)
                    (dolist (P *problems*)
                        (when (not (mem (car P) (cdr rest)))
                             (run-reasoning-problem P)
                             (when *pause*
                                  (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                                  (read-char)))))
                   (t (let ((start (mem1 rest)))
                         (cond
                           ((null (cdr rest))
                             ;; (test n)
                             (run-reasoning-problem (assoc start *problems*)))
                           ((eq (mem2 rest) t)
                             ;; (test n t)
                             (dolist (P (mem (assoc start *problems*) *problems*))
                                 (run-reasoning-problem P)
                                 (when *pause*
                                      (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                                      (read-char))))
                           ((equal (mem2 rest) :skip)
                             ;; (test n :skip i j k)
                             (dolist (P (mem (assoc start *problems*) *problems*))
                                 (when (not (mem (car P) (cdr rest)))
                                      (run-reasoning-problem P)
                                      (when *pause*
                                           (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                                           (read-char)))))
                           ((numberp (mem2 rest))
                             ;; (test n m) and (test n m :skip i j k)
                             (dolist (P (mem (assoc start *problems*) *problems*))
                                 (when (and (not (mem (car P) (cdddr rest))) (not (> (car P) (mem2 rest))))
                                      (run-reasoning-problem P)
                                      (when (and *pause* (not (= (car P) (mem2 rest))))
                                           (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                                           (read-char))))))))))
    (setf *test-log*
          (list *version* *reductio-discount* *reductio-interest* *skolem-multiplier* *quantifier-discount*
                *test-log*))
    (when (not *display?*) (display-test-log))
    (terpri)
    (princ *test-log*)
    (terpri) (princ ")") (terpri))

(defunction run-reasoning-problem (P)
    (setf *problem-number* (car P))
    (setf *pretty-list* nil *string-symbols* nil)
    (terpri)
    (princ
      "******************************************************************************************")
    (terpri)
    (princ
      "******************************************************************************************")
    (terpri)
    (display-problem P)
    (gc)
    (COGITATE)
    (terpri))

#|  COGITATE is used in place of OSCAR in TEST.  COGITATE does all reasoning
from premises, ignoring environmental-input (desires) and percepts.
Premises are triples (formula, supposition, degree-of-justification).
Premises can be defeated by rebutting defeaters, but there is no way
to have an undercutting defeater.  |#
(defunction COGITATE ()
    (let ((deductive-only *deductive-only*)
            (time nil))
      (unwind-protect
          (progn
              (when
                   (and
                     (not *deductive-only*)
                     (every #'(lambda (p) (eql (mem2 p) 1.0)) *premises*)
                     (every #'(lambda (r) (not (defeasible-rule r))) *forwards-logical-reasons*)
                     (every #'(lambda (r) (not (defeasible-rule r))) *forwards-substantive-reasons*)
                     (every #'(lambda (r) (not (defeasible-rule r))) *backwards-logical-reasons*)
                     (every #'(lambda (r) (not (defeasible-rule r))) *backwards-substantive-reasons*))
                   (setf *deductive-only* t))
             ; (initialize-reasoner)
              (setf *cycle* 0)
              ; (gc)
              (setf time (get-internal-run-time))
              (let ((abort-time
                        (if *time-limit* (+ (* *time-limit* internal-time-units-per-second 60) time))))
                (catch 'die
                   (initialize-reasoner)
               (dolist (query *ultimate-epistemic-interests*)
                  (reason-backwards-from-query query (query-strength query) 0))
                   (loop
                     (incf *cycle*)
                     (dolist (premise *premises*)
                         (when (eql (mem3 premise) *cycle*)
                              (pull premise *premises*)
                              (queue-premise (list (mem1 premise) nil (mem2 premise)))))
                     (think-or-die)
                     (when (and abort-time (> (get-internal-run-time) abort-time))
                          (princ "NO PROOF WAS FOUND WITHIN ") (princ *time-limit*) (princ " MINUTES.")
                          (throw 'die nil))))
                (setf time (- (get-internal-run-time) time))))
          (setf *deductive-only* deductive-only))
      (terpri)
      (display-queries) (terpri)
      (princ "Elapsed time = ") (display-run-time-in-seconds time) (terpri)
      (let ((nodes nil))
        (dolist (query *ultimate-epistemic-interests*)
            (dolist (N (query-answers query))
                (pushnew N nodes)))
        (compute-relevant-nodes nodes)
        (let ((argument-length (length *relevant-nodes*)))
          (cond (*proofs?* (terpri) (show-arguments))
                    (t        (princ "Cumulative size of arguments = ") (princ argument-length) (terpri)
                               (princ "Size of inference-graph = ") (princ *inference-number*)
                               (princ " of which ") (princ *unused-suppositions*)
                               (princ " were unused suppositions.") (terpri)
                               (princ (truncate (* argument-length 100) *inference-number*))
                               (princ "% of the inference-graph was used in the argument.") (terpri)))
          (princ *interest-number*) (princ " interests were adopted.") (terpri)
          (let ((nodes
                    (subset #'(lambda (n)
                                       (or (equal (node-justification n) :reductio-supposition)
                                             (equal (node-justification n) :supposition)))
                                  *inference-graph*)))
            (princ (length nodes)) (princ " suppositions were made.") (terpri))
          (when *display?*
               (princ "The following nodes were used in the arguments:") (terpri)
               (print-list (order (mapcar #'inference-number *relevant-nodes*) #'<) 40))
          (push (list *problem-number* time argument-length
                           (- *inference-number* *unused-suppositions*)) *test-log*)
          (when *log-on* (terpri) (display-reasoning))
          ; (terpri) (display-conclusions) (terpri)
          ; (terpri) (display-inference-graph) (terpri)
          ; (terpri) (display-assignment-tree)
          ; (setf *assignment-tree* (compute-assignment-tree))
          ; (terpri) (display-assignment-tree (compute-assignment-tree))
          ))))

#| This restarts the reasoning, beginning with the inference-queue item x.  x can be the
number of a queue-node, or an interest or a conclusion.  If x is empty, reasoning restarts
without altering the inference-queue. |#
(defunction try (&optional x)
    (when x
         (let ((Q
                   (cond ((numberp x)
                                (find-if #'(lambda (item) (eql (queue-number item) x)) *inference-queue*))
                               ((interest-p x) (interest-queue-node x))
                               ((inference-node-p x) (node-queue-node x)))))
            (setf *inference-queue* (cons Q (remove Q *inference-queue*)))))
    (catch 'die
        (loop (incf *cycle*) (think-or-die)))
    (terpri)
    (display-queries) (terpri)
    (let ((nodes nil))
       (dolist (query *ultimate-epistemic-interests*)
           (dolist (N (query-answers query))
               (pushnew N nodes)))
       (compute-relevant-nodes nodes)
       (let ((argument-length (length *relevant-nodes*)))
          (cond (*proofs?* (terpri) (show-arguments))
                      (t
                        (princ "Cumulative size of arguments = ") (princ argument-length) (terpri))))))

#| When the following is run before a problem is run, when an interest of number n is
queued, it goes on the front of the inference-queue. |#
(defunction try-interest (&optional n)
    (cond ((null n) (setf *priority-interests* nil))
                (t (push n *priority-interests*))))

(defunction compute-relevant-nodes (nodes)
    (setf *relevant-nodes* nil)
    (dolist (node nodes) (add-relevant-nodes node))
    *relevant-nodes*)

(defunction add-relevant-nodes (node)
    (when (not (member node *relevant-nodes*))
         (push node *relevant-nodes*)
         (dolist (m (motivating-nodes node)) (add-relevant-nodes m))
         (dolist (L (support-links node))
             (dolist (b (support-link-basis L)) (add-relevant-nodes b))
             (dolist (d (support-link-defeaters L)) (add-relevant-nodes d)))))

(defunction display-reasoning (&optional full-display)
    (cond
      (full-display (display-reasoning-fully))
      (t
        (progn
            (princ "===========================================================================")
            (terpri) (princ "THE FOLLOWING IS THE REASONING INVOLVED IN THE SOLUTION") (terpri)
            (princ "Nodes marked DEFEATED have that status at the end of the reasoning.")
            (terpri)(terpri))
        (let ((nodes nil))
           (dolist (query *ultimate-epistemic-interests*)
               (dolist (N (query-answers query)) (pushnew N nodes)))
           (compute-relevant-nodes nodes)
           (setf *not-strictly-relevant-nodes* (not-strictly-relevant-nodes))
           (let* ((ultimate-interests (mapcar #'query-interest *ultimate-epistemic-interests*))
                     (enabling-interests
                       (union (unionmapcar+ #'enabling-interests *relevant-nodes*)
                                  (unionmapcar+ #'generating-defeat-interests *relevant-nodes*)))
                     (closure (generated-nodes-and-interests
                                      *relevant-nodes* (union ultimate-interests enabling-interests) ultimate-interests))
                     (nodes-used (remove-duplicates (mem1 closure)))
                     (interests-used (remove-duplicates (mem2 closure)))
                     (interests-used-in-proof (remove-duplicates (mem3 closure)))
                     (log (reverse *reasoning-log*))
                     (boundary nil)
                     (nodes-displayed nil))
              (when *graph-log* (make-oscar-window))
              (dolist (x log)
                  (cond ((inference-node-p x)
                               (when (member x nodes-used)
                                    (display-node
                                      x *relevant-nodes* nodes-used interests-used enabling-interests nodes-displayed)
                                    (push x nodes-displayed)))
                              ((interest-p x)
                                (when (member x interests-used)
                                     (display-used-interest
                                       x *relevant-nodes* nodes-used interests-used
                                       enabling-interests interests-used-in-proof)))
                              (t (setf boundary (display-peripherals x boundary nodes-used)))))
              (when (and *graph-log* (boundp '*speak*) *speak*)
                   (setf nodes
                            (subset
                              #'(lambda (n)
                                    (some #'(lambda (q) (>= (compute-undefeated-degree-of-support n) (query-strength q)))
                                                 (answered-queries n)))
                              nodes))
                   (when nodes
                        (speak-text
                          (cond
                            ((cdr nodes)
                              (cat-list
                                (list "In conclusion, " (pranc-to-string (pretty (node-formula (car nodes))))
                                        (mapcar #'(lambda (n) (cat ", " (pranc-to-string (pretty (node-formula n)))))
                                                        (cdr nodes)))))
                            (t (cat "In conclusion, " (pranc-to-string (pretty (node-formula (car nodes))))))))))
              (when *graph-log* (invalidate-view *og*))
              (princ "============================================================")
              (terpri) (terpri))))))

(defunction display-reasoning-for (node)
    (progn
        (princ "(") (terpri)
        (princ "===========================================================================")
        (terpri) (princ "THE FOLLOWING IS THE REASONING RELATED TO NODE ") (princ (inference-number node))
        (terpri)
        (princ "Nodes marked DEFEATED have that status at the end of the reasoning.")
        (terpri)(terpri))
    (let ((nodes (list node)))
      (compute-relevant-nodes nodes)
      (let* (
                (enabling-interests
                  (union (unionmapcar+ #'enabling-interests *relevant-nodes*)
                             (unionmapcar+ #'generating-defeat-interests *relevant-nodes*)))
                (closure (generated-nodes-and-interests *relevant-nodes* enabling-interests nil))
                (nodes-used (remove-duplicates (mem1 closure)))
                (interests-used (remove-duplicates (mem2 closure)))
                (interests-used-in-proof (remove-duplicates (mem3 closure)))
                (log (reverse *reasoning-log*))
                (boundary nil)
                (nodes-displayed nil))
        (when *graph-log* (make-oscar-window))
        (dolist (x log)
            (cond ((inference-node-p x)
                        (when (member x nodes-used)
                             (display-node
                               x *relevant-nodes* nodes-used interests-used enabling-interests nodes-displayed)
                             (push x nodes-displayed)))
                      ((interest-p x)
                        (when (member x interests-used)
                             (display-used-interest
                               x *relevant-nodes* nodes-used interests-used
                               enabling-interests interests-used-in-proof)))
                      (t (setf boundary (display-peripherals x boundary nodes-used)))))
        (when (and *graph-log* (boundp '*speak*) *speak*)
             (setf nodes
                      (subset
                        #'(lambda (n)
                              (some #'(lambda (q) (>= (compute-undefeated-degree-of-support n) (query-strength q)))
                                          (answered-queries n)))
                        nodes))
             (when nodes
                  (speak-text
                    (cond
                      ((cdr nodes)
                        (cat-list
                          (list "In conclusion, " (pranc-to-string (pretty (node-formula (car nodes))))
                                 (mapcar #'(lambda (n) (cat ", " (pranc-to-string (pretty (node-formula n)))))
                                                (cdr nodes)))))
                      (t (cat "In conclusion, " (pranc-to-string (pretty (node-formula (car nodes))))))))))
        (when *graph-log* (invalidate-view *og*))
        (princ "============================================================")
        (terpri)
        (princ ")") (terpri))))

(defunction display-reasoning-fully ()
    (progn
        (princ "===========================================================================")
        (terpri) (princ "THE FOLLOWING IS THE REASONING INVOLVED IN THE SOLUTION") (terpri)
        (princ "Nodes marked DEFEATED have that status at the end of the reasoning.")
        (terpri)(terpri))
    (let ((nodes nil))
       (dolist (query *ultimate-epistemic-interests*)
           (dolist (N (query-answers query)) (pushnew N nodes)))
       (let* ((ultimate-interests (mapcar #'query-interest *ultimate-epistemic-interests*))
                 (enabling-interests (unionmapcar+ #'enabling-interests
                                                                                 *relevant-nodes*))
                 (closure (generated-nodes-and-interests
                                      *relevant-nodes* (union ultimate-interests enabling-interests) ultimate-interests))
                 (nodes-used (mem1 closure))
                 (interests-used (mem2 closure))
                 (interests-used-in-proof (mem3 closure))
                 (previous-item nil)
                 (log (reverse *reasoning-log*))
                 (boundary nil)
                 (nodes-displayed nil))
          (when *graph-log* (make-oscar-window))
          (dolist (x log)
              (cond
                ((inference-node-p x)
                  (when (and previous-item (member previous-item interests-used))
                       (princ "                                        ")
                       (princ "==========================================================")
                       (terpri) (terpri))
                  (cond ((member x nodes-used)
                               (when (or (null previous-item)
                                                  (not (member previous-item nodes-used)))
                                    (terpri)
                                    (princ "====================== NODES USED ==========================")
                                    (terpri))
                               (full-display-node x *relevant-nodes*))
                              (t (when (and previous-item (member previous-item nodes-used))
                                      (princ "============================================================")
                                      (terpri) (terpri))
                                  (display-node
                                    x *relevant-nodes* nodes-used interests-used enabling-interests nodes-displayed)
                                  (push x nodes-displayed))))
                ((interest-p x)
                  (when (and previous-item (member previous-item nodes-used))
                       (princ "============================================================")
                       (terpri) (terpri))
                  (cond ((member x interests-used)
                               (when (or (null previous-item)
                                                  (not (member previous-item interests-used)))
                                    (terpri) (princ "                                        ")
                                    (princ "=================== INTERESTS USED =======================")
                                    (terpri))
                               (full-display-used-interest x))
                              (t (when (and previous-item (member previous-item interests-used))
                                      (princ "                                        ")
                                      (princ "==========================================================")
                                      (terpri) (terpri))
                                  (display-used-interest
                                    x *relevant-nodes* nodes-used interests-used
                                    enabling-interests interests-used-in-proof))))
                (t (setf boundary (display-peripherals x boundary nodes-used))))
              (setf previous-item x))
          (when *graph-log* (invalidate-view *og*))
          (princ "============================================================")
          (terpri) (terpri))))

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
                      (when (and (boundp '*speak*) *speak*)
                           (speak-text "Node ")
                           (speak-text (write-to-string (inference-number (mem2 x))))
                           (speak-text "no longer answers query ")
                           (speak-text (write-to-string (query-number (mem3 x)))))))))
    boundary)

(defunction generated-nodes-and-interests (proof-nodes enabling-interests ultimate-interests)
   ; (p-princ enabling-interests)
    (setf *interests-used-in-proof* enabling-interests)
    (setf *used-nodes* proof-nodes)
    (setf *unprocessed-nodes* proof-nodes)
    (setf *used-interests* ultimate-interests)
    (setf *unprocessed-interests* nil)
    (loop
      (cond ((and (null *unprocessed-nodes*) (null *unprocessed-interests*))
                  (return (list *used-nodes* *used-interests* *interests-used-in-proof*)))
                (*unprocessed-nodes*
                  (process-unprocessed-node (car *unprocessed-nodes*) proof-nodes enabling-interests))
                (t (process-unprocessed-interest (car *unprocessed-interests*))))))

(defunction process-unprocessed-node (node proof-nodes enabling-interests)
    ; (princ "process-unprocessed-node ") (princ node) (terpri)
    (pull node *unprocessed-nodes*)
    (dolist (L (support-links node))
        (dolist (b (support-link-basis L))
            (when (not (member b *used-nodes*))
                 (push b *used-nodes*) (push b *unprocessed-nodes*)))
        (dolist (b (support-link-clues L))
         (when (not (member b *used-nodes*))
             (push b *used-nodes*) (push b *unprocessed-nodes*)))
        (let ((link (generating-interest-link L)))
          (when link
               (push (resultant-interest link) *used-interests*)
               (pull (resultant-interest link) *unprocessed-interests*)
               (dolist (interest (link-interests link))
                   (when (member node proof-nodes) (push interest *interests-used-in-proof*))
                   (when (not (member interest *used-interests*))
                        (push interest *used-interests*)
                        (push interest *unprocessed-interests*))))))
    (when (and (eq (node-justification node) :reduction-supposition)
                        (not (some #'(lambda (N)
                                                 (and (member N *used-interests*)
                                                          (equal (interest-formula N) (neg (node-formula node)))))
                                            enabling-interests))
                        (not (some #'(lambda (N)
                                                 (and (member N *used-interests*)
                                                          (equal (interest-formula N) (neg (node-formula node)))))
                                            (generating-interests node))))
         (let ((N (find-if #'(lambda (N) (equal (interest-formula N) (neg (node-formula node))))
                                  (generating-interests node))))
           (push N *used-interests*) (push N *unprocessed-interests*)))
    (when (and (eq (node-justification node) :supposition)
                        (not (some #'(lambda (N) (member N *used-interests*)) enabling-interests))
                        (not (some #'(lambda (N) (member N *used-interests*)) (generating-interests node))))
         (push (car (generating-interests node)) *used-interests*)
         (push (car (generating-interests node)) *unprocessed-interests*)))

(defunction process-unprocessed-interest (interest)
   ; (princ "process-unprocessed-interest ") (princ interest) (terpri)
   ; (when (eq interest (interest 8)) (break))
    (pull interest *unprocessed-interests*)
    (cond
      ((and (direct-reductio-interest interest)
                (not (some #'(lambda (N)  (member (car N) *used-nodes*)) (direct-reductio-interest interest))))
        (let ((N (caar (direct-reductio-interest interest))))
          (push N *used-nodes*) (push N *unprocessed-nodes*)))
      ((not (some #'(lambda (N) (member N *used-nodes*)) (discharging-nodes interest)))
        (let ((link (find-if #'(lambda (L) (every #'(lambda (N) (member N *used-interests*)) (link-interests L)))
                                   (left-links interest))))
          (when (null link)
               (setf link (find-if #'(lambda (L) (every #'(lambda (N) (member N *used-interests*)) (link-interests L)))
                                          (cancelled-left-links interest))))
          (when (null link) (setf link (car (left-links interest))))
          (when (null link) (setf link (car (cancelled-left-links interest))))
          (when link
               (dolist (N (link-interests link))
                   (when (not (member N *used-interests*))
                        (push N *used-interests*) (push N *unprocessed-interests*))))))))

(defunction store-interest-record (in record)
    (let ((in-record (assoc in *interest-record*)))
       (cond (in-record (push record (cdr in-record)))
                   (t (push (list in record) *interest-record*)))))

;(defunction generating-right-link (in used-interests used-nodes)
;   ; (when (eq in (interest 19)) (setf i in u used-interests un used-nodes) (break))
;   ;; (step (generating-right-link i u un))
;    (let ((L (find-if
;                  #'(lambda (L)
;                        (and
;                          (member (resultant-interest L) used-interests)
;                          (some #'(lambda (n) (member n used-nodes)) (discharging-nodes (link-interest L)))))
;                  (right-links in))))
;       (when (null L)
;            (setf L
;                     (find-if
;                       #'(lambda (L)
;                             (some #'(lambda (n) (member n used-nodes)) (discharging-nodes (link-interest L))))
;                       (right-links in))))
;       (when (null L)
;            (setf L (mem1
;                          (last (subset
;                                    #'(lambda (L) (member (resultant-interest L) used-interests))
;                                                (right-links in))))))
;       (when (null L)
;            (setf L (mem1 (last (right-links in)))))
;       L))

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
    (prinp (node-formula n))
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
    (princ "interest: ") (prinp (interest-formula interest))
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

(defunction strongly-discharging-node (dn interest proof-nodes enabling-interests)
    (or
      (some
        #'(lambda (dr)
              (some
                #'(lambda (pn)
                      (some
                        #'(lambda (SL)
                              (and (equal (support-link-rule SL) :reductio)
                                        (member dn (support-link-basis SL))
                                        (member (car dr) (support-link-basis SL))))
                        (support-links pn)))
                proof-nodes))
        (direct-reductio-interest interest))
      (some #'(lambda (L)
                        (and
                          (discharged-link L)
                          (member (resultant-interest L) enabling-interests)
                          (some
                            #'(lambda (pn)
                                  (and
                                    (member (resultant-interest L) (enabling-interests pn))
                                    (some
                                      #'(lambda (SL)
                                            (member dn (support-link-basis SL)))
                                      (support-links pn))))
                            proof-nodes)))
                   (right-links interest))))

#| This precedes the line of nodes by || . |#
(defunction full-display-node (n proof-nodes)
   (princ "||  # ") (princ (inference-number n))
   (terpri)
   (princ "||  ") (prinp (node-formula n))
   (when (node-supposition n)
        (princ "    supposition: ") (set-prinp (node-supposition n)))
   (when (not (member n proof-nodes)) (princ "   --  NOT USED IN PROOF"))
   (terpri)
    (when (node-justification n) (princ "||  by ") (princ (node-justification n)) (terpri))
    (when (support-links n)
         (princ "||  Inferred by:") (terpri)
         (dolist (L* (support-links n))
             (princ "||                support-link #") (princ (support-link-number L*))
             (princ " from ") (princ-set (mapcar #'inference-number (support-link-basis L*)))
             (princ " by ") (princ (support-link-rule L*))
             (when (support-link-defeaters L*)
                  (princ "  defeaters: ")
                  (princ-set (mapcar #'inference-number (support-link-defeaters L*))))
             (terpri)))
  ; (princ " by ") (princ (node-justification n))
   (let ((generating-interests (generating-interests n)))
      (cond ((> (length generating-interests) 1)
                   (princ "||  generated by interests ")
                   (print-list (mapcar #'interest-number generating-interests) 40))
                  ((equal (length generating-interests) 1)
                   (princ "||  generated by interest ")
                   (princ (interest-number (mem1 generating-interests)))))
      (when generating-interests (terpri)))
   (let ((interests (remove-duplicates (discharged-interests n))))
      (cond ((> (length interests) 1)
                   (princ "||  This discharges interests ") (print-list (mapcar #'interest-number interests) 40))
                  ((equal (length interests) 1)
                    (princ "||  This discharges interest ") (princ (interest-number (mem1 interests)))))
      (when interests (terpri))))

#| This precedes the line of interests by || . |#
(defunction full-display-used-interest (interest)
    (princ "                                        || # ") (princ (interest-number interest)) (terpri)
    (princ "                                        || ")
    (when (deductive-interest interest) (princ "deductive "))
    (when (reductio-interest interest) (princ "reductio "))
    (princ "interest: ") (prinp (interest-formula interest))
    (when (interest-supposition interest)
         (princ "    supposition: ")
         (set-prinp (interest-supposition interest)))
    (terpri)
    (when
         (some #'(lambda (L) (and (query-p (resultant-interest L)) (discharged-link L)))
                      (right-links interest))
         (princ "                                        || This is of ultimate interest") (terpri))
    (dolist (L (right-links interest))
        (when (and (discharged-link L) (not (query-p (resultant-interest L))))
             (princ "                                        || For ")
             (when (reductio-interest (resultant-interest L)) (princ "reductio "))
             (princ "interest ")
             (princ (interest-number (resultant-interest L)))
             (princ " by ") (princ (link-rule L))
             (terpri)))
    (let ((direct-reductio-interest (direct-reductio-interest interest)))
       (cond ((> (length direct-reductio-interest) 1)
                    (princ "                                        || Reductio interest generated by nodes ")
                    (print-list (mapcar #'inference-number direct-reductio-interest) 40) (terpri))
                   ((= (length direct-reductio-interest) 1)
                    (princ "                                        || Reductio interest generated by node ")
                    (princ (inference-number (mem1 direct-reductio-interest))) (terpri)))))

(defunction relevant-nodes (node &optional nodes-used)
    (when (not (member node nodes-used))
         (setf nodes-used (cons node nodes-used))
         (dolist (m (motivating-nodes node))
             (setf nodes-used (union (relevant-nodes m nodes-used) nodes-used)))
         (dolist (L (support-links node))
             (dolist (b (support-link-basis L))
                 (setf nodes-used (union (relevant-nodes b nodes-used) nodes-used)))
             (dolist (d (support-link-defeaters L))
                 (setf nodes-used (union (relevant-nodes d nodes-used) nodes-used))))
         nodes-used))

(defunction strictly-relevant-nodes ()
    (let ((nodes nil))
      (dolist (query *ultimate-epistemic-interests*)
          (dolist (N (query-answers query)) (pushnew N nodes)))
      (compute-strictly-relevant-nodes nodes)))

(defunction compute-strictly-relevant-nodes (nodes)
    (setf *strictly-relevant-nodes* nil)
    (dolist (node nodes) (add-strictly-relevant-nodes node))
    *strictly-relevant-nodes*)

(defunction add-strictly-relevant-nodes (node)
    (when (not (member node *strictly-relevant-nodes*))
         (push node *strictly-relevant-nodes*)
         (dolist (m (motivating-nodes node)) (add-strictly-relevant-nodes m))
         (dolist (L (support-links node))
             (dolist (b (support-link-basis L)) (add-strictly-relevant-nodes b)))))

(defunction not-strictly-relevant-nodes ()
    (order (set-difference *relevant-nodes* (strictly-relevant-nodes))
               #'(lambda (x y) (< (inference-number x) (inference-number y)))))

#| This is the same as think, but it aborts when the *inference-queue* is empty. |#
(defunction think-or-die ()
    ; (when (eql *cycle* 82) (break))
    (when (null *inference-queue*) (throw 'die nil))
    ; (when (read-char-no-hang) (clear-input) (throw 'die nil))
    ; (when (and (node 3) (not (zerop (readopted-supposition (node 3))))) (break))
    (when (eq *cycle* *start-trace*)
      (trace-on)
      #+MCL
      (when (equal (lisp-implementation-type) "Macintosh Common Lisp")
        (menu-item-disable (oscar-graphics-menu-item "Trace on"))
        (menu-item-enable (oscar-graphics-menu-item "Trace off"))
        (menu-item-enable (oscar-graphics-menu-item "Trace from"))
        (menu-item-disable (oscar-graphics-menu-item "Display on"))
        (menu-item-enable (oscar-graphics-menu-item "Display off"))
        (menu-item-enable (oscar-graphics-menu-item "Display from"))))
    (when (eq *cycle* *start-display*)
      (display-on)
      #+MCL
      (when (equal (lisp-implementation-type) "Macintosh Common Lisp")
        (menu-item-disable (oscar-graphics-menu-item "Display on"))
        (menu-item-enable (oscar-graphics-menu-item "Display off"))
        (menu-item-enable (oscar-graphics-menu-item "Display from"))))
    ; (display-assignment-tree)
    (when (and *display-inference-queue* *display?*) (display-inference-queue))
    (let ((Q (mem1 *inference-queue*)))
      (when *display?*
           (princ "---------------------------------------------------------------------------") (terpri)
           (princ *cycle*) (princ ":    ")
           (princ "Retrieving ") (princ (enqued-item Q))
           (princ " from the inference-queue.  Preference = ")
           (princ (float (/ (truncate (* 10000 (degree-of-preference Q))) 10000)))
           (terpri) (terpri))
      (pause)
      (setf *inference-queue* (cdr *inference-queue*))
      (cond ((eq (item-kind Q) :conclusion)
                  (let ((node (enqued-item Q)))
                    (store-processed-inference-node node)
                    (setf (node-queue-node node) nil)
                    (reason-forwards-from node 0)))
                (t
                  (let ((priority (retrieved-interest-priority (degree-of-preference Q) (item-complexity Q))))
                    (cond ((eq (item-kind Q) :query)
                                (let ((query (enqued-item Q)))
                                  (setf (query-queue-node query) nil)
                                  (reason-backwards-from-query query priority 0)))
                              ((eq (item-kind Q) :interest)
                                (let ((interest (enqued-item Q)))
                                  ; (when (equal interest (interest 58)) (trace-on))
                                  (setf (interest-queue-node interest) nil)
                                  (reason-backwards-from interest priority 0)
                                  (form-epistemic-desires-for interest))))))))
    (when *new-links*
         (update-beliefs)
         (setf *new-links* nil)))

(defunction display-inference-queue ()
    (princ "---------------------------------------------------------------------------") (terpri)
    (princ "inference-queue: ") (terpri)
    (dolist (Q *inference-queue*) (princ "  ") (princ (enqued-item Q))
                (princ "  degree-of-preference = ")
                (princ (float (/ (truncate (* 10000 (degree-of-preference Q))) 10000)))
                (let ((priority
                          (cond ((eq (item-kind q) :conclusion)
                                       (discounted-node-strength (enqued-item q)))
                                      ((eq (item-kind q) :query) 1.0)
                                      ((eq (item-kind q) :interest) (interest-priority (enqued-item q))))))
                   (princ "  priority = ")
                   (princ (float (/ (truncate (* 1000 priority)) 1000))))
                (terpri)))

;................................................. BACKWARDS REASONING ........................................

#| This introduces ?P queries and whether-queries. |#
(defunction reason-backwards-from-query (query priority  depth)
    ; (when (equal query (query 3)) (setf q query p priority d depth) (break))
     ;; (step (reason-backwards-from-query q p d))
    (let ((formula (query-formula query)))
       (cond
         ((whether-formula formula)
           (reason-backwards-from-whether-query query priority depth))
         ((?-genp formula)
           (reason-backwards-from-?-query query priority depth))
         (t
          (reason-backwards-from-simple-query query priority depth)))))

(defunction reason-backwards-from-whether-query (query priority depth)
    ; (when (equal query (query 1)) (setf q query p priority d depth) (break))
    (when *trace* (indent depth) (princ "REASON-BACKWARDS-FROM-QUERY") (terpri))
    (let* ((formula (mem2 (query-formula query)))
              (sequent (list nil formula))
              (link
                (make-interest-link
                  :link-number (incf *link-number*)
                  :resultant-interest query
              :link-strength (query-strength query)
                  :link-rule :answer))
              (positive-interest
                (let ((interests (interests-for formula nil)))
                   (when interests
                        (find-if #'(lambda (i)
                                          (and (null (interest-supposition i))
                                                    (eq (deductive-interest i) (deductive-query query))))
                                     interests))))
              (negative-interest
                (let ((interests (interests-for (neg formula) nil)))
                   (when interests
                        (find-if #'(lambda (i)
                                          (and (null (interest-supposition i))
                                                    (eq (deductive-interest i) (deductive-query query))))
                                     interests)))))
       (cond (positive-interest
                    (setf (degree-of-interest positive-interest)
                             (min (query-strength query) (degree-of-interest positive-interest)))
                    (setf (maximum-degree-of-interest positive-interest)
                             (max (query-strength query) (maximum-degree-of-interest positive-interest)))
                    (setf (interest-priority positive-interest) (maximum-degree-of-interest positive-interest))
                    (readopt-interest positive-interest nil)
                    (setf (link-interest link) positive-interest)
                    (push link (right-links positive-interest))
                    (push link *interest-links*)
                    (when (and *display?* *graphics-on* *graph-interests*)
                         (draw-interest positive-interest (interest-position positive-interest *og*) *og*))
                    (let ((Q (interest-queue-node positive-interest)))
                       (when Q
                            (setf (degree-of-preference Q)
                                     (maximum
                                       (list (degree-of-preference Q)
                                               (interest-preference
                                                 (query-strength query)
                                                 (sequent-complexity sequent)))))
                            (setf *inference-queue*
                                     (ordered-insert Q (remove Q *inference-queue*)
                                                                 #'i-preferred)))))
                   (t
                     (setf positive-interest
                              (make-interest
                                :interest-number (incf *interest-number*)
                                :interest-sequent sequent
                                :interest-formula formula
                                :interest-supposition nil
                                :right-links (list link)
                                :degree-of-interest (query-strength query)
                                :maximum-degree-of-interest (query-strength query)
                                :interest-priority (query-strength query)
                                :deductive-interest (deductive-query query)))
                     (store-interest positive-interest)
                     (when *display?* (display-interest positive-interest))
                     (when *log-on* (push positive-interest *reasoning-log*))
                     (when (and *display?* *graphics-on* *graph-interests*) (draw-i positive-interest *og*))
                     (setf (link-interest link) positive-interest)
                     (push link *interest-links*)
                     (apply-degenerate-backwards-reasons positive-interest priority (1+ depth))
                     (reason-backwards-from positive-interest priority (1+ depth))
                     (form-epistemic-desires-for positive-interest)))
       (setf (query-interest query) positive-interest)
       (dolist (cl (corresponding-c-lists (interest-i-list positive-interest)))
            (let ((conclusion
                     (find-if
                       #'(lambda (c)
                             (and (null (node-supposition c))
                                       (>= (compute-maximal-degree-of-support c)
                                              (query-strength query))))
                       (c-list-nodes  (mem1 cl)))))
              (when (and conclusion (not (member conclusion (supporting-nodes link))))
                              (push conclusion (supporting-nodes link))
                              (record-query-answers link))))
       (cond (negative-interest
                    (setf (degree-of-interest negative-interest)
                             (min (query-strength query) (degree-of-interest negative-interest)))
                    (setf (maximum-degree-of-interest negative-interest)
                             (max (query-strength query) (maximum-degree-of-interest negative-interest)))
                    (setf (interest-priority negative-interest) (maximum-degree-of-interest negative-interest))
                    (readopt-interest negative-interest nil)
                    (setf (link-interest link) negative-interest)
                    (push link (right-links negative-interest))
                    (push link *interest-links*)
                    (when (and *display?* *graphics-on* *graph-interests*)
                         (draw-interest negative-interest (interest-position negative-interest *og*) *og*))
                    (let ((Q (interest-queue-node negative-interest)))
                       (when Q
                            (setf (degree-of-preference Q)
                                     (maximum
                                       (list (degree-of-preference Q)
                                               (interest-preference
                                                 (query-strength query)
                                                 (sequent-complexity sequent)))))
                            (setf *inference-queue*
                                     (ordered-insert Q (remove Q *inference-queue*)
                                                                 #'i-preferred)))))
                   (t
                     (setf negative-interest
                              (make-interest
                                :interest-number (incf *interest-number*)
                                :interest-sequent (list (sequent-supposition sequent) (neg formula))
                                :interest-formula (neg formula)
                                :interest-supposition nil
                                :right-links (list link)
                                :degree-of-interest (query-strength query)
                                :maximum-degree-of-interest (query-strength query)
                                :interest-priority (query-strength query)
                                :deductive-interest (deductive-query query)))
                     (store-interest negative-interest)
                     (when *display?* (display-interest negative-interest))
                     (when *log-on* (push negative-interest *reasoning-log*))
                     (when (and *display?* *graphics-on* *graph-interests*) (draw-i negative-interest *og*))
                     (setf (link-interest link) negative-interest)
                     (push link *interest-links*)
                     (apply-degenerate-backwards-reasons negative-interest priority (1+ depth))
                     (reason-backwards-from negative-interest priority (1+ depth))
                     (form-epistemic-desires-for negative-interest)))
       (setf (negative-query-interest query) negative-interest)
       (dolist (cl (corresponding-c-lists (interest-i-list negative-interest)))
            (let ((conclusion
                     (find-if
                       #'(lambda (c)
                             (and (null (node-supposition c))
                                       (>= (compute-maximal-degree-of-support c)
                                              (query-strength query))))
                       (c-list-nodes  (mem1 cl)))))
              (when (and conclusion (not (member conclusion (supporting-nodes link))))
                              (push conclusion (supporting-nodes link))
                              (record-query-answers link))))
       (when (not (member query *permanent-ultimate-epistemic-interests*))
            (push #'(lambda (C)
                               (when (deductive-node C)
                                    (cancel-interest-in (query-interest query) 0)
                                    (cancel-interest-in (negative-query-interest query) 0)))
                        (positive-query-instructions query)))
       ))

(defunction reason-backwards-from-simple-query (query priority depth)
    ; (when (equal query (query 3)) (setf q query p priority d depth) (break))
    (when *trace* (indent depth) (princ "REASON-BACKWARDS-FROM-QUERY") (terpri))
    (let* ((formula (query-formula query))
              (sequent (list nil formula))
              (link
                (make-interest-link
                  :link-number (incf *link-number*)
                  :resultant-interest query
                  :link-strength (query-strength query)
                  :link-rule :answer))
              (interest
                (let ((interests (interests-for formula nil)))
                  (when interests
                       (find-if #'(lambda (i)
                                         (and (null (interest-supposition i))
                                                  (eq (deductive-interest i) (deductive-query query))))
                                   interests)))))
      (cond (interest
                  (setf (degree-of-interest interest)
                           (min (query-strength query) (degree-of-interest interest)))
                  (setf (maximum-degree-of-interest interest)
                           (max (query-strength query) (maximum-degree-of-interest interest)))
                  (setf (interest-priority interest) (maximum-degree-of-interest interest))
                  (readopt-interest interest nil)
                  (setf (link-interest link) interest)
                  (push link (right-links interest))
                  (push link *interest-links*)
                  (when (and *display?* *graphics-on* *graph-interests*)
                       (draw-interest interest (interest-position interest *og*) *og*))
                  (let ((Q (interest-queue-node interest)))
                    (when Q
                         (setf (degree-of-preference Q)
                                  (maximum
                                    (list (degree-of-preference Q)
                                           (interest-preference
                                             (query-strength query)
                                             (sequent-complexity sequent)))))
                         (setf *inference-queue*
                                  (ordered-insert Q (remove Q *inference-queue*)
                                                            #'i-preferred)))))
                (t
                  (setf interest
                           (make-interest
                             :interest-number (incf *interest-number*)
                             :interest-sequent sequent
                             :interest-formula formula
                             :interest-supposition nil
                             :right-links (list link)
                             :degree-of-interest (query-strength query)
                             :maximum-degree-of-interest (query-strength query)
                             :interest-priority (query-strength query)
                             :deductive-interest (deductive-query query)))
                  (store-interest interest)
                  (when *display?* (display-interest interest))
                  (when *log-on* (push interest *reasoning-log*))
                  (when (and *display?* *graphics-on* *graph-interests*) (draw-i interest *og*))
                  (setf (link-interest link) interest)
                  (push link *interest-links*)
                  (apply-degenerate-backwards-reasons interest priority (1+ depth))
                  (reason-backwards-from interest priority (1+ depth))
                  (form-epistemic-desires-for interest)))
      (setf (query-interest query) interest)
      (dolist (cl (corresponding-c-lists (interest-i-list interest)))
          (let ((conclusion
                    (find-if
                      #'(lambda (c)
                            (and (null (node-supposition c))
                                     (>= (compute-maximal-degree-of-support c)
                                            (query-strength query))))
                      (c-list-nodes  (mem1 cl)))))
            (when (and conclusion (not (member conclusion (supporting-nodes link))))
                 (push conclusion (supporting-nodes link))
                 (record-query-answers link))))))

(defunction ?-positive-instruction (query)
    #'(lambda (C)
          (when (deductive-node C)
               (cancel-interest-in (query-interest query) 0))))

(defunction reason-backwards-from-?-query (query priority depth)
    ; (when (equal query (query 3)) (setf q query p priority d depth) (break))
    ;; (step (reason-backwards-from-?-query q p d))
    (when *trace* (indent depth) (princ "REASON-BACKWARDS-FROM-QUERY") (terpri))
    (let ((p (query-formula query)))
       (multiple-value-bind
            (formula ?-vars) (?-matrix p)
            (let ((vars nil))
               (dolist (v ?-vars)
                   (let ((var (make-interest-variable)))
                      (setf formula (subst var v formula))
                      (push var vars)))
               (let* ((sequent (list nil formula))
                         (link
                           (make-interest-link
                             :link-number (incf *link-number*)
                             :resultant-interest query
                      :link-strength (query-strength query)
                             :link-rule :answer))
                         (interest
                           (make-interest
                             :interest-number (incf *interest-number*)
                             :interest-sequent sequent
                             :interest-formula formula
                             :interest-variables vars
                             :right-links (list link)
                             :degree-of-interest (query-strength query)
                             :maximum-degree-of-interest (query-strength query)
                             :interest-priority (query-strength query)
                             :discharge-condition
                             (if (?-constraint query) (funcall (?-constraint query) vars))
                             :deductive-interest (deductive-query query))))
                  (store-interest interest)
                  (when *display?* (display-interest interest))
                  (when *log-on* (push interest *reasoning-log*))
                  (when (and *display?* *graphics-on* *graph-interests*) (draw-i interest *og*))
                  (setf (link-interest link) interest)
                  (push link *interest-links*)
                  (apply-degenerate-backwards-reasons interest priority (1+ depth))
                  (reason-backwards-from interest priority (1+ depth))
                  (form-epistemic-desires-for interest)
                  (setf (query-interest query) interest)
                  (dolist (cl (corresponding-c-lists (interest-i-list interest)))
                      (let ((conclusion
                                (find-if
                                  #'(lambda (c)
                                        (and (null (node-supposition c))
                                                  (>= (compute-maximal-degree-of-support c)
                                                         (query-strength query))))
                                  (c-list-nodes  (mem1 cl)))))
                         (when (and conclusion (not (member conclusion (supporting-nodes link))))
                              (push conclusion (supporting-nodes link))
                              (record-query-answers link))))
                  (when (not (member query *permanent-ultimate-epistemic-interests*))
                       (pushnew (?-positive-instruction query) (positive-query-instructions query)))
                  )))))

#| Carrying along the priority of the inference-queue node from which
backwards reasoning proceeds simplifies the computation of interest-priorities in
discharge-link. |#
(defunction reason-backwards-from (interest priority depth)
    ; (when (equal interest (interest 1)) (setf i interest p priority d depth) (break))
    ;; (step (reason-backwards-from i p d))
    (when *trace* (indent depth) (princ "REASON-BACKWARDS-FROM: ") (princ interest) (terpri))
    (apply-backwards-reasons interest priority depth)
    (when (and *use-reductio* (not (cancelled-interest interest)))
         (make-reductio-supposition interest depth)
         (dolist (dr (direct-reductio-interest interest))
             (let ((node (car dr))
                     (match (cdr dr)))
                (discharge-retrospective-reductios node match interest 1)))
         (discharge-fortuitous-reductio-interests interest depth))
    (dolist (rule *auxiliary-backwards-rules*)
        (funcall rule interest)))

(defunction apply-backwards-reasons (interest priority depth)
   ; (when (eq interest (interest 9)) (setf i interest p priority d depth) (break))
    ; (setf i interest p priority d depth)
    ;; (step (apply-backwards-reasons i p d))
    (when *trace* (indent depth) (princ "APPLY-BACKWARDS-REASONS ") (princ interest) (terpri))
    (catch 'apply-backwards-reasons
        (let* ((i-list (interest-i-list interest))
                  (d-node (i-list-d-node i-list)))
           (reason-backwards-from-dominant-reason-nodes interest priority (1+ depth) d-node)))
    (setf (last-processed-degree-of-interest interest) (degree-of-interest interest)))

(defunction reason-backwards-from-dominant-reason-nodes (interest priority depth d-node)
    (when *trace* (indent depth) (princ "REASON-BACKWARDS-FROM-DOMINANT-REASON-NODES ")
                (princ interest) (princ " and ") (princ d-node) (terpri))
    (reason-backwards-from-reason-node interest priority (1+ depth) d-node)
    (let ((pn (parent-d-node d-node)))
       (when pn (reason-backwards-from-dominant-reason-nodes interest priority (1+ depth) pn))))

(defunction reason-backwards-from-reason-node (interest priority depth d-node)
   ; (when (eq interest (interest 5)) (setf i interest p priority d depth dn d-node) (break))
    ;; (step (reason-backwards-from-reason-node i p d dn))
    (when *trace* (indent depth) (princ "REASON-BACKWARDS-FROM-REASON-NODE ")
                (princ interest) (princ " and ") (princ d-node) (terpri))
    (dolist (reason (d-node-backwards-reasons d-node))
        (when (cancelled-interest interest) (throw 'apply-backwards-reasons nil))
        (when (or (not (deductive-interest interest)) (not (defeasible-rule reason)))
             (let ((strength (reason-strength reason)))
               (when
                    (or (not (numberp strength))
                          (and (>= strength (degree-of-interest interest))
                                   (or (null (last-processed-degree-of-interest interest))
                                         (< strength (last-processed-degree-of-interest interest)))))
                    (let ((reason-function (reason-function reason)))
                      (cond
                        (reason-function (funcall (reason-function reason) interest (1+ depth) priority))
                        (t (reason-substantively-from-backwards-reason reason interest (1+ depth) priority)))))))))

(defunction apply-degenerate-backwards-reasons (interest priority depth)
   ; (when (eq interest (interest 97)) (setf i interest p priority d depth) (break))
    ;; (step (apply-degenerate-backwards-reasons i p d))
    (when *trace* (indent depth) (princ "APPLY-DEGENERATE-BACKWARDS-REASONS ") (princ interest) (terpri))
    (catch 'apply-backwards-reasons
        (let* ((i-list (interest-i-list interest))
                  (d-node (i-list-d-node i-list)))
           (reason-degenerately-backwards-from-dominant-reason-nodes interest priority (1+ depth) d-node))))

(defunction reason-degenerately-backwards-from-dominant-reason-nodes (interest priority depth d-node)
    (when *trace* (indent depth) (princ "REASON-DEGENERATELY-BACKWARDS-FROM-DOMINANT-REASON-NODES ")
                (princ interest) (princ " and ") (princ d-node) (terpri))
    (reason-degenerately-backwards-from-reason-node interest priority (1+ depth) d-node)
    (let ((pn (parent-d-node d-node)))
       (when pn (reason-degenerately-backwards-from-dominant-reason-nodes interest priority (1+ depth) pn))))

(defunction reason-degenerately-backwards-from-reason-node (interest priority depth d-node)
   ; (when (and (eq interest (interest 24)) (eq d-node (d-node 27))) (setf i interest p priority d depth dn d-node) (break))
    ;; (step (reason-degenerately-backwards-from-reason-node i p d dn))
    (when *trace* (indent depth) (princ "REASON-DEGENERATELY-BACKWARDS-FROM-REASON-NODE ")
                (princ interest) (princ " and ") (princ d-node) (terpri))
    (dolist (reason (d-node-degenerate-backwards-reasons d-node))
        (when (cancelled-interest interest) (throw 'apply-backwards-reasons nil))
        (when (or (not (deductive-interest interest)) (not (defeasible-rule reason)))
             (let ((strength (reason-strength reason)))
               (when
                    (or (not (numberp strength))
                          (and (>= strength (degree-of-interest interest))
                                   (or (null (last-processed-degree-of-interest interest))
                                         (< strength (last-processed-degree-of-interest interest)))))
                    (let ((reason-function (reason-function reason)))
                      (cond
                        (reason-function (funcall (reason-function reason) interest (1+ depth) priority))
                        (t (reason-substantively-from-backwards-reason reason interest (1+ depth) priority)))))))))

(defunction reason-substantively-from-backwards-reason (reason interest depth priority)
    ; (when (eq interest (interest 133)) (setf r reason n interest d depth p priority) (break))
    ;; (step (reason-substantively-from-backwards-reason r n d p))
    (when *trace* (indent depth) (princ "REASON-SUBSTANTIVELY-FROM-BACKWARDS-REASON ")
                (princ reason) (terpri))
    (multiple-value-bind
         (binding instantiation)
         (funcall (conclusions-binding-function reason)
                      (interest-formula interest) (interest-variables interest))
         (when (and instantiation (funcall* (reason-condition reason) binding))
              (let ((supposition (match-sublis instantiation (interest-supposition interest))))
                (cond
                  ((forwards-premises reason)
                    (construct-interest-scheme
                      reason nil interest binding nil
                 (forwards-premises reason) nil (1+ depth) priority supposition))
                  (t (make-backwards-inference
                        reason binding interest (1+ depth) priority nil nil nil supposition)))))))

(defunction applied-forwards-reason-strength (reason binding basis)
    (let ((strength
              (cond ((keywordp reason) 1.0)
                        ((numberp (reason-strength reason)) (reason-strength reason))
                        (t (funcall (reason-strength reason) binding basis)))))
      (if (and (not (keywordp reason)) (temporal? reason))
        (* strength (minimum (mapcar #'compute-undefeated-degree-of-support basis)))
        (minimum (cons strength (mapcar #'compute-undefeated-degree-of-support basis))))))

#| When an interest is retrieved from the inference-queue, check to see the value of
reductio-trigger for its i-list.  If it is T, make a reductio-supposition for the negation
of the interest-formula,  and reset reductio-trigger to NIL. |#
(defunction MAKE-REDUCTIO-SUPPOSITION (interest depth)
    ; (when (equal interest (interest 9)) (break))
    ;; (step (make-reductio-supposition (interest 9) 0))
    (when
         (not (cancelled-interest interest))
         (let ((q (interest-formula interest))
                 (X (interest-supposition interest))
                 (i-list (interest-i-list interest)))
           (when (not (mem q X))
                (cond ((reductio-trigger i-list)
                            (setf (reductio-trigger i-list) nil)
                            (multiple-value-bind
                                 (P c-vars)
                                 (convert-interest-variables (neg q) (interest-variables interest))
                                 (let ((sup (find-if #'(lambda (N) (equal (node-formula N) P))
                                                             *reductio-supposition-nodes*)))
                                   (when (null sup)
                                        (setf sup
                                                 (find-if
                                                   #'(lambda (R)
                                                         (let* ((vars (node-variables R))
                                                                   (R-formula (node-formula R))
                                                                   (m (match R-formula P vars)))
                                                           (and m (equal (match-sublis m R-formula) P))))
                                                   *reductio-supposition-nodes*))
                                        (when (null sup)
                                             (setf sup
                                                      (find-if
                                                        #'(lambda (R)
                                                              (let ((vars (node-variables R))
                                                                      (R-formula (node-formula R)))
                                                                (match R-formula P vars)))
                                                        *non-reductio-supposition-nodes*))))
                                   (cond (sup
                                               (incf (readopted-supposition sup))
                                               (setf (node-justification sup) :reductio-supposition)
                                               (push interest (generating-interests sup))
                                               (convert-non-reductio-sup sup))
                                             (t (make-new-reductio-supposition interest X i-list P c-vars depth))))))
                          (t (augment-inherited-non-reductio-suppositions interest)))))))

(defunction augment-inherited-non-reductio-suppositions (interest &optional nodes interests)
    (dolist (node (generating-nodes interest))
        (when (not (member node nodes))
             (push node nodes)
             (dolist (R (non-reductio-supposition node))
                 (pushnew (cdr R) *inherited-non-reductio-suppositions*))
             (dolist (in (generating-interests node))
                 (when (and (not (member in interests))
                                       (not (direct-reductio-interest interest)))
                      (push in interests)
                      (dolist (R (non-reductio-interest-supposition in nodes interests))
                          (pushnew R *inherited-non-reductio-suppositions*))))))
    (dolist (L (right-links interest))
        (let ((in (resultant-interest L)))
           (when (and (not (query-p in))
                                 (not (member in interests)))
                (push in interests)
                (dolist (R (non-reductio-interest-supposition in nodes interests))
                    (pushnew R *inherited-non-reductio-suppositions*))))))

(defunction non-reductio-interest-supposition (interest &optional nodes interests)
    (let ((sup nil))
       (dolist (node (generating-nodes interest))
           (when (not (member node nodes))
                (push node nodes)
                (dolist (R (non-reductio-supposition node))
                    (pushnew (cdr R) sup))))
       (dolist (dr (direct-reductio-interest interest))
         (let ((node (car dr)))
               (when (not (member node nodes))
                    (push node nodes)
                    (dolist (R (non-reductio-supposition node))
                         (pushnew (cdr R) sup)))))
       (dolist (L (right-links interest))
           (let ((in (resultant-interest L)))
              (when (and (not (query-p in))
                                    (not (member in interests)))
                   (push in interests)
                   (setf sup (union= sup (non-reductio-interest-supposition in nodes interests))))))
       sup))

(defunction make-new-reductio-supposition (interest X i-list P c-vars depth)
    (let ((c-list (c-list-for P)))
       (cond
         ((or (null c-list)
                 (not (some #'(lambda (c) (subsetp= (node-supposition c) X))
                                      (c-list-nodes c-list))))
           (augment-inherited-non-reductio-suppositions interest)
           (let* ((new-sup (list P))
                     (sequent (list new-sup P))
                     (N (make-inference-node
                            :inference-number (incf *inference-number*)
                            :node-sequent sequent
                            :node-formula P
                            :node-supposition new-sup
                            :node-kind :inference
                            :nearest-defeasible-ancestors (list nil)
                            :node-justification :reductio-supposition
                            :undefeated-degree-of-support 1.0
                            :maximal-degree-of-support 1.0
                            :deductive-only t
                            :discounted-node-strength
                            (* *reductio-discount* (interest-priority interest))
                            :generating-interests (list interest)
                            :node-variables c-vars
                            :node-supposition-variables c-vars
                            )))
              (when *trace* (indent depth)
                           (princ "DRAW CONCLUSION: ")
                           (princ N) (terpri))
              (incf *unused-suppositions*)
              (setf (i-list-reductio-supposition i-list) N)
              (setf (reductio-ancestors N) (list (cons P N)))
              (push N *inference-graph*)
              (store-inference-node-with-c-list N P c-list)
              (when (not *deductive-only*)
                   (setf (node-UDs *assignment-tree*) (cons (cons N 1.0) (node-UDs *assignment-tree*)))
                   (setf (node-MPUDs *assignment-tree*) (cons (cons N 1.0) (node-MPUDs *assignment-tree*))))
              (if *log-on* (push N *reasoning-log*))
              (push N (generated-suppositions interest))
              (when *display?* (display-unsupported-node N))
              (queue-for-inference N)
              (when (and *display?* *graphics-on*) (when *graphics-pause* (pause-graphics))
                             (draw-n N *og* *nodes-displayed*) (push N *nodes-displayed*))
              (start-reductio-interests N (1+ depth) nil)
              ))
         (t (setf (reductio-trigger i-list) t)))))

#| When a non-reductio-supposition is readopted as a reductio-supposition, for all
of its inclusive-node-descendants that are deductive in it, it is moved from the
non-reductio-supposition to the list of reductio-ancestors.  For all of those altered
nodes that are not still on the inference-queue, we discharge-interest-in them and
reason-forwards-from them. |#
(defunction convert-non-reductio-sup (sup)
    (when *display?* (princ "Converting node ") (princ (inference-number sup))
                  (princ " to a reductio supposition") (terpri))
    (pull sup *non-reductio-supposition-nodes*)
    (when (not (member sup *reductio-supposition-nodes*))
         (setf (node-justification sup) :reductio-supposition)
         (if (null *reductio-supposition-nodes*) (start-reductio-interests sup 0 nil)
              (push sup *reductio-supposition-nodes*))
         (recompute-reductio-ancestors sup sup)))

(defunction recompute-reductio-ancestors (node sup)
    (let ((assoc (rassoc sup (non-reductio-supposition node))))
      (when assoc
           (pull assoc (non-reductio-supposition node))
           (push assoc (reductio-ancestors node))
           (discharge-interest-in node (corresponding-i-lists (node-c-list node)) 0 t 1 nil nil :reductio-only t)
           (dolist (L (consequent-links node))
               (recompute-reductio-ancestors (support-link-target L) sup)))))

#| If the interest is readopted as an interest in a defeater, defeated-nodes is the list of
nodes for which it is a defeater.  When this is called by DISCHARGE-LINK, link is the
link being discharged.  |#
(defunction readopt-interest (interest defeated-links)
    (when *display?*
         (princ "                                   Readopting interest in:") (terpri)
         (display-interest interest)
         (when defeated-links
              (princ
                "                                        Of interest as defeater for support-link ")
              (princ (support-link-number (mem1 defeated-links))) (terpri)(terpri)))
    )

(defunction discharge-interest-scheme (interest-scheme d-node priority depth)
   ; (when (eq interest-scheme (interest-scheme 5)) (setf is interest-scheme dn d-node p priority d depth) (break))
    ;; (step (discharge-interest-scheme is dn p d))
    (when *trace* (indent depth) (princ "DISCHARGE-INTEREST-SCHEME ")
                (princ (is-number interest-scheme)) (terpri))
    (dolist (c-list (d-node-c-lists d-node))
        (dolist (node (c-list-processed-nodes c-list))
            (reason-from-interest-scheme node priority (1+ depth) interest-scheme)))
    (dolist (test (discrimination-tests d-node))
        (discharge-interest-scheme interest-scheme (cdr test) priority (1+ depth))))

(defunction reason-from-interest-scheme (node priority depth is)
   ; (when (and (eq node (node 56)) (eq is (interest-scheme 20))) (setf n node p priority d depth i is) (break))
    ;; (step (reason-from-interest-scheme n p d i))
    (when *trace* (indent depth) (princ "REASON-FROM-INTEREST-SCHEME ")
                (princ (is-number is)) (terpri))
    (cond
      ((is-instance-function is) (funcall (is-instance-function is) node (1+ depth) priority))
      (t
        (let* ((vars (if node (node-variables node)))
                  (formula (if node (node-formula node))))
          (multiple-value-bind
               (binding0 instantiation0)
               (funcall (fp-binding-function (is-premise is)) formula vars)
               (when
                    (and instantiation0 (equal (fp-kind (is-premise is)) (node-kind node)))
                    (let ((unifier
                              (binding-unifier
                                binding0 (is-binding is)
                                (is-used-premise-variables is) vars (is-used-variables is))))
                      (when unifier
                           (let ((unifiers
                                     (appropriately-related-supposition
                                       node (is-target-interest is)
                                       (if (reason-discharge (is-reason is))
                                         (cons (remove-double-negation
                                                    (match-sublis (is-binding is) (reason-discharge (is-reason is))))
                                                   (is-supposition is))
                                         (is-supposition is))
                                       (is-supposition-variables is) unifier)))
                             (dolist (u unifiers)
                                 (let ((u* (merge-unifiers* unifier u)))
                                   (when (cancelled-interest (is-target-interest is))
                                        (return-from reason-from-interest-scheme))
                                   (when
                                        (constrained-assignment
                                          u* (node-supposition-variables node)
                                          (interest-variables (is-target-interest is)))
                                        (let ((binding (rectify-binding binding0 u* is))
                                                (spec (premise-node-specifier (is-premise is))))
                                          (when spec (push (cons spec node) binding))
                                          (when (funcall** (fp-condition (is-premise is)) node binding)
                                               (let
                                                 ((instantiations
                                                    (if (fp-clue? (is-premise is))
                                                      (mapcar #'(lambda (in) (merge-matches* (mem2 u*) in))
                                                                     (is-instantiations is))
                                                      (cons (merge-matches* (mem1 u*) instantiation0)
                                                                (mapcar #'(lambda (in) (merge-matches* (mem2 u*) in))
                                                                               (is-instantiations is)))))
                                                   (supposition (match-sublis (mem2 u) (is-supposition is))))
                                                 (cond
                                                   ((is-remaining-premises is)
                                                     (construct-interest-scheme
                                                       (is-reason is) node (is-target-interest is) binding
                                                       instantiations (is-remaining-premises is)
                                                       is (1+ depth) priority supposition))
                                                   (t
                                                     (make-backwards-inference
                                                       (is-reason is) binding (is-target-interest is) (1+ depth) priority
                                                       (if (fp-clue? (is-premise is)) (is-basis is) (cons node (is-basis is)))
                                                       (if (fp-clue? (is-premise is)) (cons node (is-clues is)) (is-clues is))
                                                       instantiations supposition (is-generating-node is)))))
                                               ))))))))))))))

(defunction remove-double-negation (P)
    (cond
      ((listp P)
        (cond ((and (negationp P) (negationp (negand P))) (negand (negand P)))
                  ((or (member (car P) *operators*)
                         (member (car P) '(& v <-> ->))
                         (and (listp (car P))
                                  (or (eq (caar P) 'all)
                                        (eq (caar P) 'some))))
                    (cons (car P) (mapcar #'remove-double-negation (cdr P))))
                  (t P)))
      (t P)))

(defunction construct-initial-interest-link
    (supporting-nodes instantiations reason resultant-interest depth priority binding supposition
                          &key generating-node remaining-premises clues new-variables)
   ; (when (eq *cycle* 98) (setf sn supporting-nodes in instantiations r reason ri resultant-interest d depth p priority b binding s supposition gn generating-node rp remaining-premises cl clues nv new-variables) (break))
    ; (setf sn supporting-nodes in instantiations r reason ri resultant-interest d depth p priority b binding s supposition gn generating-node rp remaining-premises cl clues nv new-variables)
    ;; (step (construct-initial-interest-link sn in r ri d p b s :generating-node gn :remaining-premises rp :clues cl :new-variables nv))
    (when *trace* (indent depth) (princ "CONSTRUCT-INITIAL-INTEREST-LINK for interest ")
                (princ (interest-number resultant-interest)) (princ " using ") (princ reason) (terpri))
    (when (null remaining-premises) (setf remaining-premises (backwards-premises reason)))
    (cond
      ((and (backwards-premise-p (car remaining-premises))
                (listp (bp-formula (car remaining-premises)))
                (equal (car (bp-formula (car remaining-premises))) 'define))
        (let* ((var (mem2 (bp-formula (car remaining-premises))))
                  (def-instantiator (bp-instantiator (car remaining-premises))))
          (multiple-value-bind
               (new-binding new-vars)
               (set-def-binding def-instantiator var binding)
               (when (funcall** (bp-condition1 (car remaining-premises)) nil new-binding)
                    (cond ((cdr remaining-premises)
                                (construct-initial-interest-link
                                  supporting-nodes instantiations reason resultant-interest depth priority new-binding
                                  supposition :generating-node generating-node :remaining-premises (cdr remaining-premises)
                                  :clues clues :new-variables (append new-vars new-variables)))
                              ((conclusions-function reason)
                                (dolist (P (funcall (conclusions-function reason) new-binding))
                                    (draw-conclusion
                                      (car P) supporting-nodes
                                      reason instantiations (discount-factor reason) depth nil
                                      (defeasible-rule reason) :binding new-binding
                                      :interest resultant-interest :clues clues)))
                              (t (draw-conclusion
                                    (interest-formula resultant-interest) supporting-nodes
                                    reason instantiations (discount-factor reason) depth nil
                                    (defeasible-rule reason) :binding new-binding
                                    :interest resultant-interest :clues clues)))))))
      (t
        (when (null resultant-interest)
             (multiple-value-bind
                  (formulas vars)
                  (funcall (conclusions-function reason) binding)
                  (multiple-value-bind
                       (i-list match)
                       (i-list-for (caar formulas) vars)
                       (let ((sup (if i-list (match-sublis match supposition) supposition)))
                         (setf resultant-interest
                             (if i-list
                               (find-if #'(lambda (i) (== (interest-supposition i) sup))
                                           (i-list-interests i-list))))))))
        (let* ((premise0 (car remaining-premises))
                  (premise
                    (if (backwards-premise-p premise0) premise0
                         (funcall premise0
                                      (defeater-binding resultant-interest) binding)))
                  (discharge (if (and (backwards-reason-p reason) (reason-discharge reason))
                                      (remove-double-negation
                                        (match-sublis binding (reason-discharge reason))))))
          (multiple-value-bind
               (generating-node new?)
               (if (and discharge (null supporting-nodes))
                 (queue-supposition
                   discharge (list discharge)
                   (subset #'(lambda (v) (occur v discharge)) (interest-variables resultant-interest))
                   (discount-factor reason) resultant-interest)
                 generating-node)
               (when (or generating-node new? (null discharge) supporting-nodes)
                    (multiple-value-bind
                         (interest-formula new-vars new-binding)
                         (funcall (bp-instantiator premise) binding)
                         (setf interest-formula (remove-double-negation interest-formula))
                         (when (or (not (equal interest-formula (interest-formula resultant-interest)))
                                           (not (mem discharge supposition)))
                              (let ((link
                                        (make-interest-link
                                          :link-number (incf *link-number*)
                                          :resultant-interest resultant-interest
                                          :link-interest-formula interest-formula
                                          :link-interest-condition (bp-condition2 premise)
                                          :link-rule reason
                                          :link-premise premise
                                          :remaining-premises (cdr remaining-premises)
                                          :supporting-nodes supporting-nodes
                                          :link-clues clues
                                          :link-instantiations instantiations
                                          :link-supposition (if (and discharge (not (mem discharge supposition)))
                                                                       (cons discharge supposition) supposition)
                                          :link-strength
                                          (cond ((eq reason :answer)
                                                      (maximum-degree-of-interest resultant-interest))
                                                    ((numberp (reason-strength reason)) (reason-strength reason))
                                                    (t (maximum-degree-of-interest resultant-interest)))
                                          :link-generating-node generating-node
                                          :link-binding new-binding
                                          )))
                                (push link *interest-links*)
                                (push link (left-links resultant-interest))
                                (compute-link-interest
                                  link (bp-condition1 premise) (bp-condition2 premise)
                                  (degree-of-interest resultant-interest)
                                  (maximum-degree-of-interest resultant-interest) depth priority
                                  (append new-vars new-variables) (bp-text-condition premise))
                                (discharge-link
                                  link (1+ depth) (degree-of-interest resultant-interest)
                                  (interest-priority (link-interest link)) nil)
                                (apply-degenerate-backwards-reasons
                                  (link-interest link) (interest-priority (link-interest link)) (1+ depth))
                                 link)))))))))

(defunction construct-interest-link
    (link0 node instantiations binding remaining-premises supposition degree
              max-degree depth priority interests &key new-variables)
    ; (when (eq *cycle* 518) (setf l link0 n node i instantiations b binding rp remaining-premises s supposition d degree m max-degree de depth p priority in interests) (break))
     ;(setf l link0 n node i instantiations b binding rp remaining-premises s supposition d degree m max-degree de depth p priority in interests)
    ;; (step (construct-interest-link l n i b rp s d m de p in))
    (when *trace* (indent depth) (princ "CONSTRUCT-INTEREST-LINK for interest ")
                (princ (interest-number (resultant-interest link0))) (princ " using ") (princ (link-rule link0))
                (princ " and nodes ") (princ (mapcar #'inference-number (supporting-nodes link0)))
                (terpri))
    (cond
      ((and (backwards-premise-p (car remaining-premises))
                (listp (bp-formula (car remaining-premises)))
                (equal (car (bp-formula (car remaining-premises))) 'define))
        (let* ((var (mem2 (bp-formula (car remaining-premises))))
                  (def-instantiator (bp-instantiator (car remaining-premises))))
          (multiple-value-bind
               (new-binding new-vars match)
               (set-def-binding def-instantiator var binding)
               (when (funcall** (bp-condition1 (car remaining-premises)) nil new-binding)
                    (cond ((cdr remaining-premises)
                                (construct-interest-link
                                  link0 node instantiations new-binding (cdr remaining-premises)
                                  supposition degree max-degree depth priority interests
                                  :new-variables (append new-vars new-variables)))
                              ((funcall+
                                 (discharge-condition (resultant-interest link0)) nil (list t t)
                                 (subst (cdr match) (car match)
                                             (link-binding (car (right-links (resultant-interest link0))))))
                                (cond
                                  ((conclusions-function (link-rule link0))
                                    (dolist (P (funcall (conclusions-function (link-rule link0)) new-binding))
                                        (draw-conclusion
                                          (car P) (cons node (supporting-nodes link0)) (link-rule link0) instantiations
                                          (discount-factor (link-rule link0)) depth nil (cdr P) :binding new-binding :interest
                                          (resultant-interest link0) :link link0 :clues (link-clues link0))))
                                  (t (draw-conclusion
                                        (interest-formula (resultant-interest link0)) (cons node (supporting-nodes link0))
                                        (link-rule link0) instantiations (discount-factor (link-rule link0)) depth nil
                                        (defeasible-rule (link-rule link0)) :binding new-binding
                                        :interest (resultant-interest link0) :link link0 :clues (link-clues link0)))
                                  )))))))
      (t
        (let* ((premise0 (car remaining-premises))
                  (premise
                    (if (backwards-premise-p premise0) premise0
                         (funcall premise0 nil binding))))
          (multiple-value-bind
               (interest-formula new-vars new-binding)
               (funcall (bp-instantiator premise) binding)
               (let ((link
                         (make-interest-link
                           :link-number (incf *link-number*)
                           :resultant-interest (resultant-interest link0)
                           :link-interest-formula (remove-double-negation interest-formula)
                           :link-interest-condition (bp-condition2 premise)
                           :link-rule (link-rule link0)
                           :link-premise premise
                           :remaining-premises (cdr remaining-premises)
                           :supporting-nodes
                           (if (bp-clue? (link-premise link0))
                             (supporting-nodes link0) (cons node (supporting-nodes link0)))
                           :link-clues
                           (if (bp-clue? (link-premise link0))
                             (cons node (link-clues link0)) (link-clues link0))
                           :link-instantiations instantiations
                           :link-supposition supposition
                           :link-strength
                           (cond ((eq (link-rule link0) :answer)
                                       (query-strength (resultant-interest link0)))
                                     ((numberp (reason-strength (link-rule link0))) (reason-strength (link-rule link0)))
                                     (t (maximum-degree-of-interest (resultant-interest link0))))
                           :link-generating-node (link-generating-node link0)
                           :link-binding new-binding
                           :generating-link link0
                           )))
                 (push link *interest-links*)
                 (when (not (eq (link-rule link0) :answer)) (push link (left-links (resultant-interest link0))))
                 (compute-link-interest
                   link (bp-condition1 premise) (bp-condition2 premise)
                   degree max-degree depth priority (append new-vars new-variables)
                   (bp-text-condition premise))
                 (discharge-link link (1+ depth) (degree-of-interest (resultant-interest link0)) priority interests)
                 (apply-degenerate-backwards-reasons (link-interest link) priority (1+ depth))
                 ))))))

(defunction link-interests (link)
    (cond
      ((null (generating-link link)) (list (link-interest link)))
      (t (cons (link-interest link) (link-interests (generating-link link))))))

(defunction display-instantiated-premise (ip)
    (terpri)
    (princ "  Constructing instantiated-premise #") (princ (ip-number ip)) (terpri)
    (princ "  next premise:  ")
    (prinp (match-sublis (ip-binding ip) (fp-formula (ip-premise ip))))
    (terpri) (princ "  by ")
    (princ (ip-reason ip)) (princ ",  basis = ")
    (print-list (mapcar #'inference-number (ip-basis ip)))
    (princ " with clues ") (print-list (mapcar #'inference-number (ip-clues ip)) nil)
    (terpri) (terpri))

(defunction list-interest-schemes (&optional d-node)
    (when (null d-node) (setf d-node (d-node 1)))
    (append (d-node-interest-schemes d-node)
                   (unionmapcar #'(lambda (d) (list-interest-schemes (cdr d)))
                                           (discrimination-tests d-node))))

(defunction is (n)
    (find-if #'(lambda (x) (equal (ip-number x) n)) (list-interest-schemes)))

(defunction list-instantiated-premises (&optional d-node)
    (when (null d-node) (setf d-node (d-node 1)))
    (append (d-node-forwards-reasons d-node)
                   (unionmapcar #'(lambda (d) (list-instantiated-premises (cdr d)))
                                           (discrimination-tests d-node))))

(defunction ip (n)
    (find-if #'(lambda (x) (equal (ip-number x) n)) (list-instantiated-premises)))

(defunction analyze-interest-schemes ()
    (let ((schemes (list-interest-schemes))
            (reasons nil))
      (dolist (s schemes)
          (when (not (member (ip-reason s) *backwards-logical-reasons*))
               (pushnew (ip-reason s) reasons)))
      (dolist (R reasons)
          (princ "There are ")
          (princ (number-of schemes #'(lambda (x) (eq (ip-reason x) R))))
          (princ " interest-schemes employing the reason ")
          (princ R) (terpri))))

(defunction analyze-instantiated-premises ()
    (let ((schemes (list-instantiated-premises))
            (reasons nil))
      (dolist (s schemes)
          (when (not (member (ip-reason s) *forwards-logical-reasons*))
               (pushnew (ip-reason s) reasons)))
      (dolist (R reasons)
          (princ "There are ")
          (princ (number-of schemes #'(lambda (x) (eq (ip-reason x) R))))
          (princ " instantiated-premises employing the reason ")
          (princ R) (terpri))))

(defunction analyze-schemes ()
    (analyze-instantiated-premises)
    (analyze-interest-schemes))

#| new-vars are new variables introduced by the inference-rule, as in EG. |#
(defunction compute-link-interest
    (link condition1 condition2 degree max-degree depth priority &optional new-vars text-condition)
    (declare (ignore new-vars))
   ; (when (equal link (link 21)) (setf l link c1 condition1 c2 condition2 d degree md max-degree dp depth p priority nv new-vars) (break))
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
              ; (let ((i-depth (interest-depth (resultant-interest link))))
              ;   (setf (interest-depth interest) (1+ i-depth))
              ;   (setf (interest-priority interest) (* interest-priority (/  i-depth (1+ i-depth)))))

               (setf (interest-priority interest) interest-priority)
               ))
           (setf (link-interest link) interest)
          ; (dolist (p (decision-plans (resultant-interest link)))
          ;     (pushnew p (decision-plans interest)))
           )))

#| X and Y are sets of sequents, and every member of X subsumes some member
of Y. |#
(defunction subsumes-basis (X Y)
    (every
      #'(lambda (a)
            (some
              #'(lambda (b) (subsumes a b))
              Y))
      X))

;#|  This returns the list of two c-lists, one supporting the rebutting defeater and the
;other supporting the undercutting defeater.  It creates them if necessary.  |#
;(defunction defeaters-for (sequent basis)
;    (let* ((formula (sequent-formula sequent))
;              (base (mapcar #'sequent-formula basis))
;              (rebut (neg formula))
;              (undercut (make-@ (gen-conjunction base) formula))
;              (rebutting-c-list (c-list-for rebut))
;              (undercutting-c-list (c-list-for undercut)))
;       (when (null rebutting-c-list)
;            (setf rebutting-c-list
;                     (make-c-list
;                       :c-list-formula rebut
;                       :corresponding-i-lists (matching-i-lists-for rebut nil)))
;            (push (cons rebut rebutting-c-list) *conclusions*))
;       (when (null undercutting-c-list)
;            (setf undercutting-c-list
;                     (make-c-list
;                       :c-list-formula undercut
;                       :corresponding-i-lists (matching-i-lists-for undercut nil)))
;            (push (cons undercut undercutting-c-list) *conclusions*))
;       (list rebutting-c-list undercutting-c-list)))

(defunction interest-for (sequent vars condition &optional link)
    (multiple-value-bind
         (i-list match match*)
         (i-list-for (sequent-formula sequent) vars)
         (let*
           ((sup
              (if i-list (match-sublis match (sequent-supposition sequent)) (sequent-supposition sequent)))
             (interest
               (if i-list
                 (find-if
                   #'(lambda (i)
                         (and (or condition (null (discharge-condition i)))
                                  (funcall* condition i) (== (interest-supposition i) sup)
                                  (or (null link)
                                        (eq (deductive-interest i) (deductive-interest (resultant-interest link))))))
                             (i-list-interests i-list)))))
            (when (and (null interest) (not (eq match t))) (setf i-list nil))
            (values interest i-list match match*))))

#| The priority is the priority of the inference-queue node from which this link
is derived, if this value is known.  This simplifies the computation of the interest-priority
for the new interests produced by this operation.  degree is the degree of interest of
the resultant-interest. |#
(defunction DISCHARGE-LINK (link depth degree priority interests)
    ; (when (eq link (link 159)) (setf l link d depth dg degree p priority in interests) (break))
    ; (setf l link d depth dg degree p priority in interests)
    ;; (step (discharge-link l d dg p in))
    (when *trace* (indent depth) (princ "DISCHARGE-LINK: ") (princ link) (terpri))
    (let ((deductive-rule? (not (defeasible-rule (link-rule link))))
            (node-list nil)
            (interest (link-interest link))
            (reason (link-rule link))
            (condition (link-interest-condition link))
           ; (match (interest-match link))
            (match* (interest-reverse-match link))
            (spec (premise-node-specifier (link-premise link))))
      (block nodes
          (dolist  (cl (corresponding-c-lists (interest-i-list interest)))
              (let* ((c-list (car cl))
                        (unifier0 (mem2 cl))
                        (unifier
                          (match-sublis match* unifier0)))
                (dolist (node (c-list-nodes c-list))
                    (when (and (funcall+
                                          (discharge-condition interest) node unifier
                                          (if spec (cons (cons spec node) (link-binding link)) (link-binding link)))
                                        (or (not (deductive-only node)) deductive-rule?)
                                        (or (non-reductio-interest interest) (deductive-node node)))
                         (when (and (deductive-node node)
                                             (null condition)
                                             (eq (mem2 unifier) t)
                                             (subsetp= (match-sublis (mem1 unifier) (node-supposition node))
                                                               (link-supposition link)))
                              (setf node-list (list (cons node unifier)))
                              (setf (cancelling-node interest) node)
                              (return-from nodes))
                         (when (>= (compute-maximal-degree-of-support node) degree)
                              (push (cons node unifier) node-list))))))
          (re-queue-interest link priority (link-interest link) degree))
      (dolist (nl node-list)
          (let* ((node (car nl))
                    (unifier (cdr nl))
                    (unifiers
                      (appropriately-related-supposition
                        node (link-interest link) (link-supposition link) (interest-supposition-variables interest) unifier)))
            (when unifiers (setf (discharged-link link) t))
            (dolist (u unifiers)
                (let ((u* (merge-unifiers* unifier u)))
                  (when (cancelled-interest (link-interest link)) (return-from discharge-link))
                  (when
                       (constrained-assignment
                         u* (node-supposition-variables node) (interest-variables (link-interest link)))
                       (when *display?*
                            (princ "                                        ") (princ "Node #") (princ (inference-number node))
                            (princ " discharges interest #") (princ (interest-number interest)) (terpri) (terpri))
                       (pushnew node (discharging-nodes interest))
                      ; (setf u* (convert-unifier-variables u* (node-variables node)))
                       (let
                         ((binding
                            (mapcar
                              #'(lambda (assoc) (cons (car assoc) (match-sublis (mem2 u*) (cdr assoc))))
                              (if spec (cons (cons spec node) (link-binding link)) (link-binding link))))
                           (instantiations
                             (cons (mem1 u*)
                                       (mapcar #'(lambda (in) (merge-matches* in (mem2 u*))) (link-instantiations link))))
                           (supposition (match-sublis (mem2 u*) (link-supposition link))))
                         (cond
                           ((eq (link-rule link) :answer)
                             (push node (query-answers (resultant-interest link)))
                             (pushnew (resultant-interest link) (answered-queries node))
                             (when (deductive-node node)
                                  (when (and
                                               (every
                                                 #'(lambda (query)
                                                       (or (eq query (resultant-interest link))
                                                             (some #'deductive-node (query-answers query))))
                                                 *ultimate-epistemic-interests*)
                                               (not (some
                                                         #'(lambda (Q) (eq (item-kind Q) :query))
                                                         *inference-queue*)))
                                       (setf (undefeated-degree-of-support node) 1.0)
                                       (setf (answered? (resultant-interest link)) T)
                                       (let ((deductive-links nil)
                                               (deductive-nodes nil))
                                         (dolist (L *new-links*)
                                             (when (deductive-node (support-link-target L))
                                                  (push L deductive-links)
                                                  (push (support-link-target L) deductive-nodes)))
                                         (dolist (N deductive-nodes) (setf (undefeated-degree-of-support N) 1.0))
                                         (dolist (L deductive-links) (setf (support-link-strength L) 1.0))
                                         (display-belief-changes
                                           *new-links*
                                           deductive-nodes
                                           nil))
                                       (dolist (instruction (positive-query-instructions (resultant-interest link)))
                                           (funcall instruction node))
                                       (when *display?*
                                            (terpri)
                                            (princ "             ALL QUERIES HAVE BEEN ANSWERED DEDUCTIVELY.")
                                            (terpri))
                                       ; (cancel-interest-in (link-interest link) 0)
                                       (throw 'die nil)))
                             ; (record-query-answers link)
                             )
                           ((remaining-premises link)
                             (construct-interest-link
                               link node instantiations binding (remaining-premises link) supposition
                               (degree-of-interest (link-interest link))
                               (maximum-degree-of-interest (link-interest link)) (1+ depth) priority interests))
                           ((or
                                  (some #'(lambda (L) (eq (link-rule L) ug))
                                        (left-links (resultant-interest link)))
                                  (funcall+ (discharge-condition interest) nil u binding))
                             (cond
                               ((conclusions-function reason)
                                 (dolist (P (funcall (conclusions-function reason) binding))
                                     (draw-conclusion
                                       (car P) (cons node (supporting-nodes link)) reason instantiations
                                       (discount-factor reason) depth nil (cdr P) :binding binding :interest
                                       (resultant-interest link) :link link :clues (link-clues link))))
                               (t
                                 (draw-conclusion
                                   (interest-formula (resultant-interest link)) (cons node (supporting-nodes link)) reason
                                   instantiations (discount-factor reason) depth nil (defeasible-rule reason)
                                   :binding binding :interest (resultant-interest link) :link link :clues (link-clues link)))
                               )))))))
            (when (and (cancelling-node interest) (every #'discharged-link (right-links interest)))
                 (cancel-interest-in interest (if *trace* depth 0)))
            (when (and
                         unifiers
                         (not (cancelled-interest interest))
                         (equal (node-formula node) (interest-formula interest))
                         (subsetp= (node-supposition node) (interest-supposition interest))
                         (dolist (sup-node (generated-suppositions interest))
                             (when
                                  (and
                                    (equal (generating-interests sup-node) (list interest))
                                    (deductive-in node sup-node))
                                  (cancel-node sup-node (if *trace* depth 0)))))))
          )))

#| This returns deductive-node. |#
(defunction validating-deductive-node (S deductive-rule?)
    (let ((c-list (c-list-for (sequent-formula S))))
       (when c-list
            (let ((sup (sequent-supposition S)))
               (find-if
                 #'(lambda (c)
                       (and (deductive-node c)
                                 (or (not (deductive-only c)) deductive-rule?)
                                 (subsetp= (node-supposition c) sup)))
                 (c-list-nodes c-list))))))

(defunction record-query-answers (link)
   ; (when (eq link (link 1)) (break))
    (let* ((C (mem1 (supporting-nodes link)))
              (degree (compute-undefeated-degree-of-support C))
              (Q (resultant-interest link)))
       (pushnew C (query-answers Q))
       (pull C (supporting-nodes link))
       (pushnew Q (answered-queries C))
       (when (and *display?* *graphics-on*)
            (draw-just-node (node-position C *og*) *og* C (node-color C *og*)))
       (cond ((and (not (zerop degree))
                           (>= degree (query-strength Q))
                           (or (null (old-undefeated-degree-of-support C))
                                 (zerop (old-undefeated-degree-of-support C))
                                 (< (old-undefeated-degree-of-support C) (query-strength Q))))
               (when *log-on* (push (list :answer-query C Q degree) *reasoning-log*))
                    (when *display?*
                         (princ "               ")
                         (princ "=========================================") (terpri)
                         (princ "               ") (princ "Justified belief in ")
                         (prinp (node-formula C)) (terpri)
                         (princ "               with undefeated-degree-of-support ")
                         (princ (compute-undefeated-degree-of-support C)) (terpri)
                         (princ "               ") (princ "answers ") (princ Q)
                         (terpri) (princ "               ")
                         (princ "=========================================") (terpri))
                    (dolist (instruction (positive-query-instructions Q))
                         (funcall instruction C))
                    (setf (answered? Q) t))
                   (*display?*
                     (princ "               ----------------------------------------") (terpri)
                     (princ "               ") (princ C)
                     (princ " answers ") (princ Q) (terpri)
                     (princ "               ----------------------------------------") (terpri)))
       (when (deductive-node C)
            (when (and
                          (every
                            #'(lambda (query)
                                  (or (eq query Q)
                                        (some #'deductive-node (query-answers query))))
                            *ultimate-epistemic-interests*)
                          (not (some
                                      #'(lambda (Q) (eq (item-kind Q) :query))
                                      *inference-queue*)))
                 (setf (undefeated-degree-of-support C) 1.0)
                 (setf (answered? Q) T)
                 (when *display?*
                      (princ "             ALL QUERIES HAVE BEEN ANSWERED DEDUCTIVELY.")
                      (terpri))
                 (cancel-interest-in (link-interest link) 0)
                 (throw 'die nil)))))

(defunction condition-satisfying-interest (S condition link vars)
    (multiple-value-bind
         (interests match)
         (interests-for (sequent-formula S) vars)
         (when interests
              (let ((sup (match-sublis match (sequent-supposition S))))
                 (find-if #'(lambda (i)
                                   (and (eq (deductive-interest i)
                                                    (deductive-interest (resultant-interest link)))
                                             (funcall* (mem1 condition) i)
                                             (== (interest-supposition i) sup)))
                              interests)))))

(defunction construct-new-interest-for
    (link vars condition degree maximum-degree depth i-list text-condition)
   ; (when (equal link (link 6)) (setf l link v vars c condition d degree m* maximum-degree d* depth i i-list) (break))
    ;; (step (construct-new-interest-for l v c d m* d* i))
    (let* ((gn (link-generating-node link))
              (interest
                (make-interest
                  :interest-number (incf *interest-number*)
                  :interest-sequent (list (link-supposition link) (link-interest-formula link))
                  :interest-formula (link-interest-formula link)
                  :interest-variables vars
                  :interest-supposition (link-supposition link)
                  :interest-supposition-variables
                  (unionmapcar= #'formula-node-variables (link-supposition link))
                  :right-links (list link)
                  :generating-nodes (if gn (list gn))
                  :degree-of-interest degree
                  :text-discharge-condition text-condition
                  :maximum-degree-of-interest maximum-degree
                  :deductive-interest (deductive-interest (resultant-interest link))
                  :interest-defeat-status (link-defeat-status link)
                  :reductio-interest (reductio-interest (resultant-interest link)))))
       (funcall* condition interest)
       (if gn (push interest (generated-interests gn)))
       (compute-interest-supposition-nodes interest)
       (store-interest interest i-list)
       (when *trace* (indent (1+ depth)) (princ "CONSTRUCT-NEW-INTEREST-FOR LINK:") (terpri))
       (when *display?* (display-interest interest))
       (when *log-on* (push interest *reasoning-log*))
       (when (and *display?* *graphics-on* *graph-interests*) (draw-i interest *og*))
       interest))

(defunction compute-interest-supposition-nodes (interest)
    (when (interest-supposition interest)
         (dolist (n (generating-nodes interest))
             (when (not (member n (interest-supposition-nodes interest)))
                  (push n (interest-supposition-nodes interest))
                  (dolist (in (generating-interests n))
                      (setf (interest-supposition-nodes interest)
                               (union
                                 (interest-supposition-nodes interest)
                                 (interest-supposition-nodes in))))))
         (dolist (L (right-links interest))
             (setf (interest-supposition-nodes interest)
                      (union
                        (interest-supposition-nodes interest)
                        (interest-supposition-nodes (resultant-interest L)))))))

(defunction re-queue-interest (link interest-priority interest degree)
    ; (when (eq interest (interest 7)) (setf l link p interest-priority i interest d degree) (break))
    ;;  (step (re-queue-interest l p i d))
    (let ((Q (interest-queue-node interest)))
      (cond (Q
                  (let ((preference
                            (interest-preference
                              (interest-link-priority link interest-priority interest)
                              (sequent-complexity (interest-sequent interest)))))
                    (when (> preference (degree-of-preference Q))
                         (setf *inference-queue*
                                  (ordered-insert Q (remove Q *inference-queue*) #'i-preferred)))))
                (t
                  (let ((old-degree (last-processed-degree-of-interest interest)))
                    (when (or (null old-degree) (< degree old-degree))
                         (queue-interest interest (interest-link-priority link interest-priority interest))
                         ))))))

(defunction unifying-nodes (interest)
    (let ((nodes nil))
       (dolist (cl (corresponding-c-lists (interest-i-list interest)))
           (dolist (c (c-list-nodes (mem1 cl)))
               (push c nodes)))
       nodes))

(defun funcall** (f x y) (if f (funcall f x y) t))

(defunction validating-node (interest degree binding)
    (let ((node nil))
       (some
         #'(lambda (cl)
               (let ((unifiers nil)
                       (unifier (mem2 cl)))
                  (setf node
                           (find-if
                             #'(lambda (c)
                                   (and (>= (compute-maximal-degree-of-support c) degree)
                                            (funcall+ (discharge-condition interest) c unifier binding)
                                             (setf unifiers
                                                      (appropriately-related-suppositions c interest unifier))))
                             (c-list-nodes (mem1 cl))))
                  (when node
                       (push (list interest unifier unifiers) (discharged-interests node)))))
         (corresponding-c-lists (interest-i-list interest)))
       node))

#| For non-reductio-interests, this returns the list of unifiers unifying the node-supposition of
node into the the interest-supposition of interest.  For reductio-interests, this returns the list of
unifiers unifying the non-inherited part of the non-reductio-supposition into the
interest-supposition. |#
(defunction appropriately-related-suppositions (node interest unifier &optional a-list target)
    (when (null target) (setf target interest))
    (let* ((i-sup (match-sublis (mem2 unifier) (interest-supposition interest)))
              (c-vars
            (subset #'(lambda (x) (and (symbolp x) (eq (var-kind x) :variable)))
                        (match-sublis (mem1 unifier) (node-supposition-variables node))))
              (i-vars
            (subset #'(lambda (x) (and (symbolp x) (eq (var-kind x) :variable)))
                        (match-sublis (mem2 unifier) (interest-variables interest)))))
      (if (and (not (query-p target)) (reductio-interest target))
        (let ((domain nil))
          (dolist (S (non-reductio-supposition node))
              (let ((sup (cdr S)))
                (when (not (member sup *inherited-non-reductio-suppositions*))
                     (push (car S) domain))))
          (set-unifier (match-sublis (mem1 unifier) (match-sublis a-list domain)) i-sup c-vars i-vars))
        (set-unifier
          (match-sublis (mem1 unifier)
                                 (match-sublis a-list (node-supposition node)))
          i-sup c-vars i-vars))))

(defunction appropriately-related-reductio-suppositions (node interest unifier)
    (when (and (not (query-p interest)) (reductio-interest interest))
         (let* ((i-sup (match-sublis (mem2 unifier) (interest-supposition interest)))
              (c-vars
            (subset #'(lambda (x) (and (symbolp x) (eq (var-kind x) :variable)))
                        (match-sublis (mem1 unifier) (node-supposition-variables node))))
              (i-vars
            (subset #'(lambda (x) (and (symbolp x) (eq (var-kind x) :variable)))
                        (match-sublis (mem2 unifier) (interest-variables interest)))))
           (let ((domain nil))
             (dolist (S (non-reductio-supposition node))
                 (let ((sup (cdr S)))
                   (when (not (member sup *inherited-non-reductio-suppositions*))
                        (push (car S) domain))))
             (set-unifier (match-sublis (mem1 unifier) domain) i-sup c-vars i-vars)))))

(defunction appropriately-related-non-reductio-suppositions (node interest unifier)
    ; (When (eq node (node 127)) (setf n1 node i interest u unifier) (break))
    ;; (step (appropriately-related-non-reductio-suppositions n1 i u))
    (let* ((i-sup (match-sublis (mem2 unifier) (interest-supposition interest)))
              (c-vars
            (subset #'(lambda (x) (and (symbolp x) (eq (var-kind x) :variable)))
                        (match-sublis (mem1 unifier) (node-supposition-variables node))))
              (i-vars
            (subset #'(lambda (x) (and (symbolp x) (eq (var-kind x) :variable)))
                        (match-sublis (mem2 unifier) (interest-variables interest)))))
      (set-unifier (match-sublis (mem1 unifier) (node-supposition node)) i-sup c-vars i-vars)))

#| This returns the list of unifiers unifying the node-supposition of  node into the the
node-supposition of node*. |#
(defunction appropriately-related-node-suppositions (node node* unifier)
    (let* ((sup (match-sublis (mem1 unifier) (node-supposition node)))
              (sup* (match-sublis (mem2 unifier) (node-supposition node*)))
              (vars
            (subset #'(lambda (x) (and (symbolp x) (eq (var-kind x) :variable)))
                        (match-sublis (mem1 unifier) (node-supposition-variables node))))
              (vars*
            (subset #'(lambda (x) (and (symbolp x) (eq (var-kind x) :variable)))
                        (match-sublis (mem2 unifier) (node-supposition-variables node*)))))
      (set-unifier sup sup* vars vars*)))

(defunction appropriately-related-supposition (node interest supposition supposition-variables unifier)
   ; (setf n node i interest s supposition sv supposition-variables u unifier)
    ;; (step (appropriately-related-supposition n i s sv u))
    (let* ((i-sup (match-sublis (mem2 unifier) supposition))
              (c-vars
            (subset #'(lambda (x) (and (symbolp x) (eq (var-kind x) :variable)))
                        (match-sublis (mem1 unifier) (node-supposition-variables node))))
              (i-vars
            (subset #'(lambda (x) (and (symbolp x) (eq (var-kind x) :variable)))
                        (match-sublis (mem2 unifier) supposition-variables))))
      (if (and (not (query-p interest)) (reductio-interest interest))
        (let ((domain nil))
          (dolist (S (non-reductio-supposition node))
              (let ((sup (cdr S)))
                (when (not (member sup *inherited-non-reductio-suppositions*))
                     (push (car S) domain))))
          (set-unifier (match-sublis (mem1 unifier) domain) i-sup c-vars i-vars))
        (set-unifier
          (match-sublis (mem1 unifier) (node-supposition node)) i-sup c-vars i-vars))))

;................................................. FORWARDS REASONING ........................................
#|  In the following functions, the depth variable is used in printing the trace. |#

(defunction reason-forwards-from (node depth)
    (when *trace* (indent depth) (princ "REASON-FORWARDS-FROM: ")
                 (princ node) (terpri))
   ; (when (equal node (node 671)) (setf n node d depth) (break))
    ;; (step (reason-forwards-from n d))
    (when (eq (node-justification node) :reductio-supposition) (decf *unused-suppositions*))
    (discharge-interest-schemes node 0 (1+ depth))
    (when (not (cancelled-node node)) (apply-forwards-reasons node depth))
    (when (eq (node-kind node) :inference)
         (let ((i-lists (corresponding-i-lists (node-c-list node))))
            (when (null (interests-discharged? node)) (discharge-interest-in node i-lists 0 t depth nil))
            (when *use-reductio*
                 (when (not (cancelled-node node)) (adopt-reductio-interest node (1+ depth) nil))
                 (discharge-delayed-reductios node depth nil)))  )
    (dolist (rule *auxiliary-forwards-rules*) (funcall rule node)))

(defunction apply-forwards-reasons (node depth)
    ; (when (equal node (node 10)) (setf n node) (break))
    ;; (step (apply-forwards-reasons n 0))
    (catch 'apply-forwards-reasons
        (let* ((c-list (node-c-list node))
                  (d-node (c-list-d-node c-list)))
           (reason-from-dominant-premise-nodes node d-node depth))))

(defunction apply-forwards-defeasible-reasons (node)
    (catch 'apply-forwards-defeasible-reasons
        (let* ((c-list (node-c-list node))
                  (d-node (c-list-d-node c-list)))
           (reason-defeasibly-from-dominant-premise-nodes node d-node))))

(defunction reason-from-dominant-premise-nodes (node d-node depth)
   ; (when (and (eq node (node 252)) (eq d-node (d-node 68))) (setf n node dn d-node d depth) (break))
    ;; (step (reason-from-dominant-premise-nodes n dn d))
    (reason-from-instantiated-premises node d-node depth)
    (let ((pn (parent-d-node d-node)))
       (when pn (reason-from-dominant-premise-nodes node pn depth))))

(defunction reason-defeasibly-from-dominant-premise-nodes (node d-node)
    (reason-defeasibly-from-instantiated-premises node d-node)
    (let ((pn (parent-d-node d-node)))
       (when pn (reason-defeasibly-from-dominant-premise-nodes node pn))))

(defunction reason-from-instantiated-premises (node d-node depth)
   ; (when (and (eq node (node 252)) (eq d-node (d-node 10))) (setf n node dn d-node d depth) (break))
    ;; (step (reason-from-instantiated-premises n dn d))
    (dolist (ip (d-node-forwards-reasons d-node))
        (let* ((reason (ip-reason ip))
                  (reason-function (reason-function reason)))
                    ;(and (null (ip-basis ip)) (reason-function reason))))
           (when (cancelled-node node) (throw 'apply-forwards-reasons nil))
           (when (or (not (deductive-only node)) (not (defeasible-rule reason)))
                (cond
                  (reason-function (funcall reason-function node depth ip))
                  ((ip-initial? ip) (reason-substantively-from-first-instantiated-premise node depth ip))
                  (t (reason-substantively-from-non-initial-instantiated-premise nil depth ip node)))))))

(defunction reason-defeasibly-from-instantiated-premises (node d-node)
    ; (when (and (eq node (node 5)) (eq d-node (d-node 19)))
    ;      (setf n node dn d-node tl term-list d depth) (break))
    ;; (step (reason-from-instantiated-premises n dn tl d))
    (dolist (ip (d-node-forwards-reasons d-node))
        (let ((reason (ip-reason ip)))
          (when (defeasible-rule reason)
               (let ((reason-function (and (null (ip-basis ip)) (reason-function reason))))
                 (when (cancelled-node node) (throw 'apply-forwards-defeasible-reasons nil))
                 (when (not (deductive-only node))
                      (cond
                        (reason-function (funcall reason-function node 0 ip))
                        ((ip-basis ip)
                          (reason-substantively-from-non-initial-instantiated-premise nil 0 ip node))
                        (t (reason-substantively-from-first-instantiated-premise node 0 ip)))))))))

(defunction reason-substantively-from-first-instantiated-premise (node depth ip)
    ; (when (eq ip (ip 29)) (setf n node d depth p ip) (break))
    ;; (step (reason-substantively-from-first-instantiated-premise n d p))
    (multiple-value-bind
         (binding instantiation)
         (funcall (fp-binding-function (ip-premise ip)) (node-formula node) (node-variables node))
         (let ((spec (premise-node-specifier (ip-premise ip))))
           (when spec (push (cons spec node) binding)))
         (when (and instantiation (equal (fp-kind (ip-premise ip)) (node-kind node))
                             (funcall** (fp-condition (ip-premise ip)) node binding))
              (cond
                ((ip-remaining-premises ip)
                  (let* ((ip*
                              (store-instantiated-premise
                                (ip-reason ip) node nil binding (list instantiation) ip (ip-remaining-premises ip)))
                            (dn (ip-d-node ip*)))
                    (reason-from-subsidiary-c-lists dn depth ip*)))
                (t (make-forwards-inference
                      binding (if (not (clue? (ip-premise ip))) (list instantiation))
                      (if (not (clue? (ip-premise ip))) (list node))
                      (if (clue? (ip-premise ip)) (list node))
                      depth ip))))))

(defunction reason-from-subsidiary-c-lists (d-node depth ip)
    (dolist (c-list (d-node-c-lists d-node))
        (when (c-list-processed-nodes c-list)
             (reason-substantively-from-non-initial-instantiated-premise c-list depth ip)))
    (dolist (test (discrimination-tests d-node))
        (reason-from-subsidiary-c-lists (cdr test) depth ip)))

(defunction reason-substantively-from-non-initial-instantiated-premise
    (c-list depth ip &optional node)
    ; (when (eq ip (ip 29)) (setf n node d depth p ip c c-list) (break))
    ;; (step (reason-substantively-from-non-initial-instantiated-premise c d p n))
    (let* ((vars (if node (node-variables node) (c-list-variables c-list)))
              (formula (if node (node-formula node) (c-list-formula c-list))))
      (multiple-value-bind
           (binding0 instantiation0)
           (funcall (fp-binding-function (ip-premise ip)) formula vars)
           (when instantiation0
                (let ((unifier
                          (binding-unifier
                            binding0 (ip-binding ip)
                            (ip-used-premise-variables ip) vars (ip-used-variables ip))))
                  (when unifier
                       (let
                         ((binding
                            (rectify-binding binding0 unifier ip))
                           (instantiations
                             (cons (merge-matches* (mem1 unifier) instantiation0)
                                       (mapcar #'(lambda (in) (merge-matches* (mem2 unifier) in))
                                                      (ip-instantiations ip))))
                           (spec (premise-node-specifier (ip-premise ip))))
                         (let ((nodes nil))
                           (when
                                (or
                                  (and node
                                           (equal (fp-kind (ip-premise ip)) (node-kind node))
                                           (funcall** (fp-condition (ip-premise ip)) node
                                                            (if spec (cons (cons spec node) binding) binding))
                                           (setf nodes (list node)))
                                  (and (null node)
                                           (setf nodes
                                                    (subset
                                                      #'(lambda (c)
                                                            (and (equal (fp-kind (ip-premise ip)) (node-kind c))
                                                                     (funcall** (fp-condition (ip-premise ip)) c
                                                                                      (if spec (cons (cons spec c) binding) binding))))
                                                      (c-list-processed-nodes c-list)))))
                                (cond
                                  ((ip-remaining-premises ip)
                                    (dolist (node nodes)
                                        (let* ((ip*
                                                    (store-instantiated-premise
                                                      (ip-reason ip) node c-list
                                                       (if spec (cons (cons spec node) binding) binding)
                                                       instantiations ip (ip-remaining-premises ip))))
                                          (when ip* (reason-from-subsidiary-c-lists (ip-d-node ip*) depth ip*)))))
                                  (t
                                    (dolist (node nodes)
                                        (make-forwards-inference
                                          binding instantiations
                                          (if (clue? (ip-premise ip)) (ip-basis ip) (cons node (ip-basis ip)))
                                (if (clue? (ip-premise ip)) (cons node (ip-clues ip)))
                                           depth ip)))))))))))))

(defunction rectify-binding (binding0 unifier ip)
    (let ((binding
              (mapcar
                #'(lambda (assoc)
                      (cons (car assoc) (match-sublis (mem2 unifier) (cdr assoc))))
                (ip-binding ip))))
       (dolist (v (fp-variables (ip-premise ip)))
           (when (null (assoc v (ip-binding ip)))
                (push (cons v (match-sublis (mem1 unifier) (cdr (assoc v binding0)))) binding)))
       binding))

(defunction binding-unifier (binding1 binding2 premise-variables vars1 vars2)
    (let ((term-list1 nil)
            (term-list2 nil))
       (dolist (v premise-variables)
           (let ((assoc1 (assoc v binding1))
                   (assoc2 (assoc v binding2)))
              (when (and assoc1 assoc2)
                   (push (cdr assoc1) term-list1) (push (cdr assoc2) term-list2))))
       (unifier term-list1 term-list2 vars1 vars2)))

(defunction make-forwards-inference (binding instantiations basis clues depth ip)
   ; (when (eql *inference-number* 284) (setf b binding in instantiations bs basis cl clues d depth i ip) (break))
   ;;  (step (make-forwards-inference b in bs cl d i))
    (when *trace* (indent depth) (princ "MAKE-FORWARDS-INFERENCE from instantiated-premise ")
                (princ (ip-number ip)) (terpri))
    (cond
      ((backwards-premises (ip-reason ip))
        (let ((formulas (funcall (conclusions-function (ip-reason ip)) binding))
                (sup nil)
                (instantiations+ instantiations)
                (variables (unionmapcar+ #'node-variables basis))
                (new-vars nil))
          (dolist (b basis)
              (let ((b-sup (node-supposition b))
                      (b-vars (setdifference (node-supposition-variables b) (node-variables b))))
                (dolist (var b-vars)
                    (when (mem var variables)
                         (let ((new-var (make-interest-variable)))
                           (push new-var new-vars)
                           (setf b-sup (=subst new-var var b-sup)))))
                (setf sup (union= sup (match-sublis (mem1 instantiations+) b-sup)))
                (setf instantiations+ (cdr instantiations+))))
          (setf sup
                   (remove-if
                     #'(lambda (s)
                           (some #'(lambda (b) (and (not (equal s b)) (match s b new-vars))) sup)) sup))
          (dolist (formula formulas)
              (let* ((sequent (list sup (car formula)))
                        (deductive-node (validating-deductive-node sequent (not (defeasible-rule (ip-reason ip))))))
                (cond (deductive-node
                            (draw-conclusion
                              (car formula) (cons deductive-node basis) (ip-reason ip) (cons t instantiations) 1 depth
                              nil (cdr formula) :binding binding :clues clues))
                          (t
                            (let ((degree
                                      (minimum
                                        (cons (applied-forwards-reason-strength (ip-reason ip) binding basis)
                                                  (append
                                                    (mapcar #'undefeated-degree-of-support (ip-basis ip))
                                                    (mapcar #'undefeated-degree-of-support (ip-clues ip))
                                                    (mapcar #'query-strength *ultimate-epistemic-interests*))))))
                              (construct-initial-interest-link
                                basis instantiations (ip-reason ip) nil depth degree binding sup
                                :remaining-premises (backwards-premises (ip-reason ip)) :clues clues))))))))
      (t
        (dolist (formula (funcall (conclusions-function (ip-reason ip)) binding))
            (draw-conclusion
              (car formula) basis (ip-reason ip) instantiations (discount-factor (ip-reason ip)) depth nil
              (cdr formula) :binding binding :clues clues)))))

#| This code is modified from DISCHARGE-LINK. |#
(defunction adopt-interest (S degree defeasible? binding)
    ;(when (equal *interest-number* 44) (setf ss s d degree df defeasible? b binding))
    ;; (step (adopt-interest ss d df b))
    ;; the following assumes there are no i-variables in formula
    (let ((deductive-node (validating-deductive-node S (not defeasible?))))
       (or
         deductive-node
         ;; code from condition-satisfying-interest
         (let ((interest
                   (multiple-value-bind
                        (interests match)
                        (interests-for (sequent-formula S) nil)
                        (when interests
                             (let ((sup (match-sublis match (sequent-supposition S))))
                                (find-if #'(lambda (i) (== (interest-supposition i) sup)) interests))))))
            (cond (interest
                         (setf (degree-of-interest interest) (min (degree-of-interest interest) degree))
                         (setf (maximum-degree-of-interest interest)
                                  (max (maximum-degree-of-interest interest) degree))
                         (setf (interest-priority interest) (max (interest-priority interest) degree)))
                        (t
                          (setf interest (construct-new-interest-for-sequent S degree degree))
                          (setf (interest-priority interest) degree)
                          (let ((conclusion (validating-node interest degree binding)))
                             (when conclusion
                                  (when *display?*
                                       (princ "                                        ")
                                       (princ "Node #")
                                       (princ (inference-number conclusion))
                                       (princ " discharges interest #")
                                       (princ (interest-number interest))
                                       (terpri) (terpri))
                                  (pushnew conclusion (discharging-nodes interest))
                                  (when (and (not (cancelled-interest interest))
                                                        (equal (node-formula conclusion) (interest-formula interest))
                                                        (subsetp= (node-supposition conclusion) (interest-supposition interest))
                                                        (dolist (sup-node (generated-suppositions interest))
                                                            (when (and
                                                                         (equal (generating-interests sup-node) (list interest))
                                                                         (deductive-in conclusion sup-node))
                                                                 (cancel-node sup-node 0)))))))))
            interest))))

(defunction construct-new-interest-for-sequent (S degree maximum-degree)
    ; (when (equal link (link 2))
    ;      (setf b* b l link d degree m* maximum-degree d* depth) (break))
    (let ((interest
              (make-interest
                :interest-number (incf *interest-number*)
                :interest-sequent S
                :interest-formula (sequent-formula S)
                :interest-supposition (sequent-supposition S)
                :interest-supposition-variables
                (unionmapcar= #'formula-node-variables (sequent-supposition S))
                :degree-of-interest degree
                :maximum-degree-of-interest maximum-degree)))
       (compute-interest-supposition-nodes interest)
       (store-interest interest)
       (when *display?* (display-interest interest))
       (if *log-on* (push interest *reasoning-log*))
       interest))

(defunction invert-contradiction  (L node node* D N instantiations depth)
   ; (setf l* l n0 node n* node* d* d nn n d** depth)
    ;; (step (invert-contradiction l* n0 n* d* nn d**))
    (let ((variables nil)
            (reverse-binding nil)
            (reverse-binding* nil)
            (binding* nil))
      (dolist (b (support-link-binding L))
                      (cond ((or (and (listp (cdr b)) (skolem-function (mem1 (cdr b))))
                                       (skolem-function (cdr b))
                                       (conclusion-variable (cdr b)))
                                  (push (car b) variables)
                                  (push (cons (cdr b) (car b)) reverse-binding)
                                  (push (cons (cdr b) (make-interest-variable)) reverse-binding*))
                                (t (push b binding*))))
      (let* ((S (node-sequent (support-link-target L)))
                (B (support-link-basis L))
                (supposition
                  (subset
                    #'(lambda (P)
                          (every #'(lambda (b) (not (occur (car b) P :test 'equal))) reverse-binding))
                    (sequent-supposition S)))
                (sup-remainder (setdifference (sequent-supposition S) supposition))
                (antecedent (match-sublis reverse-binding sup-remainder :test 'equal))
                (antecedent*
                  (gen-conjunction
                    (match-sublis reverse-binding* sup-remainder :test 'equal)))
                (antecedent-variables
                  (subset #'(lambda (v) (occur v antecedent)) variables))
                (sup
                  (if sup-remainder
                    (generalized-e-gen antecedent-variables (gen-conjunction antecedent))))
                (new-sup (if sup (cons sup supposition) supposition))
                (formula (match-sublis reverse-binding* (sequent-formula S)))
                (base
                  (mapcar
                    #'(lambda (c m)
                          (cond ((is-desire c)
                                      (list 'I_desire_that
                                             (match-sublis reverse-binding*
                                                                    (match-sublis m (node-formula c)))))
                                    ((is-percept c)
                                      (let ((time (percept-date (node-justification c))))
                                        (list 'it-appears-to-me-that
                                               (match-sublis reverse-binding*
                                                                      (match-sublis m (mem2 (node-formula c))))
                                               (list 'closed time time))))
                                    (t (match-sublis reverse-binding*
                                                               (match-sublis m (node-formula c)) :test 'equal))))
                    B instantiations))
                (rebutting-defeater
                  (cond (antecedent* (conj antecedent* (conj (gen-conjunction base) (neg formula))))
                            (variables (conj (gen-conjunction base) (neg formula)))
                            (t (neg formula)))))
        (draw-conclusion
          rebutting-defeater (adjoin node* (remove N D))
          (read-from-string
            (cat-list (list ":inversion_from_contradictory_nodes_"
                                 (string-rep (inference-number node))
                                 "_and_" (string-rep (inference-number node*)))))
          nil 1 (1+ depth) nil nil :motivators (list node) :supposition new-sup))))

(defunction invert-contradictions (node instantiations depth)
    ; (when (eq node (node 43)) (break))
    ;; (step (invert-contradictions (node 43) 0))
    (let ((c-list (node-c-list node)))
      (dolist (nl (c-list-contradictors c-list))
          (let* ((unifier (mem2 nl))
                    (unifier* (reverse unifier)))
            (dolist (node* (c-list-nodes (mem1 nl)))
                (when (not (deductive-node node*))
                     (dolist (u (appropriately-related-node-suppositions node* node unifier))
                         (dolist (D (nearest-defeasible-ancestors node))
                             (dolist (N D)
                                 (when (set-unifier
                                              (match-sublis (mem2 u) (node-supposition node))
                                              (node-supposition N)
                                              (append (node-variables node) (node-variables node*))
                                              (node-variables N))
                                      (dolist (L (support-links N))
                                          (invert-contradiction L node node* D N instantiations depth)))))))
                (when (not (deductive-node node))
                     (dolist (u (appropriately-related-node-suppositions node node* unifier*))
                         (dolist (D (nearest-defeasible-ancestors node*))
                             (dolist (N D)
                                 (when (set-unifier
                                              (match-sublis (mem2 u) (node-supposition node*))
                                              (node-supposition N)
                                              (append (node-variables node) (node-variables node*))
                                              (node-variables N))
                                      (dolist (L (support-links N))
                                          (invert-contradiction L node* node D N instantiations depth))))))))))))

(defunction invert-contradictions-retrospectively (node NDA old-NDA)
    ; (when (equal (node 5) node) (setf n node nd nda on old-nda) (break))
    ;; (step (invert-contradictions-retrospectively n nd on))
    (let ((c-list (node-c-list node)))
      (dolist (nl (c-list-contradictors c-list))
          (let ((unifier (reverse (mem2 nl))))
            (dolist (node* (c-list-nodes (mem1 nl)))
                (dolist (u (appropriately-related-node-suppositions node node* unifier))
                    (dolist (N NDA)
                        (when
                             (and (not (some #'(lambda (Y) (member N Y)) old-NDA))
                                      (set-unifier
                                        (match-sublis (mem2 u) (node-supposition node*))
                                        (node-supposition N)
                                        (append (node-variables node) (node-variables node*))
                                        (node-variables N)))
                             (dolist (L (support-links N))
                                 (invert-contradiction L node node* NDA N u 0))))))))))

(defunction invert-contradictions-from-new-support-link (link instantiations)
    (let ((target (support-link-target link)))
      (dolist (node (deductive-consequences target))
          (let ((c-list (node-c-list node)))
            (dolist (nl (c-list-contradictors c-list))
                (let ((unifier (mem2 nl)))
                  (dolist (node* (c-list-nodes (mem1 nl)))
                      (when (not (deductive-node node*))
                           (dolist (u (appropriately-related-node-suppositions node* node unifier))
                               (when (set-unifier (match-sublis (mem2 u) (node-supposition node))
                                                              (node-supposition target)
                                                              (append (node-variables node) (node-variables node*))
                                                              (node-variables target))
                                    (dolist (D (nearest-defeasible-ancestors node))
                                        (invert-contradiction link node node* D target instantiations 0))))))))))))

(defunction deductive-consequences (node)
    (let ((descendants (list node))
            (nodes (list node)))
       (loop
          (let ((node (car nodes)))
             (setf nodes (cdr nodes))
             (dolist (L (consequent-links node))
                 (when (not (defeasible? L))
                      (let ((N (support-link-target L)))
                         (when (not (member N descendants))
                              (push N descendants)
                              (push N nodes)))))
             (when (null nodes) (return descendants))))))

(defunction cancel-subsumed-links (link depth)
    ; (when (equal link (support-link 14)) (break))
    ;; (step (cancel-subsumed-links (support-link 14) 0))
    (when (not (defeasible? link))
         (let* ((node (support-link-target link))
                   (formula (node-formula node))
                   (f-vars (node-variables node)))
            (dolist (cl (d-node-c-lists (c-list-d-node (node-c-list node))))
                (let* ((P (c-list-formula cl))
                          (m (match formula P f-vars)))
                   (when (and m (equal P (match-sublis m formula)))
                        (let* ((sup (match-sublis m (node-supposition node)))
                                  (vars (setdifference (unionmapcar #'formula-node-variables sup) f-vars))
                                  (NR (match-sublis m (non-reductio-supposition node))))
                           (dolist (M (c-list-nodes cl))
                               (cond
                                 ((eq M node)
                                   (let ((NDA (support-link-nearest-defeasible-ancestors link)))
                                      (dolist (L (support-links M))
                                          (when
                                               (and (not (eq L link))
                                                         (not (defeasible? L)))
                                               (let ((NDA* (support-link-nearest-defeasible-ancestors L)))
                                                  (when (every
                                                                #'(lambda (Y)
                                                                      (some #'(lambda (X) (subsetp X Y)) NDA))
                                                                NDA*)
                                                       (delete-arguments L M link depth)
                                                       (when *display?*
                                                                 (princ link) (princ " subsumes ") (princ L) (terpri))
                                                       ; (pull L (support-links M))
                                                       ))))))
                                 ((<= (length (node-supposition node)) (length (node-supposition M)))
                                   (let* ((M-sup (node-supposition M))
                                             (SM (set-match sup M-sup vars)))
                                      (when
                                           (and SM
                                                     (some
                                                       #'(lambda (s)
                                                             (subsetp=
                                                               (match-sublis (mem2 s) NR)
                                                               (non-reductio-supposition M)))
                                                       SM))
                                           (let ((NDA (support-link-nearest-defeasible-ancestors link)))
                                              (dolist (L (support-links M))
                                                  (when
                                                       (and (not (cancelled-node (support-link-target L)))
                                                                 (not (link-ancestor L link))
                                                                 (let ((NDA* (support-link-nearest-defeasible-ancestors L)))
                                                                    (every
                                                                      #'(lambda (Y)
                                                                            (some #'(lambda (X) (subsetp X Y)) NDA))
                                                                      NDA*)))
                                                            (delete-arguments L M link depth)
                                                            (when *display?*
                                                                 (princ link) (princ " subsumes ") (princ L) (terpri))
                                                            )))))))))))))))

#| L0 subsumes link which supports node. |#
(defunction delete-arguments (link node L0 depth)
    (declare (special *deleted-arguments*))
    ; (when (equal link (support-link 10)) (setf l link n node ll l0 d depth) (break))
    ;; (step (delete-arguments l n ll d t))
    (setf *deleted-arguments* nil)
    (when (and (not (member link *deleted-arguments*))
                          (not (cancelled-node node))
                          (not (link-ancestor link L0)))
         (push link *deleted-arguments*)
         ; (princ "**** Deleting ") (princ link) (terpri)
         (pull link (support-links node))
         (cond ((null (support-links node)) (cancel-node node (if *trace* depth 0)))
                     (t
                       (dolist (L (support-links node))
                           (let ((NDA
                                     (cond ((defeasible? L)
                                                  (mapcar #'genunion
                                                                  (gencrossproduct
                                                                    (mapcar #'nearest-defeasible-ancestors
                                                                                    (support-link-basis L)))))
                                                 (t (list (list node))))))
                              (dolist (X NDA)
                                  (when
                                       (not (some #'(lambda (Y) (subsetp= Y X))
                                                            (nearest-defeasible-ancestors node)))
                                       (dolist (Y (nearest-defeasible-ancestors node))
                                           (when (subsetp= X Y) (pull Y (nearest-defeasible-ancestors node))))
                                       (push X (nearest-defeasible-ancestors node))))
                              (recursively-compute-nearest-defeasible-ancestors node)))
                       (let ((ancestors
                                 (unionmapcar+
                                   #'(lambda (L)
                                         (union (support-link-basis L)
                                                      (unionmapcar+ #'node-ancestors (support-link-basis L))))
                                   (support-links node))))
                          (setf (node-ancestors node) ancestors)
                          (recursively-compute-node-ancestors node ancestors)
                          )))))

#| L is an ancestor of support-link link, whose target is node. |#
(defunction link-ancestor (L link)
    (some #'(lambda (N) (member L (support-links N)))
      (node-ancestors (support-link-target link))))

#| Rule is either a member of *forwards-reasons* or *backwards-reasons*,
or keyword describing an inference (:given, :Q&I, or :supposition).  basis
is a list of conclusions.  If supposition is not T, it is added to the supposition.  |#
(defunction DRAW-CONCLUSION
    (formula basis rule instantiations discount depth interests defeasible?
                   &key interest motivators binding link (supposition t) clues)
    ; (when (eql *inference-number* 10) (setf f formula b basis r rule i instantiations d discount d* depth in interests def defeasible? in* interest bi binding) (break) )
    ;;  (step (draw-conclusion f b r i d d* in def :interest in* :binding bi))
    (when (and formula (not (some #'cancelled-node basis))
                        (not (inconsistent-supposition basis)))
         (setf basis (reverse basis))
         (setf instantiations (reverse instantiations))
         (let* ((NDA (compute-nearest-defeasible-ancestors basis rule))
                   (discharge (if (backwards-reason-p rule)
                              (remove-double-negation (match-sublis binding (reason-discharge rule)))))
                   (CD (conclusion-data basis instantiations discharge supposition)))
           (when CD
                (let* ((RA (mem1 CD))
                          (NR (mem2 CD))
                          (sup (mem3 CD))
                          (sequent (list sup formula))
                          (d-node (d-node-for formula))
                          (c-list (if d-node (fetch-c-list-for formula d-node)))
                          (proof-nodes (if c-list (c-list-nodes c-list)))
                          (node (find-if #'(lambda (c)
                                                      (and (eq (node-kind c) :inference)
                                                               (== (node-supposition c) sup)))
                                                proof-nodes))
                          (new-node? (null node)))
                  (when
                       (and
                         (not (some #'(lambda (f) (mem (neg f) sup)) sup))
                         (or (null d-node)
                               (not (subsumed node basis sequent NDA NR rule binding d-node))))
                       (let* ((deductive-only (and (not (eq rule :reductio))
                                                                    (some #'deductive-only basis))))
                         (when (and node (deductive-only node) (not deductive-only))
                              (setf (deductive-only node) nil))
                         (when (null node)
                              (setf node (make-new-conclusion sequent deductive-only RA NR)))
                         (let ((old-degree (compute-maximal-degree-of-support node))
                                 (support-link
                                   (build-support-link
                                     basis clues rule discount node NDA binding link instantiations depth defeasible?)))
                           (cond
                             ((null support-link)
                               (decf *support-link-number*)
                               (when new-node? (decf *inference-number*)))
                             (t
                               (setf (motivating-nodes node) (union clues motivators))
                               (when new-node?
                                    (push node *inference-graph*)
                                    (store-inference-node-with-c-list
                                      node (sequent-formula sequent) c-list))
                               (when interest
                                    (push interest (enabling-interests node))
                                    (push node (enabled-nodes interest)))
                               (when *trace* (indent depth) (princ "DRAW CONCLUSION: ")
                                           (princ node) (terpri))
                               (when (read-char-no-hang) (clear-input) (throw 'die nil))
                               (let* ((i-lists (corresponding-i-lists (node-c-list node)))
                                         (increased-justification?
                                           (or new-node? (> (maximal-degree-of-support node) old-degree)))
                                         (cancellations
                                           (when increased-justification?
                                                (discharge-interest-in-defeaters node i-lists old-degree new-node?))))
                               (when *display?* (display-support-link support-link))
                                 (adopt-interest-in-defeaters-for support-link instantiations binding)
                                 (push support-link *new-links*)
                                 ; (update-beliefs support-link node)
                                 (dolist (node* cancellations) (cancel-node node* (if *trace* depth 0)))
                                 (when (not (cancelled-node node))
                                      (when increased-justification?
                                           (discharge-interest-in
                                             node i-lists old-degree new-node? (1+ depth) interests interest)
                                           (cond (*use-reductio*
                                                       (discharge-immediate-reductios
                                                         node old-degree new-node? (1+ depth) interests interest))))
                                      (when new-node? (invert-contradictions node instantiations (1+ depth)))
                                      (cancel-subsumed-links support-link depth)))))))
                       nil))))))

(defunction contradicting-nodes (n1 n2)
    (assoc (node-c-list n1) (c-list-contradictors (node-c-list n2))))

#| Combining the suppositions of the nodes in basis yields an inconsistent supposition. |#
(defunction inconsistent-supposition (basis)
    (let ((B (cdr basis)) (n (mem1 basis)))
       (loop
          (when
               (some
                 #'(lambda (m)
                       (or
                         (some #'(lambda (bm)
                                           (or
                                             (some #'(lambda (bn) (contradicting-nodes (cdr bm) (cdr bn)))
                                                          (reductio-ancestors n))
                                             (some #'(lambda (bn) (contradicting-nodes (cdr bm) (cdr bn)))
                                                          (non-reductio-supposition n))))
                                      (reductio-ancestors m))
                         (some #'(lambda (bm)
                                           (or
                                             (some #'(lambda (bn) (contradicting-nodes (cdr bm) (cdr bn)))
                                                          (reductio-ancestors n))
                                             (some #'(lambda (bn) (contradicting-nodes (cdr bm) (cdr bn)))
                                                          (non-reductio-supposition n))))
                                      (non-reductio-supposition m))))
                 B)
               (return t))
          (when (null (cdr b)) (return))
          (setf n (mem1 b))
          (setf b (cdr b)))))

(defunction compute-nearest-defeasible-ancestors (basis rule)
    (if (or (keywordp rule)
               (not (defeasible-rule rule)))
       (mapcar #'genunion
                       (gencrossproduct
                         (mapcar #'nearest-defeasible-ancestors basis)))
       (list nil)))

(defunction reductio-supposition (node) (eq (node-justification node) :reductio-supposition))

(defunction subsetp* (X Y)
    (subsetp X Y :test #'(lambda (z w)
                                          (and (equal (car z) (car w))
                                                    (or (reductio-supposition (cdr z))
                                                          (not (reductio-supposition (cdr w))))))))

(defunction subsumed (node basis sequent NDA non-reductio-supposition rule binding d-node)
    ; (when (equal *inference-number* 9)
    ;      (setf n node b basis s sequent nd nda nr non-reductio-supposition r rule bi binding dn d-node)  (break))
    ;; (step (subsumed n b s nd nr r bi dn))
    (let ((defeasible? (and (not (keywordp rule)) (defeasible-rule rule))))
       (when defeasible? (setf NDA (list (list node))))
       (cond
         (node
           (and
             (not defeasible?)
             (every #'(lambda (Y)
                               (some #'(lambda (X) (subsetp X Y)) (nearest-defeasible-ancestors node)))
                          NDA)))
         (t
           (let ((formula (sequent-formula sequent)))
              (some
                #'(lambda (cl)
                      (and
                        (c-list-nodes cl)
                        (let* ((P (c-list-formula cl))
                                  (f-vars (c-list-variables cl))
                                  (m (match P formula f-vars)))
                          (when (and m (equal formula (match-sublis m P)))
                               (let ((sup (sequent-supposition sequent)))
                                 (some
                                   #'(lambda (N)
                                         ; (and
                                         (let* ((N-sup (match-sublis m (node-supposition N)))
                                                   (vars
                                                     (setdifference
                                                       (unionmapcar= #'formula-node-variables (node-supposition N))
                                                       f-vars))
                                                   (sm (set-match N-sup sup vars)))
                                           (and
                                             SM
                                             (let ((NR (match-sublis m (non-reductio-supposition N))))
                                               (some
                                                 #'(lambda (s)
                                                       (subsetp= (match-sublis (mem2 s) NR) non-reductio-supposition))
                                                 sm))
                                             (cond
                                               (defeasible?
                                                   (let ((binding* (match-sublis m binding)))
                                                     (some
                                                       #'(lambda (L)
                                                             (and
                                                               (eq rule (support-link-rule L))
                                                               (equal binding* (support-link-binding L))
                                                               (== (unionmapcar+ #'nearest-defeasible-ancestors
                                                                                                basis)
                                                                      (unionmapcar+ #'nearest-defeasible-ancestors
                                                                                                (support-link-basis L)))))
                                                       (support-links N))))
                                               (t
                                                 (every
                                                   #'(lambda (Y)
                                                         (some
                                                           #'(lambda (X) (subsetp X Y)) (nearest-defeasible-ancestors N)))
                                                   NDA)))))
                                         ; (or (progn (princ "*** ")
                                         ;           (princ sequent) (princ " is subsumed by ") (princ N) (terpri))
                                         ;       t))
                                         )
                                   (c-list-nodes cl)))))))
                (d-node-c-lists d-node)))))))

#| RA does not contain two different base-reductio-suppositions, and if RA contains a
base-reductio-supposition then for some generating-interest of the base-reductio-supposition,
every member of NRS is an interest-supposition-node of that interest. |#
(defunction potent-suppositions (NRS RA)
    ; (setf nr nrs r ra); (break)
    ;; (step (potent-suppositions nr r))
    (every
      #'(lambda (R)
            (or (non-reductio-supposition? (cdr R))
                  (not (base-reductio-supposition (cdr R)))
                  (and
                    (every #'(lambda (x)
                                      (or (eq (cdr x) (cdr R))
                                            (non-reductio-supposition? (cdr x))
                                            (not (base-reductio-supposition (cdr x))))) RA)
                    (or (> (length RA) 1)
                          (some
                            #'(lambda (in)
                                  (every
                                    #'(lambda (nr)
                                          (member (cdr nr) (interest-supposition-nodes in)))
                                    NRS))
                            (generating-interests (cdr R)))
                  ))))
      RA))

(defunction conclusion-data (basis instantiations discharge supposition)
     ; (setf b basis i instantiations d discharge s supposition)
    ;  (princ sequent) (terpri) (break)
    (let* ((RA nil)
              (NR nil)
              (sup nil)
              (instantiations+ instantiations)
              (B+ basis))
       (when B+
            (loop
               (setf RA
                        (union= RA
                                       (subset #'(lambda (x)
                                                             (if (not (eq supposition t))
                                                                (member (car x) supposition)
                                                                (not (equal (car x) discharge))))
                                                      (match-sublis (mem1 instantiations+)
                                                                                (reductio-ancestors (mem1 B+))))))
               (setf B+ (cdr B+))
               (when (null B+) (return))
               (setf instantiations+ (cdr instantiations+))))
       (when  ;; this blocks multiple instantiations of reductio-ancestors
            (not (some
                      #'(lambda (R)
                            (some #'(lambda (R*)
                                              (and (not (eq R R*))
                                                        (eq (cdr R) (cdr R*))
                                                        (zerop (readopted-supposition (cdr R)))))
                                         RA))
                      RA))
            (let ((instantiations+ instantiations)
                    (B+ basis))
               (when B+
                    (loop
                       (setf
                         NR
                         (union= NR
                                        (subset #'(lambda (x)
                                                             (if (not (eq supposition t))
                                                                (member (car x) supposition)
                                                                (not (equal (car x) discharge))))
                                                       (match-sublis (mem1 instantiations+)
                                                                                 (non-reductio-supposition (mem1 B+))))))
                       (setf B+ (cdr B+))
                       (when (null B+) (return))
                       (setf instantiations+ (cdr instantiations+)))))
            (when   ;; this blocks multiple instantiations of non-reductio-suppositions
                 (and
                   (not (some
                             #'(lambda (R)
                                   (some #'(lambda (R*)
                                                     (and (not (eq R R*))
                                                               (eq (cdr R) (cdr R*))
                                                               (zerop (readopted-supposition (cdr R)))))
                                                NR))
                             NR))
                   (potent-suppositions NR RA))
                      (let ((instantiations+ instantiations)
                              (variables (unionmapcar+ #'node-variables basis))
                              (new-vars nil))
                         (dolist (b basis)
                             (let ((b-sup (node-supposition b))
                                     (b-vars (setdifference (node-supposition-variables b) (node-variables b))))
                                (dolist (var b-vars)
                                    ;; rewrite supposition-variables to avoid collision with formula-variables
                                    ;; of other members of the basis
                                    (when (member var variables)
                                         (let ((new-var (make-interest-variable)))
                                            (push new-var new-vars)
                                            (setf b-sup (subst new-var var b-sup)))))
                                (setf
                                  sup
                                  (union= sup
                                                 (subset #'(lambda (x) (not (equal x discharge)))
                                                                (match-sublis (mem1 instantiations+)
                                                                                          b-sup))))
                                (setf instantiations+ (cdr instantiations+)))))
                 (list RA NR (if (eq supposition t) sup (union= sup supposition)))))))

(defunction supposition-variables (sup)
    (unionmapcar= #'formula-node-variables sup))

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
       node))

#| This must recompute the set of node-arguments for the support-link-target and its
inference-descendants.  Node arguments are stored as triples (arg,strength,discounted-strength) |#
(defunction build-support-link (basis clues rule discount node NDA binding link instantiations depth defeasible?)
   ; (setf b basis r rule d discount n node nd nda bi binding de depth)
    ; (when (eql *support-link-number* 10) (setf b basis r rule d discount n node nd nda bi binding de depth) (break))
    ;; (step (build-support-link b r d n nd bi de))
    (incf *support-link-number*)
    (when (not (some #'(lambda (L)
                                         (and (equal (support-link-basis L) basis)
                                                  (eq (support-link-rule L) rule)))
                                   (support-links node)))
         (let* ((new? (null (support-links node)))
                   (reason-strength
                     (cond ((keywordp rule) 1.0)
                               ((numberp (reason-strength rule)) (reason-strength rule))
                              (t (let ((r (funcall (reason-strength rule) binding basis)))
                                     (if (>= r 0) r 0)))))
                   (link (make-support-link
                            :support-link-number *support-link-number*
                            :support-link-basis basis
                            :support-link-clues clues
                            :support-link-rule rule
                            :support-link-target node
                            :defeasible? defeasible?
                            :temporal-link
                            (if (or (and (not (keywordp rule)) (temporal? rule))
                                      (some #'temporal-node basis)) *cycle*)
                            :support-link-reason-strength  reason-strength
                            :support-link-binding binding
                            :support-link-discount-factor
                            (cond (discount discount)
                                      ((not (keywordp rule)) (discount-factor rule))
                                      (t 1.0))
                            :support-link-nearest-defeasible-ancestors
                            (if defeasible? (list (list node)) NDA)
                            :generating-interest-link link))
                   (ancestors (union basis (unionmapcar+ #'node-ancestors basis))))
           (when (or (not (member nil NDA))
                             (non-circular (node-sequent node) ancestors))  ;; this is a circularity test
                (dolist (n basis) (push link (consequent-links n)))
                (if (null (temporal-node node)) (setf (temporal-node node) (temporal-link link)))
                (add-support-link link node depth)
                (push link *support-links*)
                (if *log-on* (push node *reasoning-log*))
               (when (and (not defeasible?) basis (every #'background-knowledge basis))
                    (setf (background-knowledge node) t))
                (let ((old-NDA (nearest-defeasible-ancestors node)))
                  (cond (defeasible?
                                (pushnew (list node) (nearest-defeasible-ancestors node) :test 'equal))
                            (t
                              (dolist (X NDA)
                                  (when
                                       (not (some #'(lambda (Y) (subsetp Y X))
                                                           (nearest-defeasible-ancestors node)))
                                       (dolist (Y (nearest-defeasible-ancestors node))
                                           (when (subsetp X Y) (pull Y (nearest-defeasible-ancestors node))))
                                       (push X (nearest-defeasible-ancestors node))))))
                  (when (not new?)
                       (dolist (X (nearest-defeasible-ancestors node))
                           (invert-contradictions-retrospectively node X old-NDA))))
                (recursively-compute-nearest-defeasible-ancestors node)
                (setf (node-ancestors node) (union ancestors (node-ancestors node)))
                (recursively-compute-node-ancestors node ancestors)
                (when (not new?) (invert-contradictions-from-new-support-link link instantiations))
                link))))

(defunction non-circular (sequent ancestors)
    (every
      #'(lambda (b)
            (or (not (is-inference b))
                  (not (subsumes (node-sequent b) sequent))))
      ancestors))

(defunction recursively-compute-node-ancestors (node ancestors)
    (dolist (L (consequent-links node))
        (let* ((target (support-link-target L))
                  (new-ancestors (set-difference ancestors (node-ancestors target))))
           (when new-ancestors
                (setf (node-ancestors target) (union new-ancestors (node-ancestors target)))
                (recursively-compute-node-ancestors target new-ancestors)))))

(defunction recursively-compute-nearest-defeasible-ancestors
    (node &optional nodes-done)
    (push node nodes-done)
    (dolist (L (consequent-links node))
        (when (not (defeasible? L))
             (let ((NDA
                       (mapcar #'genunion
                                      (gencrossproduct
                                        (mapcar #'nearest-defeasible-ancestors (support-link-basis L)))))
                     (target (support-link-target L)))
                (let ((old-NDA (nearest-defeasible-ancestors node)))
                   (dolist (X NDA)
                       (when
                            (not (some #'(lambda (Y) (subsetp Y X))
                                                 (nearest-defeasible-ancestors target)))
                            (dolist (Y (nearest-defeasible-ancestors target))
                                (when (subsetp X Y) (pull Y (nearest-defeasible-ancestors target))))
                            (push X (nearest-defeasible-ancestors target))
                            (invert-contradictions-retrospectively node X old-NDA))))
                (when (not (member target nodes-done))
                     (recursively-compute-nearest-defeasible-ancestors target nodes-done))))))

(defunction add-support-link (link node depth)
    ; (setf l link n node d depth)
    ; (when (eq link (support-link 11)) (setf l link n node d depth) (break))
    ;; (step (add-support-link l n d))
    (push link (support-links node))
    (let ((degree-of-support
              (minimum (cons (support-link-reason-strength link)
                                          (mapcar #'compute-maximal-degree-of-support (support-link-basis link))))))
      (cond ((and (temporal-link link) (not (eql (temporal-node node) *cycle*)))
                  (let* ((decay (expt *temporal-decay* (- *cycle* (temporal-node node))))
                            (old-degree (adjust-for-decay (maximal-degree-of-support node) decay)))
                    (when (> degree-of-support old-degree)
                         (setf (maximal-degree-of-support node) degree-of-support)
                         (setf (temporal-node node) *cycle*)
                         (adjust-support-for-consequences node old-degree depth))))
                (t
                  (let ((old-degree (maximal-degree-of-support node)))
                    (when (> degree-of-support old-degree)
                         (setf (maximal-degree-of-support node) degree-of-support)
                         (adjust-support-for-consequences node old-degree depth)))))))

(defunction adjust-support-for-consequences (node old-degree depth)
   ; (setf n node o old-degree d depth)
    ;; (step (adjust-support-for-consequences n o d))
    (when *trace* (indent depth) (princ "ADJUST-SUPPORT-FOR-CONSEQUENCES for ")
                 (princ node) (terpri))
    (dolist (L (consequent-links node))
        (let ((n (support-link-target L)))
          (cond ((temporal-node node)
                      (let* ((decay (expt *temporal-decay* (- *cycle* (temporal-node n))))
                                (adjusted-old-degree (adjust-for-decay old-degree decay)))
                        (when (>< adjusted-old-degree (maximal-degree-of-support n))
                             (let* ((temp
                                         (or (eq (support-link-rule L) *temporal-projection*)
                                               (eq (support-link-rule L) *causal-implication*)
                                               (and (not (keywordp (support-link-rule L)))
                                                        (temporal? (support-link-rule L)))))
                                       (degree-of-support
                                         (if temp
                                           (* (adjust-for-decay (support-link-reason-strength L) decay)
                                                (minimum
                                                  (mapcar #'maximal-degree-of-support (support-link-basis L))))
                                           (adjust-for-decay
                                             (minimum
                                               (cons (support-link-reason-strength L)
                                                         (mapcar #'maximal-degree-of-support (support-link-basis L))))
                                             decay))))
                               (when (> degree-of-support adjusted-old-degree)
                                    (setf (maximal-degree-of-support n) degree-of-support)
                                    (dolist (L (support-links node))
                                        (setf (support-link-strength L) (adjust-for-decay (support-link-strength L) decay))
                                        (when (and (not (keywordp (support-link-rule L))) (temporal? (support-link-rule L)))
                                             (setf (support-link-reason-strength L)
                                                      (adjust-for-decay (support-link-reason-strength L) decay)))
                                        (setf (temporal-link L) *cycle*))
                                    (setf (temporal-node n) *cycle*)
                                    (setf (temporal-link L) *cycle*)
                                    (let ((i-lists (corresponding-i-lists (node-c-list n))))
                                      (discharge-interest-in-defeaters n i-lists old-degree nil)
                                      (discharge-interest-in n i-lists old-degree (1+ depth) nil nil)
                                      (when (processed? N)
                                           (discharge-interest-schemes N old-degree (1+ depth)))
                                      (when *use-reductio*
                                           (cond ((node-queue-node n)
                                                       (discharge-immediate-reductios n old-degree nil (1+ depth) nil nil))
                                                     (t (discharge-reductios n old-degree (1+ depth) nil)))))
                                    (adjust-support-for-consequences n old-degree depth))))))
                    ((eql (maximal-degree-of-support n) old-degree)
                      (let ((degree-of-support
                                (maximum
                                  (cons (support-link-reason-strength L)
                                            (mapcar #'maximal-degree-of-support (support-link-basis L))))))
                        (when (> degree-of-support old-degree)
                             (setf (maximal-degree-of-support node) degree-of-support)
                             (let ((i-lists (corresponding-i-lists (node-c-list n))))
                               (discharge-interest-in-defeaters n i-lists old-degree nil)
                               (discharge-interest-in n i-lists old-degree (1+ depth) nil nil)
                               (when (processed? N)
                                    (discharge-interest-schemes N old-degree (1+ depth)))
                               (when *use-reductio*
                                    (cond ((node-queue-node n)
                                                (discharge-immediate-reductios n old-degree nil (1+ depth) nil nil))
                                              (t (discharge-reductios n old-degree (1+ depth) nil)))))
                             (adjust-support-for-consequences n old-degree depth))))))))

;(defunction inference-descendants (N)
;    (let ((consequences (node-consequences N)))
;       (union consequences (unionmapcar+ #'inference-descendants consequences))))

#| Reductio-interests are started when the first reductio-supposition is made, and
reductio-interests in the negations of reductio-suppositions are adopted when the
suppositions are made.  Other direct-reductio-interests are adopted when the
generating nodes are retrieved from the inference-queue. |#
(defunction START-REDUCTIO-INTERESTS (node depth interests)
    ; (when (equal node (node 7)) (setf c node d depth i interests) (break))
    ;; (step (start-reductio-interests c d i))
    (when *trace* (indent depth) (princ "ADOPT-REDUCTIO-INTEREST-FROM: ")
                 (princ node) (terpri))
    (let ((start-interests (null *reductio-supposition-nodes*)))
       (push node *reductio-supposition-nodes*)
       (when start-interests
            (when *trace* (indent (1+ depth)) (princ "INITIATING-REDUCTIO-INTERESTS") (terpri))
            (dolist (dn *discrimination-net*)
                 (dolist (cl (d-node-c-lists dn))
                    (when  (reductio-interests cl)
                         (dolist (C (c-list-processed-nodes cl))
                      (when
                           (and (deductive-node C)
                           (or
                             (null (enabling-interests C))
                             (some #'(lambda (in) (not (cancelled-interest in))) (enabling-interests C))))
                                  (generate-reductio-interests C (1+ depth) interests)))))))
       (when (reductio-interests (node-c-list node))
            (generate-reductio-interests node depth interests))))

(defunction ADOPT-REDUCTIO-INTEREST (node depth d-interests)
   ; (when (equal *interest-number* 44) (setf n node d depth di d-interests))
    ;; (step (adopt-reductio-interest n d di))
    (let ((enabling-interests (enabling-interests node)))
       (when
            (and
              *reductio-supposition-nodes*
           (deductive-node node)
              (not (eq (node-justification node) :reductio-supposition))
              (reductio-interests (node-c-list node))
              (or (null enabling-interests)
                      (some #'(lambda (in) (not (cancelled-interest in))) enabling-interests)))
            (generate-reductio-interests node depth d-interests))))

(defunction generate-reductio-interests (node depth d-interests)
    ; (setf n node d depth di d-interests)
    ; (when (eq node (node 54)) (setf n node d depth di d-interests) (break))
    ;; (step (generate-reductio-interests n d di))
    (multiple-value-bind
         (sequent vars substitution)
         (convert-conclusion-variables
           (list (domain (non-reductio-supposition node)) (neg (node-formula node))) (node-variables node))
         (let ((P (sequent-formula sequent))
                 (sup (sequent-supposition sequent)))
           (multiple-value-bind
                (interest i-list match)
                (interest-for sequent vars nil nil)
                (let* ((interests (unionmapcar #'generating-interests *reductio-supposition-nodes*))
                          (degree (maximum (mapcar #'degree-of-interest interests)))
                          (priority
                            (* *reductio-interest*
                                 (maximum
                                   (mapcar #'compute-discounted-node-strength *reductio-supposition-nodes*)))))
                  (cond ((null interest)
                              (setf interest
                                       (make-interest
                                         :interest-number (incf *interest-number*)
                                         :interest-sequent sequent
                                         :interest-formula P
                                         :interest-supposition sup
                                         :interest-variables vars
                                         :interest-supposition-variables (supposition-variables sup)
                                         :degree-of-interest degree
                                         :interest-priority priority
                                         :maximum-degree-of-interest degree
                                         :reductio-interest t
                                         :direct-reductio-interest (list (cons node substitution))
                                         :non-reductio-interest nil
                                         ))
                              (push interest (generated-direct-reductio-interests node))
                              (if i-list
                                (store-interest interest i-list)
                                (let ((c-lists (c-list-contradictors (node-c-list node))))
                                  (setf c-lists
                                           (mapcar
                                             #'(lambda (cl)
                                                   (cons (car cl) (match-sublis substitution (cdr cl))))
                                             c-lists))
                                  (store-interest-with-c-lists interest c-lists)))
                              (when *display?*
                                   (display-interest interest) (princ "                                        ")
                                   (princ "using node ") (princ (inference-number node)) (terpri))
                              (when *log-on* (push interest *reasoning-log*))
                              (when (and *display?* *graphics-on* *graph-interests*) (draw-i interest *og*))
                              (queue-interest interest priority)
                              (push interest *direct-reductio-interests*))
                            (t
                              (let ((direct-reductio-interest (direct-reductio-interest interest)))
                                (pushnew (cons node (merge-matches* substitution match)) (direct-reductio-interest interest))
                                (pushnew interest (generated-direct-reductio-interests node))
                                (when (not direct-reductio-interest)
                                     (push interest *direct-reductio-interests*)
                                     (setf (interest-priority interest) (max (interest-priority interest) priority))
                                     (change-to-reductio-interest interest depth d-interests)
                                     (setf (degree-of-interest interest) (max (degree-of-interest interest) degree))))
                              (readopt-interest interest nil))))))))

(defunction rewrite-u-vars (formula vars)
    (if vars
       (let ((a-list (mapcar #'(lambda (v) (cons v (make-interest-variable))) vars)))
          (list (sublis a-list formula) a-list))
       (list formula t)))

(defunction change-to-reductio-interest (interest depth d-interests)
   ; (when (equal interest (interest 6)) (break))
    (when (not (reductio-interest interest))
         (setf (reductio-interest interest) t)
         (discharge-new-reductio-interest interest (1+ depth) d-interests)
         (dolist (L (left-links interest))
             (change-to-reductio-interest (link-interest L) depth d-interests))))

#| This assumes that N is a reductio-supposition-node. |#
(defunction base-reductio-supposition (N)
    (not (some #'reductio-interest (generating-interests N))))

#| This assumes that N is a reductio-supposition-node.  The second conjunct could be
made more efficient by storing the appropriate information in a slot
non-reductio-generating-interests. |#
(defunction strictly-base-reductio-supposition (N)
    (and
      (not (some #'reductio-interest (generating-interests N)))
      (every #'(lambda (in) (equal (node-formula N) (neg (interest-formula in))))
                   (generating-interests N))))

(defunction merge-unifiers* (u1 u2)
    (list (merge-matches* (mem1 u1) (mem1 u2))
            (merge-matches* (mem2 u1) (mem2 u2))))

;(defunction discharge-fortuitous-reductios (node d-interests depth)
;    ; (when (eq node (node 399)) (setf n node di d-interests d depth) (break))
;    ;; (step (discharge-fortuitous-reductios n di d))
;    (dolist (nl (c-list-contradictors (node-c-list node)))
;        (let* ((unifier (mem2 nl))
;                  (unifier* (list (mem2 unifier) (mem1 unifier))))
;           (dolist (node* (c-list-nodes (mem1 nl)))
;               (when (and (null (node-supposition node))
;                                     (null (node-supposition node*))
;                                     (deductive-node node)
;                                     (deductive-node node*))
;                    (dolist (Q *ultimate-epistemic-interests*)
;                        (let ((in (query-interest Q)))
;                           (draw-conclusion
;                             (match-sublis (mem1 unifier) (interest-formula in))
;                             (list node node*) :fortuitous-reductio unifier 1 (1+ depth) d-interests))))
;               (when
;                    (and
;                      (some
;                        #'(lambda (sup)
;                              (some
;                                #'(lambda (in) (not (assoc in (discharged-interests node))))
;                                (generated-interests (cdr sup))))
;                        (non-reductio-supposition node*))
;                      (appropriately-related-node-suppositions node node* unifier))
;                    (dolist (sup (non-reductio-supposition node*))
;                        (let ((sup-node (cdr sup)))
;                           (when (deductive-in node* sup-node)
;                                (dolist (in (generated-interests sup-node))
;                                    (when (appropriately-related-suppositions node in '(t t))
;                                         (draw-conclusion
;                                           (match-sublis (mem1 unifier) (interest-formula in))
;                                           (list node node*) :fortuitous-reductio unifier 1 (1+ depth) d-interests)))))))
;               (when
;                    (and
;                      (some
;                        #'(lambda (sup)
;                              (some
;                                #'(lambda (in) (not (assoc in (discharged-interests node))))
;                                (generated-interests (cdr sup))))
;                        (non-reductio-supposition node))
;                      (appropriately-related-node-suppositions node* node unifier*))
;                    (dolist (sup (non-reductio-supposition node))
;                        (let ((sup-node (cdr sup)))
;                           (when (deductive-in node sup-node)
;                                (dolist (in (generated-interests sup-node))
;                                    (when (appropriately-related-suppositions node in '(t t))
;                                         (draw-conclusion
;                                           (match-sublis (mem1 unifier*) (interest-formula in))
;                                           (list node* node) :fortuitous-reductio unifier* 1 (1+ depth) d-interests)))))))
;               ))))

(defunction discharge-fortuitous-reductios (node d-interests depth)
    ; (when (eq node (node 4)) (setf n node di d-interests d depth) (break))
    ;; (step (discharge-fortuitous-reductios n di d))
    (dolist (nl (c-list-contradictors (node-c-list node)))
        (let ((unifier (mem2 nl)))
           (dolist (node* (c-list-nodes (mem1 nl)))
               (when (and (null (node-supposition node))
                                     (null (node-supposition node*))
                                     (deductive-node node)
                                     (deductive-node node*))
                    (dolist (Q *ultimate-epistemic-interests*)
                        (let ((in (query-interest Q)))
                           (draw-conclusion
                             (match-sublis (mem1 unifier) (interest-formula in))
                             (list node node*) :fortuitous-reductio unifier 1 (1+ depth) d-interests nil))))
               (let ((nodes nil))
                 (dolist (n (reductio-ancestors node)) (pushnew (cdr n) nodes))
                 (dolist (n (non-reductio-supposition node)) (pushnew (cdr n) nodes))
                 (dolist (n (reductio-ancestors node*)) (pushnew (cdr n) nodes))
                 (dolist (n (non-reductio-supposition node*)) (pushnew (cdr n) nodes))
                 (dolist (n nodes)
                     (dolist (interest (generated-interests n))
                         (when (subsetp nodes (interest-supposition-nodes interest))
                              (draw-conclusion
                                (interest-formula interest) (list node node*) :discharge-fortuitous-reductios
                                unifier 1 (1+ depth) d-interests nil)))))))))

(defunction discharge-fortuitous-reductio-interests (interest depth)
   ; (when (eq interest (interest 88)) (setf i interest d depth) (break))
    ;; (step (discharge-fortuitous-reductio-interests i d))
    (when *trace* (indent depth) (princ "DISCHARGE-FORTUITOUS-REDUCTIO-INTERESTS: ")
                 (princ interest) (terpri))
    (when (reductio-interest interest)
         (dolist (n (interest-supposition-nodes interest))
             (when (deductive-node n)
                  (dolist (c (c-list-contradictors (node-c-list n)))
                      (let ((cl (car c))
                              (u (cadr c)))
                        (dolist (n* (c-list-nodes cl))
                            (when (eq (node-justification n*) :reductio-supposition)
                                 (draw-conclusion
                                   (interest-formula interest) (list n* n) :fortuitous-reductio u 1.0 depth nil nil)))))))))

(defunction base-test (R RA)
    (or (not (base-reductio-supposition (cdr R)))
          (every #'(lambda (x) (or (eq x R) (non-reductio-supposition? (cdr x)))) RA)))

(defunction discharge-immediate-reductios
    (node old-degree new? depth d-interests d-interest)
    ; (when (eq node (node 6)) (setf c node o old-degree n new? d depth di d-interests di* d-interest) (break))
    ;(setf c node o old-degree n new? d depth di d-interests di* d-interest)
    ;; (step (discharge-immediate-reductios c o n d di di*))
    (when *trace* (indent depth) (princ "DISCHARGE-IMMEDIATE-REDUCTIOS-FROM ")
                (princ node) (terpri))
    (when
         (and
           (<= (length (setdifference (node-supposition node) *skolem-free-suppositions*)) 1)
           (not (member d-interest d-interests)))
         (setf (reductios-discharged node) t)
         (let ((reductio-ancestors (reductio-ancestors node))
                 (Y0 (node-supposition node)))
           (discharge-fortuitous-reductios node d-interests (1+ depth))
           (dolist (il (discharged-interests node))
               (let* ((interest (mem1 il))
                         (direct-reductio-interest (direct-reductio-interest interest))
                         (unifier (mem2 il))  ;; this unifies node with interest
                         (unifiers
                           (if (mem3 il)
                             (mem3 il)
                             (appropriately-related-suppositions node interest unifier)))
                         (Y1 (remove-duplicates= (match-sublis (mem1 unifier) Y0))))
                 (when (or  (eq interest d-interest)
                                    (and
                                      (not (member interest d-interests))
                                      (or new?
                                            (> (maximum-degree-of-interest interest) old-degree))
                                      (<= (degree-of-interest interest)
                                             (compute-maximal-degree-of-support node))))
                      (dolist (dr direct-reductio-interest)
                          (let ((node* (car dr))
                                  (match (cdr dr)))
                            (when (cancelled-node node) (return-from discharge-immediate-reductios))
                            ;; to use unifier we must first transform node* to make it like interest
                            (let ((Y*0 (remove-duplicates=
                                              (match-sublis
                                                (mem2 unifier)
                                                (match-sublis
                                                  match (node-supposition node*))))))
                              (dolist (u unifiers)
                                  (let ((unifier* (merge-unifiers* unifier u))
                                          (Y (remove-duplicates= (match-sublis (mem1 u) Y1)))
                                          (Y* (remove-duplicates= (match-sublis (mem2 u) Y*0))))
                                    (let ((RA (union=
                                                     (mapcar
                                                       #'(lambda (x)
                                                             (cons
                                                               (match-sublis
                                                                 (mem1 unifier*)
                                                                 (car x)) (cdr x)))
                                                       reductio-ancestors)
                                                     (mapcar
                                                       #'(lambda (x)
                                                             (cons (match-sublis
                                                                        (mem2 unifier*)
                                                                        (match-sublis match (car x))) (cdr x)))
                                                       (reductio-ancestors node*))))
                                            (NR (union=
                                                    (mapcar
                                                      #'(lambda (x)
                                                            (cons
                                                              (match-sublis
                                                                (mem1 unifier*)
                                                                (car x)) (cdr x)))
                                                      (non-reductio-supposition node))
                                                    (mapcar
                                                      #'(lambda (x)
                                                             (cons (match-sublis
                                                                        (mem2 unifier*)
                                                                        (match-sublis match (car x))) (cdr x)))
                                                      (non-reductio-supposition node*)))))
                                      (dolist (R RA)
                                          (when (base-test R RA)
                                               (let ((P (car R)))
                                                 (draw-reductio-conclusion
                                                   P node node* R Y Y* RA NR interest unifier* (1+ depth)
                                       (cons d-interest d-interests)))))))))))))))))

(defunction discharge-delayed-reductios (node depth d-interests)
    (when *trace* (indent depth) (princ "DISCHARGE-DELAYED-REDUCTIOS-FROM ")
                (princ node) (terpri))
    ; (when (eq node (node 3)) (setf n node d depth di d-interests) (break))
    ;; (step (discharge-delayed-reductios n d di))
    (when
         (not (reductios-discharged node))
         (setf (reductios-discharged node) t)
         (let ((reductio-ancestors (reductio-ancestors node))
                 (Y0 (node-supposition node)))
           (discharge-fortuitous-reductios node d-interests (1+ depth))
           (dolist (il (discharged-interests node))
               (let* ((interest (mem1 il))
                         (direct-reductio-interest (direct-reductio-interest interest))
                         (unifier (mem2 il))
                         (unifiers
                           (if (mem3 il)
                             (mem3 il)
                             (appropriately-related-suppositions node interest unifier)))
                         (Y1 (remove-duplicates= (match-sublis (mem1 unifier) Y0))))
                 (when (<= (degree-of-interest interest)
                                    (compute-maximal-degree-of-support node))
                      (dolist (dr direct-reductio-interest)
                          (let ((node* (car dr))
                                  (match (cdr dr)))
                            (when (cancelled-node node) (return-from discharge-delayed-reductios))
                            (let ((Y*0 (remove-duplicates=
                                              (match-sublis
                                                (mem2 unifier)
                                                (match-sublis
                                                  match (node-supposition node*))))))
                              (dolist (u unifiers)
                                  (let ((unifier* (merge-unifiers* unifier u))
                                          (Y (remove-duplicates=
                                                (match-sublis (mem1 u) Y1)))
                                          (Y* (remove-duplicates= (match-sublis (mem2 u) Y*0))))
                           ; (when (and
                           ;               (not (some #'(lambda (f) (mem (neg f) Y)) Y))
                           ;               (not (some #'(lambda (f) (mem (neg f) Y*)) Y*))
                           ;               (not (some #'(lambda (f) (mem (neg f) Y)) Y*)))
                                    (let ((RA (union=
                                                     (mapcar
                                                       #'(lambda (x)
                                                             (cons
                                                               (match-sublis
                                                                 (mem1 unifier*)
                                                                 (car x)) (cdr x)))
                                                       reductio-ancestors)
                                                     (mapcar
                                                       #'(lambda (x)
                                                             (cons (match-sublis
                                                                        (mem2 unifier*)
                                                                        (match-sublis match (car x))) (cdr x)))
                                                       (reductio-ancestors node*))))
                                            (NR (union=
                                                    (mapcar
                                                      #'(lambda (x)
                                                            (cons
                                                              (match-sublis
                                                                (mem1 unifier*)
                                                                (car x)) (cdr x)))
                                                      (non-reductio-supposition node))
                                                    (mapcar
                                                      #'(lambda (x)
                                                            (cons (match-sublis
                                                                       (mem2 unifier*)
                                                                       (match-sublis match (car x))) (cdr x)))
                                                      (non-reductio-supposition node*)))))
                                      (dolist (R RA)
                                          (when (base-test R RA)
                                               (let ((P (car R)))
                                                 (draw-reductio-conclusion
                                                   P node node* R Y Y* RA NR interest unifier* (1+ depth)
                                                   d-interests))))))))))))))))  ;)

(defunction discharge-new-reductio-interest (interest depth d-interests)
    (when *trace* (indent depth) (princ "DISCHARGE-NEW-REDUCTIO-INTEREST from ")
                (princ interest) (terpri))
    ; (when (equal interest (interest 6)) (break))
    (dolist (corresponding-c-list (corresponding-c-lists (interest-i-list interest)))
        (let* ((c-list (mem1 corresponding-c-list))
                  (unifier (mem2 corresponding-c-list))
                  (i-sup (match-sublis (mem2 unifier) (interest-supposition interest))))
          (dolist (node (c-list-nodes c-list))
              (let ((degree (compute-maximal-degree-of-support node))
                      (deductive? (deductive-node node)))
                (when (and
                             (or deductive? (not (deductive-interest interest)))
                             (<= (degree-of-interest interest) degree)
                             (not (subsetp=
                                       (match-sublis (mem1 unifier) (node-supposition node))
                                       i-sup)))
                     (let* ((unifiers (appropriately-related-suppositions node interest unifier))
                               (new-vars
                                 (mapcar #'(lambda (v) (cons v (make-interest-variable)))
                                                (intersection (c-list-variables c-list)
                                                                      (set-difference (node-supposition-variables node)
                                                                                                (node-variables node)))))
                               (Y1 (remove-duplicates=
                                       (match-sublis
                                         (mem1 unifier) (sublis new-vars (node-supposition node))))))
                       (dolist (dr (direct-reductio-interest interest))
                           (let ((node* (car dr))
                                   (match (cdr dr)))
                             (when (cancelled-interest interest)
                                  (return-from discharge-new-reductio-interest))
                             (let* ((new-vars
                                         (mapcar #'(lambda (v) (cons v (make-interest-variable)))
                                                        (intersection (node-variables node)
                                                                              (set-difference (node-supposition-variables node*)
                                                                                                        (node-variables node*)))))
                                       (Y*0 (remove-duplicates=
                                                 (match-sublis
                                                   (mem2 unifier)
                                                   (match-sublis
                                                     match
                                                     (sublis new-vars (node-supposition node*)))))))
                               (dolist (u unifiers)
                                   (let ((unifier* (merge-unifiers* unifier u))
                                           (Y (remove-duplicates=
                                                 (match-sublis (mem1 u) Y1)))
                                           (Y* (remove-duplicates= (match-sublis (mem2 u) Y*0))))
                                     (let ((RA (union=
                                                      (mapcar
                                                        #'(lambda (x)
                                                              (cons
                                                                (match-sublis
                                                                  (mem1 unifier*)
                                                                  (car x)) (cdr x)))
                                                         (reductio-ancestors node))
                                                      (mapcar
                                                        #'(lambda (x)
                                                              (cons (match-sublis
                                                                         (mem2 unifier*)
                                                                         (match-sublis match (car x))) (cdr x)))
                                                        (reductio-ancestors node*))))
                                             (NR (union=
                                                     (mapcar
                                                       #'(lambda (x)
                                                             (cons
                                                               (match-sublis
                                                                 (mem1 unifier*)
                                                                 (car x)) (cdr x)))
                                                       (non-reductio-supposition node))
                                                     (mapcar
                                                       #'(lambda (x)
                                                             (cons (match-sublis
                                                                        (mem2 unifier*)
                                                                        (match-sublis match (car x))) (cdr x)))
                                                       (non-reductio-supposition node*)))))
                                       (dolist (R RA)
                                           (when (base-test R RA)
                                                (let ((P (car R)))
                                                  (draw-reductio-conclusion
                                                    P node node* R Y Y* RA NR interest unifier*
                                                    (1+ depth) (cons interest d-interests)))))
                                       )))))))))))))

(defunction discharge-reductios (node old-degree depth d-interests)
    (when *trace* (indent depth) (princ "DISCHARGE-REDUCTIOS-FROM ")
                 (princ node) (terpri))
    (when
         (not (some
                   #'(lambda (il) (member (mem1 il) d-interests))
                   (discharged-interests node)))
         (setf (reductios-discharged node) t)
         (let ((reductio-ancestors (reductio-ancestors node))
                 (Y0 (node-supposition node)))
            (discharge-fortuitous-reductios node d-interests (1+ depth))
            (dolist (il (discharged-interests node))
                 (let* ((interest (mem1 il))
                             (direct-reductio-interest (direct-reductio-interest interest))
                             (unifier (mem2 il))
                             (unifiers (mem3 il))
                             ;; rewrite supposition-variables to avoid collision with formula-variables
                             (new-vars
                               (mapcar #'(lambda (v) (cons v (make-interest-variable)))
                                                  (intersection (interest-variables interest)
                                                                              (set-difference (node-supposition-variables node)
                                                                                                         (node-variables node)))))
                             (Y1 (remove-duplicates=
                                       (match-sublis (mem1 unifier) (sublis new-vars Y0)))))
                   ; (when new-vars (break))
                    (when (and
                                  (setdifference (interest-supposition interest)
                                                            *skolem-free-suppositions*)
                                  (> (maximum-degree-of-interest interest) old-degree)
                                  (<= (degree-of-interest interest)
                                         (compute-maximal-degree-of-support node)))
                         (dolist (dr direct-reductio-interest)
                      (let ((node* (car dr))
                              (match (cdr dr)))
                             (when (cancelled-node node) (return-from discharge-reductios))
                             (let ((Y*0 (remove-duplicates=
                                    (match-sublis
                                                  (mem2 unifier)
                                                  (match-sublis
                                       match (node-supposition node*))))))
                                (dolist (u unifiers)
                                    (let ((unifier* (merge-unifiers* unifier u))
                                            (Y (remove-duplicates=
                                      (match-sublis (mem1 u) Y1)))
                                            (Y* (remove-duplicates= (match-sublis (mem2 u) Y*0))))
                                            (let ((RA (union=
                                                     (mapcar
                                                       #'(lambda (x)
                                                             (cons
                                                               (match-sublis
                                                                 (mem1 unifier*)
                                                                 (car x)) (cdr x)))
                                                       reductio-ancestors)
                                                     (mapcar
                                                       #'(lambda (x)
                                                             (cons (match-sublis
                                                                        (mem2 unifier*)
                                                                        (match-sublis match (car x))) (cdr x)))
                                                       (reductio-ancestors node*))))
                                            (NR (union=
                                                    (mapcar
                                                      #'(lambda (x)
                                                            (cons
                                                              (match-sublis
                                                                (mem1 unifier*)
                                                                (car x)) (cdr x)))
                                                      (non-reductio-supposition node))
                                                    (mapcar
                                                      #'(lambda (x)
                                                             (cons (match-sublis
                                                                        (mem2 unifier*)
                                                                        (match-sublis match (car x))) (cdr x)))
                                                      (non-reductio-supposition node*)))))
                                               (dolist (R RA)
                                                   (when (base-test R RA)
                                                        (let ((P (car R)))
                                                           (draw-reductio-conclusion
                                                             P node node* R Y Y* RA NR interest unifier* (1+ depth)
                                                             d-interests))))))))))))))))

#| node* is the node that generates interest, whose interest-formula is the
negation of the node-formula of node*.  This is called by GENERATE-REDUCTIO-INTERESTS. |#
(defunction DISCHARGE-RETROSPECTIVE-REDUCTIOS (node match interest depth)
   ; (when (eq interest (interest 37)) (setf n node m match i interest d depth) (break))
    ;; (step (discharge-retrospective-reductios n m i d))
    (when *trace* (indent depth) (princ "DISCHARGE-RETROSPECTIVE-REDUCTIOS-FROM ")
                 (princ node) (princ " and ") (princ interest) (terpri))
    (let* ((Y0 (match-sublis match (node-supposition node)))
              (reductio-ancestors* (reductio-ancestors node)))
       (dolist (cl (corresponding-c-lists (interest-i-list interest)))
           (let* ((c-list (mem1 cl))
                     (nodes (c-list-nodes c-list))
                     (unifier (mem2 cl))
                     (new-vars
                       (mapcar #'(lambda (v) (cons v (make-interest-variable)))
                                          (intersection (c-list-variables c-list)
                                                                      (set-difference (node-supposition-variables node)
                                                                                                       (node-variables node)))))
                     (Y*0 (remove-duplicates=
                                (match-sublis (mem2 unifier) (sublis new-vars Y0)))))
              (dolist (C nodes)
                  (when (cancelled-interest interest)
                       (return-from discharge-retrospective-reductios))
                  (when (<= (degree-of-interest interest) (compute-maximal-degree-of-support C))
                       (let* ((unifiers (appropriately-related-suppositions C interest unifier))
                                (reductio-ancestors (reductio-ancestors C))
                                (new-vars
                                  (mapcar #'(lambda (v) (cons v (make-interest-variable)))
                                                     (intersection (node-variables node)
                                                                                 (set-difference
                                                                                   (node-supposition-variables C)
                                                                                   (node-variables C)))))
                                (Y1 (remove-duplicates=
                                          (match-sublis
                                            (mem1 unifier) (sublis new-vars (node-supposition C))))))
                          (dolist (u unifiers)
                               (let ((unifier* (merge-unifiers* unifier u))
                                       (Y (remove-duplicates=
                                   (match-sublis (mem1 u) Y1)))
                                       (Y* (remove-duplicates= (match-sublis (mem2 u) Y*0))))
                                 ; (when (and
                                 ;                 (not (some #'(lambda (f) (mem (neg f) Y)) Y))
                                 ;                 (not (some #'(lambda (f) (mem (neg f) Y*)) Y*))
                                 ;                 (not (some #'(lambda (f) (mem (neg f) Y)) Y*)))
                                       (let ((RA (union=
                                                        (mapcar
                                                          #'(lambda (x)
                                                                (cons
                                                                       (match-sublis
                                                                         (mem1 unifier*)
                                                                         (car x)) (cdr x)))
                                                          reductio-ancestors)
                                                        (mapcar
                                                          #'(lambda (x)
                                                                (cons
                                                                  (match-sublis
                                                                    (mem2 unifier*)
                                                                    (match-sublis match (car x))) (cdr x)))
                                                          reductio-ancestors*)))
                                               (NR (union=
                                                         (mapcar
                                                           #'(lambda (x)
                                                                 (cons
                                                                       (match-sublis
                                                                         (mem1 unifier*)
                                                                         (car x)) (cdr x)))
                                                           (non-reductio-supposition C))
                                                         (mapcar
                                                           #'(lambda (x)
                                                                 (cons
                                                                   (match-sublis
                                                                     (mem2 unifier*)
                                                                     (match-sublis match (car x))) (cdr x)))
                                                           (non-reductio-supposition node)))))
                                          (dolist (R RA)
                                              (when (base-test R RA)
                                                   (let ((P (car R)))
                                                      (draw-reductio-conclusion
                                                        P C node R Y Y* RA NR interest unifier* (1+ depth) nil))))))))))))))   ;)

(defunction draw-reductio-conclusion (P node node* R Y Y* RA NR interest unifier depth d-interests)
    ; (when (equal *cycle* 81) (setf p1 p c1 node c2 node* r1 r y1 y y2 y* r2 ra n1 nr i interest u unifier d depth di d-interests) (break))
    ;; (step (draw-reductio-conclusion p1 c1 c2 r1 y1 y2 r2 n1 i u d di))
    (when (and (not (cancelled-node node))
                        (not (cancelled-node node*))
                        (not (mem (neg P) Y)) (not (mem (neg P) Y*))
                        (not (inconsistent-supposition (list node node*)))
                        ;; This prevents a reductio-ancestor from being instantiated in two different ways
                        (not (some
                                  #'(lambda (R)
                                        (some #'(lambda (R*)
                                                         (and (not (eq R R*))
                                                                  (eq (cdr R) (cdr R*))
                                                                  (zerop (readopted-supposition (cdr R)))))
                                                    RA))
                                  RA))
                        ;; This prevents a non-reductio-supposition from being instantiated in two different ways
                        (not (some
                                  #'(lambda (R)
                                        (some
                                          #'(lambda (R*)
                                                (and (not (eq R R*))
                                                         (eq (cdr R) (cdr R*))
                                                         (zerop (readopted-supposition (cdr R)))))
                                          NR))
                                  NR)))
         (let ((sup (remove-if-equal P (union= Y Y*))))
           (when (not (some #'(lambda (f) (mem (neg f) sup)) sup))
               ; (setf sup (order sup #'lessp))
                (let* ((P* (neg P))
                          (sequent (list sup P*))
                          (reductio-ancestors (remove-if-equal R RA))
                          (non-reductio-supposition
                            (subset #'(lambda (S) (not (equal P (car S)))) NR))
                          (NDA
                            (mapcar #'genunion
                                           (crossproduct (nearest-defeasible-ancestors node)
                                                                   (nearest-defeasible-ancestors node*))))
                          (d-node (d-node-for P*))
                          (c-list (if d-node (fetch-c-list-for P* d-node)))
                          (nodes (if c-list (c-list-nodes c-list)))
                          (N-conclusion
                            (find-if #'(lambda (c)
                                              (and (eq (node-kind c) :inference)
                                                       (== (node-supposition c) sup)
                                                       (== (reductio-ancestors c) reductio-ancestors)
                                                       (== (non-reductio-supposition c) non-reductio-supposition)))
                                        nodes))
                          (new-node? (null N-conclusion)))
                  (when
                       (or (null d-node)
                             (not (subsumed N-conclusion (list node node*) sequent NDA
                                                        non-reductio-supposition :reductio nil d-node)))
                       (pushnew node (discharging-nodes interest))
                       (when (null N-conclusion)
                            (setf N-conclusion
                                     (make-new-conclusion
                                       sequent reductio-ancestors reductio-ancestors non-reductio-supposition)))
                       (let ((old-degree (compute-maximal-degree-of-support N-conclusion))
                               (support-link
                                 (build-support-link
                                   (list node node*) nil :reductio 1.0 N-conclusion NDA nil nil unifier depth nil)))
                         (cond
                           ((null support-link)
                             (decf *support-link-number*)
                             (when new-node? (decf *inference-number*)))
                           (t
                             (when new-node?
                                  (push N-conclusion *inference-graph*)
                                  (store-inference-node-with-c-list
                                    N-conclusion (sequent-formula sequent) c-list))
                            ; (when R
                            ;      (setf (enabling-interests N-conclusion)
                            ;               (union (enabling-interests N-conclusion)
                            ;                          (generating-interests (cdr R)))))
                             (when *trace* (indent depth)
                                         (princ "draw-reductio-conclusion: ")
                                         (princ N-conclusion) (terpri))
                             (when *display?* (display-support-link support-link))
                             (when (read-char-no-hang) (clear-input) (throw 'die nil))
                             (let ((i-lists (corresponding-i-lists (node-c-list N-conclusion)))
                                     (increased-justification?
                                       (or new-node? (> (compute-maximal-degree-of-support node) old-degree))))
                               (when increased-justification?
                                    (discharge-interest-in-defeaters
                                      N-conclusion i-lists old-degree new-node?))
                               (push support-link *new-links*)
                               (when increased-justification?
                                    (discharge-interest-in
                                      N-conclusion i-lists old-degree new-node? (1+ depth) d-interests)
                                    (when (not (cancelled-node N-conclusion))
                                         (discharge-immediate-reductios
                                           N-conclusion old-degree new-node?
                                           (1+ depth) d-interests interest)))
                               (when new-node? (invert-contradictions node unifier (1+ depth)))
                               (cancel-subsumed-links support-link depth)
                               ))))))))))

#| The following assumes that the sequent and members of the basis share the same
sequent-supposition.  Basis is a list of conclusions. |#
(defunction adopt-interest-in-defeaters-for (link instantiations &optional bindings)
    ; (when (eq link (support-link 34)) (setf l link i instantiations r reason b bindings) (break))
    ;; (step (adopt-interest-in-defeaters-for l i r b))
    (cond ((defeasible? link)
                (let ((variables nil)
                        (reverse-binding nil)
                        (reverse-binding* nil)
                        (binding* nil))
                  (dolist (b bindings)
                      (cond ((or (and (listp (cdr b)) (skolem-function (mem1 (cdr b))))
                                       (skolem-function (cdr b))
                                       (conclusion-variable (cdr b))
                                       )
                                  (push (car b) variables)
                                  (push (cons (cdr b) (car b)) reverse-binding)
                                  (push (cons (cdr b) (make-interest-variable)) reverse-binding*))
                                (t (push b binding*))))
                  (let* ((S (node-sequent (support-link-target link)))
                            (B (support-link-basis link))
                            (supposition
                              (subset
                                #'(lambda (P)
                                      (every #'(lambda (b) (not (occur (car b) P :test 'equal))) reverse-binding))
                                (sequent-supposition S)))
                            (sup-remainder (setdifference (sequent-supposition S) supposition))
                            (antecedent (match-sublis reverse-binding sup-remainder :test 'equal))
                            (antecedent*
                              (gen-conjunction
                                (match-sublis reverse-binding* sup-remainder :test 'equal)))
                            (antecedent-variables
                              (subset #'(lambda (v) (occur v antecedent)) variables))
                            (sup
                              (if sup-remainder
                                (generalized-e-gen antecedent-variables (gen-conjunction antecedent))))
                            (new-sup (if sup (cons sup supposition) supposition))
                            (formula (match-sublis reverse-binding* (sequent-formula S)))
                            (base
                              (mapcar
                                #'(lambda (c m)
                                      (cond ((is-desire c)
                                                  (list 'I_desire_that
                                                         (match-sublis reverse-binding*
                                                                                (match-sublis m (node-formula c)))))
                                                ((is-percept c)
                                                  (let ((time (percept-date (node-justification c))))
                                                    (list 'it-appears-to-me-that
                                                           (match-sublis reverse-binding*
                                                                                  (match-sublis m (mem2 (node-formula c))))
                                                           (list 'closed time time))))
                                                (t (match-sublis reverse-binding*
                                                                           (match-sublis m (node-formula c)) :test 'equal))))
                                B instantiations)))
                    (when sup (queue-defeater-supposition sup))
                    (when base
                         (make-undercutting-defeater base formula new-sup antecedent* link reverse-binding*))
                    (make-rebutting-defeater variables base formula new-sup antecedent* link))))
              ((eq (support-link-rule link) :Q&I)
                (adopt-interest-in-Q&I-defeaters-for (node-sequent (support-link-target link))))))

(defunction make-undercutting-defeater (base formula supposition antecedent* link reverse-binding)
    ; (when (eql link 2812) (setf b base f formula s supposition a antecedent* l link rb reverse-binding) (break))
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
                                  :interest-priority *base-priority*
                                  :defeater-binding (support-link-binding link)
                                  :generating-defeat-nodes (list (support-link-target link))))
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
                                  :interest-priority *base-priority*
                                  :generating-defeat-nodes (list (support-link-target link))))
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
                       (let ((priority (defeater-priority rebutting-interest)))
                         (queue-interest
                           rebutting-interest priority)
                         (apply-degenerate-backwards-reasons rebutting-interest priority 0)))
                     (t
                       (readopt-interest rebutting-interest (list link))
                       (push rebutting-interest (generated-defeat-interests (support-link-target link)))
                       (push (support-link-target link) (generating-defeat-nodes rebutting-interest))
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

(defunction instantiate-defeater (undercutting-interest defeater antecedent* link reverse-binding)
    ;(setf u undercutting-interest d defeater a antecedent* l link r reverse-binding)
    ;; (step (instantiate-defeater u d a l r))
    (let ((binding (match-sublis reverse-binding (support-link-binding link) :test 'equal)))
      (cond
        (antecedent*
          (let*
            ((i-link
               (construct-initial-interest-link
                 nil nil adjunction undercutting-interest 0 *base-priority*
                 (list (cons 'p defeater) (cons 'q antecedent*)) (interest-supposition undercutting-interest)))
              (interest (link-interest i-link)))
            (dolist (reason (undercutting-defeaters (support-link-rule link)))
                (when (and (member reason *backwards-reasons*) (funcall* (reason-condition reason) binding))
                     (let ((supposition (interest-supposition interest)))
                       (cond
                         ((forwards-premises reason)
                           (construct-interest-scheme
                             reason nil interest binding nil (forwards-premises reason) nil 1
                             *base-priority* supposition))
                         (t (make-backwards-inference
                               reason binding interest 1 *base-priority* nil nil nil supposition))))))))
        (t
          (dolist (reason (undercutting-defeaters (support-link-rule link)))
              (when (and (member reason *backwards-reasons*) (funcall* (reason-condition reason) binding))
                   (let ((supposition (interest-supposition undercutting-interest)))
                     (cond
                       ((forwards-premises reason)
                         (construct-interest-scheme
                           reason nil undercutting-interest binding nil (forwards-premises reason) nil 1
                           *base-priority* supposition))
                       (t (make-backwards-inference
                             reason binding undercutting-interest 1 *base-priority* nil nil nil supposition))))))))))

(defunction queue-defeater-supposition (sup)
    (let ((sup-node (find-if #'(lambda (N) (equal (node-formula N) sup))
                                         *non-reductio-supposition-nodes*)))
      (cond (sup-node
                  (incf (readopted-supposition sup-node))
                  (when (deductive-only sup-node)
                       (let ((nodes (convert-from-deductive-only sup-node)))
                         (dolist (C nodes)
                             (apply-forwards-defeasible-reasons C)))))
                (t
                  (setf sup-node (subsuming-supposition sup))  ;; an inference-node
                  (cond ((null sup-node)
                              (setf sup-node
                                       (queue-non-reductio-defeater-supposition sup)))
                            ((reductio-supposition sup-node)
                              (incf (readopted-supposition sup-node))
                              (convert-reductio-supposition sup-node 1.0)))))))

(defunction queue-non-reductio-defeater-supposition (supposition)
    (when (skolem-free supposition) (push supposition *skolem-free-suppositions*))
    (let* ((sequent (list (list supposition) supposition))
              (complexity
                (max 1 (* 2 (formula-complexity supposition))))
              (node
                (make-inference-node
                  :inference-number (incf *inference-number*)
                  :node-sequent sequent
                  :node-formula supposition
                  :node-supposition (list supposition)
                  :node-kind :inference
                  :nearest-defeasible-ancestors (list nil)
                  :node-justification :supposition
                  :maximal-degree-of-support 1.0
                  :undefeated-degree-of-support 1.0
                  :discounted-node-strength 1.0
              :non-reductio-supposition? t))
              (queue-node
                (make-inference-queue-node
                  :queue-number (incf *queue-number*)
                  :enqued-item node
                  :item-kind :conclusion
                  :item-complexity complexity
                  :discounted-strength 1.0
                  :degree-of-preference (/ 1.0 complexity))))
      (setf (non-reductio-supposition node) (list (cons supposition node)))
      (setf (node-queue-node node) queue-node)
      (store-inference-node node supposition)
      (push node *inference-graph*)
      (push node *non-reductio-supposition-nodes*)
      (if *log-on* (push node *reasoning-log*))
      (setf (node-UDs *assignment-tree*) (cons (cons node 1.0) (node-UDs *assignment-tree*)))
      (setf (node-MPUDs *assignment-tree*) (cons (cons node 1.0) (node-MPUDs *assignment-tree*)))
      (when *display?* (display-unsupported-node node))
      (discharge-interest-in node (corresponding-i-lists (node-c-list node)) nil t 1 nil)
      (setf *inference-queue* (ordered-insert queue-node *inference-queue* #'i-preferred))
      (when (and *display?* *graphics-on*)
           (when *graphics-pause* (pause-graphics))
           (draw-n node *og* *nodes-displayed*) (push node *nodes-displayed*))
      node))

(defunction make-backwards-inference
    (reason binding interest depth priority supporting-nodes clues instantiations supposition
                  &optional generating-node)
    ; (when (eq *cycle* 518) (setf r reason b binding i interest d depth p priority s supporting-nodes in instantiations u supposition) (break))
    ;; (step (make-backwards-inference r b i d p s in u))
    (cond
      ((or (backwards-premises reason) (backwards-premises-function reason))
        (construct-initial-interest-link
          supporting-nodes instantiations reason interest depth priority binding supposition
          :generating-node generating-node :remaining-premises (backwards-premises reason) :clues clues))
      ((or (numberp (reason-strength reason))
             (>= (funcall (reason-strength reason) binding supporting-nodes) (degree-of-interest interest)))
        (cond
          ((conclusions-function reason)
            (dolist (P (funcall (conclusions-function reason) binding))
                (draw-conclusion
                  (car P) supporting-nodes reason instantiations (discount-factor reason) depth nil (cdr P)
                  :binding binding :clues clues)))
          (t (draw-conclusion
                (interest-formula interest) supporting-nodes reason instantiations
                (discount-factor reason) depth nil (defeasible-rule reason) :binding binding :clues clues)))
        )))

#| When a priority-interest is encountered, it is placed at the front of the inference-queue. |#
(defunction queue-interest (interest priority)
   ; (when (eq interest (interest 7)) (setf i interest p priority) (break))
    ;; (step (queue-interest i p))
    (let* ((complexity (sequent-complexity (interest-sequent interest)))
              (queue-node
                (make-inference-queue-node
                  :queue-number (incf *queue-number*)
                  :enqued-item interest
                  :item-kind :interest
                  :item-complexity complexity
                  :discounted-strength priority
                  :degree-of-preference (interest-preference priority complexity))))
       (setf (interest-queue-node interest) queue-node)
       (let ((n (interest-number interest)))
          (cond ((member n *priority-interests*)
                       (when *display?* (princ "Giving priority to interest ") (princ n) (terpri))
                       (setf *inference-queue* (cons queue-node *inference-queue*))
                       (when *display?* (display-inference-queue)))
                      (t (setf *inference-queue*
                                  (ordered-insert queue-node *inference-queue* #'i-preferred)))))
      ; (when *display?* (princ "                                        Preference = ")
      ;               (princ (float (/ (truncate (* 10000 (degree-of-preference queue-node))) 10000)))
      ;               (terpri))
       ))

#| sequent1 has the correct syntactical form to defeat an inference from basis
to sequent2. |#
(defunction defeats (sequent1 basis sequent2)
   (or (rebuts sequent1 sequent2)
          (undercuts sequent1 basis sequent2)))

(defunction rebuts (sequent1 sequent2)
   (and (equal (sequent-formula sequent1) (neg (sequent-formula sequent2)))
            (subsetp= (sequent-supposition sequent1) (sequent-supposition sequent2))))

(defunction undercuts (sequent1 basis sequent2)
   (and (equal (sequent-formula sequent1)
                         (make-@ (gen-conjunction (mapcar #'node-formula basis))
                               (sequent-formula sequent2)))
            (subsetp= (sequent-supposition sequent1) (sequent-supposition sequent2))
            (every #'(lambda (b)
                              (subsetp= (sequent-supposition sequent1) (node-supposition b)))
                        basis)))

(defunction queue-for-inference (node)
    ; (when (equal node (node 13)) (break))
    (when (not (cancelled-node node))
         (cond ((mem (inference-number node) *blocked-conclusions*)
                     (when *display?* (princ "node #") (princ (inference-number node))
                                 (princ " is a blocked node and so is not being queued.") (terpri)))
                   (t
                     (let* ((complexity (sequent-complexity (node-sequent node)))
                               (strength (compute-discounted-node-strength node))
                               (degree
                                 (if (numberp strength) (/ strength complexity)))
                               (queue-node
                                 (make-inference-queue-node
                                   :queue-number (incf *queue-number*)
                                   :enqued-item node
                                   :item-kind :conclusion
                                   :item-complexity complexity
                                   :discounted-strength (discounted-node-strength node)
                                   :degree-of-preference degree)))
                       (setf (node-queue-node node) queue-node)
                       (when degree
                            (setf *inference-queue*
                                     (ordered-insert queue-node *inference-queue* #'i-preferred)))
                       ; (when *display?* (princ "  Preference = ")
                       ;               (princ (float (/ (truncate (* 10000 (degree-of-preference queue-node))) 10000)))
                       ;               (terpri))
                       )))))

(defun adopt-interest-in-Q&I-defeaters-for (sequent)
    (declare (ignore sequent))
    T)

#| new? indicates whether the node is newly-constructed.  Old-degree
is the old maximal-degree-of-support.  |#
(defunction DISCHARGE-INTEREST-IN
    (node corresponding-i-lists old-degree new? depth interests &optional interest &key reductio-only)
   ; (when (eq node (node 671)) (setf c node i corresponding-i-lists o old-degree n new? d depth in interests i* interest)  (break))
    ;; (step (discharge-interest-in c i o n d in i*))
    (when *trace* (indent depth) (princ "DISCHARGE-INTEREST-IN: ") (princ node) (terpri))
    (let ((degree (compute-maximal-degree-of-support node)))
      (when (and (not (cancelled-node node))
                          (or new? (> degree old-degree)))
           (when
                (every
                  #'(lambda (i-list)
                        (not (some
                                  #'(lambda (N) (member N interests))
                                  (i-list-interests (mem1 i-list)))))
                  corresponding-i-lists)
                (setf (interests-discharged? node) t)
                (dolist (corresponding-i-list corresponding-i-lists)
                    (let* ((i-list (mem1 corresponding-i-list))
                              (unifier (mem2 corresponding-i-list))
                              (C-sup (match-sublis (mem1 unifier) (node-supposition node))))
                      (dolist (N (if (and interest (member interest (i-list-interests i-list)))
                                        (cons interest (remove interest (i-list-interests i-list)))
                                        (i-list-interests i-list)))
                          (when
                               (and (not (member node (discharging-nodes N)))
                                        (or (null reductio-only) (reductio-interest N))
                                        (not (member N interests))
                                        (or (eq N interest)
                                              (and
                                                (or new?
                                                      (> (maximum-degree-of-interest N) old-degree))
                                                (or (deductive-node node) (not (deductive-interest N)))
                                                (<= (degree-of-interest N) degree)
                                                (not (assoc N (discharged-interests node))))))
                               (let ((unifiers
                                         (if
                                            (or (not (direct-reductio-interest N))
                                                   (some #'(lambda (L)
                                                                    (or (eq (link-rule L) :answer)
                                                                          (not (reductio-interest (resultant-interest L)))))
                                                               (right-links N)))
                                           (appropriately-related-non-reductio-suppositions node N unifier)))
                                       (reductio-unifiers
                                         (if
                                           (or (direct-reductio-interest N)
                                                 (some #'(lambda (L)
                                                                  (and (not (eq (link-rule L) :answer))
                                                                           (reductio-interest (resultant-interest L))))
                                                             (right-links N)))
                                           (appropriately-related-reductio-suppositions node N unifier))))
                                 (when (or unifiers reductio-unifiers)
                                      (dolist (u unifiers)
                                          (let ((u* (merge-unifiers* unifier u)))
                                            (dolist (link (right-links N))
                                                (let ((spec (premise-node-specifier (link-premise link))))
                                                  (when (and (or (not (direct-reductio-interest N))
                                                                            (eq (link-rule link) :answer)
                                                                            (not (reductio-interest (resultant-interest link))))
                                                                      (funcall+
                                                                        (discharge-condition N) node unifier
                                                                        (match-sublis
                                                                          (interest-match link)
                                                                          (if spec (cons (cons spec node) (link-binding link))
                                                                               (link-binding link)))))
                                                       (push (list N unifier (append unifiers reductio-unifiers)) (discharged-interests node))
                                                       (pushnew node (discharging-nodes N))
                                                       (when *display?* (princ "  Node ") (princ (inference-number node))
                                                                   (princ " discharges interest ") (princ (interest-number N)) (terpri) (terpri))
                                                       (when *trace* (indent depth) (princ "DISCHARGE-INTEREST-IN: ")
                                                                   (princ N) (princ " from ") (princ node) (terpri))
                                                       (discharge-appropriately-related-link
                                                         link u* degree new? old-degree N node depth (cons N interests)))))))
                                      (when reductio-unifiers
                                           (push (list N unifier (append unifiers reductio-unifiers))
                                                     (discharged-interests node)))
                                      (dolist (u reductio-unifiers)
                                          (let ((u* (merge-unifiers* unifier u)))
                                            (dolist (link (right-links N))
                                                (let ((spec (premise-node-specifier (link-premise link))))
                                                  (when (and (not (eq (link-rule link) :answer))
                                                                      (reductio-interest (resultant-interest link))
                                                                      (funcall+
                                                                        (discharge-condition N) node unifier
                                                                        (match-sublis
                                                                          (interest-match link)
                                                                          (if spec (cons (cons spec node) (link-binding link))
                                                                               (link-binding link)))))
                                                       (pushnew node (discharging-nodes N))
                                                       (when *display?* (princ "  Node ") (princ (inference-number node))
                                                                   (princ " discharges interest ") (princ (interest-number N)) (terpri) (terpri))
                                                       (when *trace* (indent depth) (princ "DISCHARGE-INTEREST-IN: ")
                                                                   (princ N) (princ " from ") (princ node) (terpri))
                                                       (discharge-appropriately-related-link
                                                         link u* degree new? old-degree N node depth (cons N interests)))))))
                                      (when (and (not (cancelled-interest N))
                                                          (eq (mem2 unifier) t)
                                                          (subsetp= C-sup (interest-supposition N)))
                                           (cond ((deductive-node node)
                                                       (setf (cancelling-node N) node)
                                                       (cancel-interest-in N (if *trace* depth 0)))
                                                     (t
                                                       (dolist (sup-node (generated-suppositions N))
                                                           (when
                                                                (and
                                                                  (equal (generating-interests sup-node) (list N))
                                                                  (deductive-in node sup-node))
                                                                (cancel-node sup-node (if *trace* depth 0))))))
                                           )))))))))))

(defunction discharge-appropriately-related-link (link u* degree new? old-degree N node depth interests)
     ;(when (eq link  (link 21)) (setf l link u u* d degree nw new? od old-degree n* n nd node dp depth in interests) (break))
    ;; (step (discharge-appropriately-related-link l u d nw od n* nd dp in))
    (when *trace* (indent depth) (princ "DISCHARGE-APPROPRIATELY-RELATED-LINK: ") (princ link) (terpri))
    (let* ((degree* (degree-of-interest* (resultant-interest link)))
              (spec (premise-node-specifier (link-premise link)))
              (binding (if spec (cons (cons spec node) (link-binding link)) (link-binding link))))
      (when (and (<= degree* degree) (or new? (> (link-strength link) old-degree)))
           (setf (discharged-link link) t)
           (cond ((eq (link-rule link) :answer)
                       (when (null (node-supposition node))
                            (when (not (member node (supporting-nodes link)))
                                 (push node (supporting-nodes link))
                                 (push node (query-answers (resultant-interest link)))
                                 (pushnew (resultant-interest link) (answered-queries node))
                                 (when (deductive-node node)
                                      (when (and
                                                   (every
                                                     #'(lambda (query)
                                                           (or (eq query (resultant-interest link))
                                                                 (some #'deductive-node (query-answers query))))
                                                     *ultimate-epistemic-interests*)
                                                   (not (some
                                                             #'(lambda (Q) (eq (item-kind Q) :query))
                                                             *inference-queue*)))
                                           (setf (undefeated-degree-of-support node) 1.0)
                                           (setf (answered? (resultant-interest link)) T)
                                           (let ((deductive-links nil)
                                                   (deductive-nodes nil))
                                             (dolist (L *new-links*)
                                                 (when (deductive-node (support-link-target L))
                                                      (push L deductive-links)
                                                      (push (support-link-target L) deductive-nodes)))
                                             (dolist (N deductive-nodes) (setf (undefeated-degree-of-support N) 1.0))
                                             (dolist (L deductive-links) (setf (support-link-strength L) 1.0))
                                             (display-belief-changes
                                               *new-links*
                                               deductive-nodes
                                               nil))
                                           (dolist (instruction (positive-query-instructions (resultant-interest link)))
                                               (funcall instruction node))
                                           (when *display?*
                                                (terpri)
                                                (princ "             ALL QUERIES HAVE BEEN ANSWERED DEDUCTIVELY.")
                                                (terpri))
                                           ; (cancel-interest-in (link-interest link) 0)
                                           (throw 'die nil)))
                                 ; (record-query-answers link)
                                 )))
                     ((and (or (non-reductio-interest (resultant-interest link)) (deductive-node node))
                       (funcall+ (discharge-condition N) node u*
                                              (match-sublis (interest-match link) binding)))
                       (let
                         (;(match (interest-match link))
                           (match* (interest-reverse-match link)))
                         (setf u* (match-sublis match* u*))
                         (let* ((u1 (mem1 u*))
                                 (u2 (mem2 u*))
                                 (binding
                                   (mapcar
                                     #'(lambda (assoc)
                                           (cons (car assoc) (match-sublis u2 (cdr assoc)))) binding))
                                 (instantiations
                                   (cons u1
                                             (mapcar
                                               #'(lambda (in)
                                                     (cond ((eq in t) u2)
                                                                 (t (match-sublis u2 in))))
                                                              ; (t (cons (car in) (match-sublis u2 (cdr in))))))
                                               (link-instantiations link))))
                                 (supposition (match-sublis u2 (link-supposition link))))
                         (cond
                           ((remaining-premises link)
                             (construct-interest-link
                               link node instantiations binding (remaining-premises link) supposition
                               (degree-of-interest N) (maximum-degree-of-interest N) (1+ depth)
                               (interest-priority (resultant-interest link)) interests))
                           ((or (null (right-links (resultant-interest link)))
                                  (some #'(lambda (L) (eq (link-rule L) ug))
                                        (right-links (resultant-interest link)))
                                  (some #'(lambda (L)
                                  (funcall+ (discharge-condition (resultant-interest link)) nil (list u1 u2)
                                                            (match-sublis (interest-match link) (link-binding L))))
                                        (right-links (resultant-interest link))))
                             (cond
                               ((conclusions-function (link-rule link))
                                 (dolist (P (funcall (conclusions-function (link-rule link)) binding))
                                     (draw-conclusion
                                       (car P) (cons node (supporting-nodes link)) (link-rule link) instantiations
                                       (discount-factor (link-rule link)) depth nil (cdr P) :binding binding :interest
                                       (resultant-interest link) :link link :clues (link-clues link))))
                               (t
                                 (draw-conclusion
                                   (interest-formula (resultant-interest link)) (cons node (supporting-nodes link))
                                   (link-rule link) instantiations (discount-factor (link-rule link)) depth nil
                                   (defeasible-rule (link-rule link)) :binding binding :interest (resultant-interest link)
                                   :link link :clues (link-clues link)))
                               ))))))))))

#| n is deductive in m. |#
(defunction deductive-in (n m)
    (and (member m (node-ancestors n))
              (some
                #'(lambda (L)
                      (and
                        (deductive-link L)
                        (let ((B (support-link-basis L)))
                           (and
                             (or (member m B)
                                   (some #'(lambda (x) (member m (node-ancestors x))) B))
                             (every
                               #'(lambda (x) (or (not (member m (node-ancestors x)))
                                                              (deductive-in x m)))
                               B)))))
                (support-links n))))

(defunction deductive-link (L)
    (or (keywordp (support-link-rule L)) (not (defeasible-rule (support-link-rule L)))))

(defunction discharge-interest-in-defeaters (node i-lists old-degree new?)
   ; (when (eq node (node 7)) (setf n node i i-lists o old-degree n? new?) (break))
    ;; (step (discharge-interest-in-defeaters n i o n?))
    (let ((degree (compute-maximal-degree-of-support node))
            (cancellations nil))
       (dolist (il i-lists)
            (let ((i-list (car il)))
               (dolist (N (i-list-interests i-list))
                   (when (and  (interest-defeatees N)
                                        (<= (degree-of-interest N) degree)
                                        (or new?
                                              (> (maximum-degree-of-interest N) old-degree))
                                        (subsetp= (node-supposition node)
                                                          (interest-supposition N)))
                        (pushnew N (generating-defeat-interests node))
                        (dolist (L (interest-defeatees N))
                            (pushnew node (support-link-defeaters L))
                            (pushnew L (node-defeatees node))
                            (when (deductive-node node)
                                 (let ((node* (support-link-target L)))
                                   (setf (support-link-conclusive-defeat-status L) T)
                                   (cond ((every #'support-link-conclusive-defeat-status (support-links node*))
                                               (push node* cancellations))
                                             (t
                                               (dolist (L (support-links node*))
                                                   (let ((NDA
                                                             (cond ((defeasible? L)
                                                                         (mapcar #'genunion
                                                                                        (gencrossproduct
                                                                                          (mapcar #'nearest-defeasible-ancestors
                                                                                                         (support-link-basis L)))))
                                                                       (t (list (list node*))))))
                                                     (dolist (X NDA)
                                                         (when
                                                              (not (some #'(lambda (Y) (subsetp= Y X))
                                                                                  (nearest-defeasible-ancestors node*)))
                                                              (dolist (Y (nearest-defeasible-ancestors node*))
                                                                  (when (subsetp= X Y) (pull Y (nearest-defeasible-ancestors node*))))
                                                              (push X (nearest-defeasible-ancestors node*))))
                                                     (recursively-compute-nearest-defeasible-ancestors node*)))
                                               (let ((ancestors
                                                         (unionmapcar+
                                                           #'(lambda (L)
                                                                 (union (support-link-basis L)
                                                                            (unionmapcar+ #'node-ancestors (support-link-basis L))))
                                                           (support-links node*))))
                                                 (setf (node-ancestors node*) ancestors)
                                                 (recursively-compute-node-ancestors node* ancestors)
                                                 ))))))))))
       (if (and cancellations
                    (every #'(lambda (L)
                                      (and (not (keywordp (support-link-rule L)))
                                               (backwards-reason-p (support-link-rule L))))
                                (support-links node)))
         (cons node cancellations) cancellations)))

(defunction cancel-node (node depth)
     ; (when (eq node (node 21)) (setf n node d depth) (break))
    ;; (step (cancel-node n d))
    (compute-dependencies-from-node node)
    (let ((draw-lines?
              (and *display?* (zerop depth)
                        (or (not (cancelled-node node)) *dependent-nodes* *dependent-interests*))))
       (when  draw-lines?
            (princ
              "..........................................................................................................................................")
            (terpri) (princ "Cancelling node ") (princ (inference-number node))
            (terpri))
       (dolist (n *dependent-nodes*) (cancel-interest-in-node n (1+ depth)))
       (dolist (in *dependent-interests*) (cancel-interest in (1+ depth)))
       (when draw-lines?
            (princ
              "..........................................................................................................................................")
            (terpri))))

(defunction cancel-interest-in (interest depth)
    ; (when (equal interest (interest 2)) (setf i interest d depth) (break))
    ; (when (equal interest (interest 137)) (setf *d-trace* t) (display-on))
    ;; (step (cancel-interest-in i d))
    (when  (and *display?* (zerop depth))
         (princ
           "..........................................................................................................................................")
         (terpri) (princ "Cancelling interest ") (princ (interest-number interest))
         (terpri))
    (compute-dependencies interest)
    (dolist (n *dependent-nodes*) (cancel-interest-in-node n (1+ depth)))
    (dolist (in *dependent-interests*) (cancel-interest in (1+ depth)))
    (when (and *display?* (zerop depth))
         (princ
           "..........................................................................................................................................")
         (terpri))
    ; (when (equal interest (interest 2)) (setf *d-trace* nil) (break))
    )

(defunction compute-interest-dependencies (interest indent msg)
   ; (when (eq interest (interest 105)) (setf i interest n indent m msg) (break))
    ;; (step (compute-interest-dependencies i n m))
    (when *d-trace*
         (bar-indent indent) (princ msg) (princ interest)
         (when (cancelled-interest interest) (princ " cancelled")) (terpri))
    (dolist (s (generated-suppositions interest))
        (when (not (member s *dependent-nodes*))
             (push s *dependent-nodes*)
             (when (eq (node-justification s) :reductio-supposition)
                  (pull s *independent-reductio-suppositions*))
             (compute-node-dependencies s (1+ indent) "generated-supposition: ")))
   (dolist (n (anchored-nodes interest))
      (when (and (not (cancelled-node n)) (not (member n *dependent-nodes*)))
          (push n *dependent-nodes*)
          (when (eq (node-justification n) :reductio-supposition)
              (pull n *independent-reductio-suppositions*))
          (compute-node-dependencies n (1+ indent) "partial-satisfier: ")))
    (dolist (L (left-links interest))
        (let ((in (link-interest L)))
          (when (not (member in *dependent-interests*))
               (cond ((not (cancelled-interest in))
                           (push in *dependent-interests*)
                           (compute-interest-dependencies in (1+ indent) "left-link: "))
                         (t
                           (dolist (n (discharging-nodes in))
                               (when (and (not (member n *dependent-nodes*))
                                                   (not (cancelled-node n)))
                                    (push n *dependent-nodes*)
                                    (compute-node-dependencies
                                      n (1+ indent) "discharging-node of left-link: ")))))))))

(defunction compute-node-dependencies (node indent msg)
    (when *d-trace*
         (bar-indent indent) (princ msg) (princ node)
         (when (cancelled-node node) (princ " cancelled")) (terpri))
    (dolist (n (node-consequences node))
        (when (and (not (member n *dependent-nodes*))
                               (not (cancelled-node n)))
             (push n *dependent-nodes*)
             (compute-node-dependencies n (1+ indent) "node-consequence: ")))
    (dolist (in (generated-direct-reductio-interests node))
        (when (not (member in *dependent-interests*))
             (push in *dependent-interests*)
             (compute-interest-dependencies
               in (1+ indent) "generated-direct-reductio-interest: ")))
    (dolist (in (generated-defeat-interests node))
        (when (not (member in *dependent-interests*))
              (push in *dependent-interests*)
              (compute-interest-dependencies
                in (1+ indent) "generated-defeat-interest: ")))
    (when (eq (node-justification node) :reductio-supposition)
         (dolist (in *direct-reductio-interests*)
             (when (not (member in *dependent-interests*))
                  (push in *dependent-interests*)
                  (compute-interest-dependencies
                    in (1+ indent) "*direct-reductio-interest*: ")))))

#| This computation is exhibited by setting *d-trace* to t. |#
(defunction compute-dependencies-from-node (node)
    ; (when (eq node (node 703)) (break))
    (setf *dependent-interests* nil *dependent-nodes* (list node)
             *independent-reductio-suppositions* *reductio-supposition-nodes*)
    (compute-node-dependencies
      node 0 "COMPUTING DEPENDENCIES from ")
    (when *d-trace* (princ "ANCHORING-NODES AND INTERESTS") (terpri))
    (let ((anchored-nodes
              (subset
                #'(lambda (n)
                      (and
                        (not (eq n node))
                        (or
                   (some
                     #'(lambda (in)
                           (and
                             (not (member in *dependent-interests*))
                             (not (cancelled-interest in))
                             (progn
                                (when *d-trace*
                                    (princ "Node ") (princ (inference-number n))
                                    (princ " is directly anchored by the anchoring-interest ")
                                    (princ (interest-number in)) (terpri)) t)))
                     (anchoring-interests n))
                          (some #'(lambda (in)
                                           (and
                                             (not (member in *dependent-interests*))
                                             (not (cancelled-interest in))))
                                      (generating-interests n))
                          (some
                            #'(lambda (L)
                                  (every #'(lambda (b)
                                                    (and (not (member b *dependent-nodes*))
                                                             (not (cancelled-node b))))
                                              (support-link-basis L)))
                            (support-links n))
                          (and
                            *independent-reductio-suppositions*
                            (some
                              #'(lambda (in)
                                    (some
                                      #'(lambda (dr)
                                            (let ((n* (car dr)))
                                              (and
                                                (not (cancelled-node n*))
                                    (pushnew n (anchored-nodes (car in)))
                                                (pushnew (car in) (anchoring-interests n))
                                                (not (member n* *dependent-nodes*))
                                                (progn
                                                    (when *d-trace*
                                                         (princ "Node ") (princ (inference-number n))
                                                         (princ " is directly anchored by discharging a direct-reductio-interest from node ")
                                                         (princ (inference-number n*)) (terpri)) t))))
                                    (direct-reductio-interest (car in))))
                            (discharged-interests n)))
                          (some
                            #'(lambda (in)
                                  (some
                                    #'(lambda (L)
                                          (and (not (query-p (resultant-interest L)))
                                                   (not (cancelled-interest (resultant-interest L)))
                                                   (pushnew n (anchored-nodes in))
                                                   (pushnew in (anchoring-interests n))
                                                   (not (member (resultant-interest L) *dependent-interests*))
                                                   ))
                                    (right-links in)))
                            (enabling-interests n))
                          )))
                *dependent-nodes*))
            (anchored-interests
              (subset
                #'(lambda (in)
                      (or
                        (some #'(lambda (n) (not (member n *dependent-nodes*)))
                                    (generating-nodes in))
                        (some #'(lambda (n) (not (member n *dependent-nodes*)))
                                    (generating-defeat-nodes in))
                        (and *independent-reductio-suppositions*
                                 (some #'(lambda (dr) (not (member (car dr) *dependent-nodes*)))
                                             (direct-reductio-interest in)))
                        (some #'(lambda (L) (not (member (resultant-interest L) *dependent-interests*)))
                                    (right-links in))))
                *dependent-interests*)))
      (dolist (n anchored-nodes)
          (anchor-node-relative-to-node n node 0 "Directly-anchored node: "))
      (dolist (in anchored-interests)
          (anchor-interest-relative-to-node in node 0 "Directly-anchored interest: "))))

(defunction compute-dependencies (interest)
   ; (when (eq interest (interest 105)) (setf i interest) (break))
    ;; (step (compute-dependencies i))
    (setf *dependent-interests* (list interest) *dependent-nodes* nil
             *independent-reductio-suppositions* *reductio-supposition-nodes*)
    (compute-interest-dependencies
      interest 0 "COMPUTING DEPENDENCIES from ")
    (when *d-trace* (princ "ANCHORING-NODES AND INTERESTS") (terpri))
    (let ((anchored-nodes
              (subset
                #'(lambda (n)
                      (or
                  (some
                    #'(lambda (in)
                          (and
                            (not (member in *dependent-interests*))
                            (not (cancelled-interest in))
                            (progn
                               (when *d-trace*
                                   (princ "Node ") (princ (inference-number n))
                                   (princ " is directly anchored by the anchoring-interest ")
                                   (princ (interest-number in)) (terpri)) t)))
                    (anchoring-interests n))
                        (some #'(lambda (in)
                                         (and
                                           (not (member in *dependent-interests*))
                                           (not (cancelled-interest in))
                                           (progn
                                               (when *d-trace*
                                                    (princ "Node ") (princ (inference-number n))
                                                    (princ " is directly anchored by the generating-interest ")
                                                    (princ (interest-number in)) (terpri)) t)))
                                    (generating-interests n))
                        (some #'(lambda (in)
                                         (and
                                           (not (member in *dependent-interests*))
                                           (not (cancelled-interest in))
                                           (progn
                                               (when *d-trace*
                                                    (princ "Node ") (princ (inference-number n))
                                                    (princ " is directly anchored by the enabling-interest ")
                                                    (princ (interest-number in)) (terpri)) t)))
                                    (enabling-interests n))
                        (some
                          #'(lambda (L)
                                (and
                                  (every #'(lambda (b)
                                                    (and (not (member b *dependent-nodes*))
                                                              (not (cancelled-node b))))
                                               (support-link-basis L))
                                  (progn
                                      (when *d-trace*
                                           (princ "Node ") (princ (inference-number n))
                                           (princ " is directly anchored by the support-link ")
                                           (princ (support-link-number L)) (terpri)) t)))
                          (support-links n))
                        (and
                          *independent-reductio-suppositions*
                          (some
                            #'(lambda (in)
                                  (some
                                    #'(lambda (dr)
                                (let ((n* (car dr)))
                                  (and
                                    (not (cancelled-node n*))
                                    (pushnew n (anchored-nodes (car in)))
                                    (pushnew (car in) (anchoring-interests n))
                                    (not (member n* *dependent-nodes*))
                                    (progn
                                        (when *d-trace*
                                             (princ "Node ") (princ (inference-number n))
                                             (princ " is directly anchored by discharging a direct-reductio-interest from node ")
                                             (princ (inference-number n*)) (terpri)) t))))
                                    (direct-reductio-interest (car in))))
                            (discharged-interests n)))
                        (some
                          #'(lambda (in)
                                (and
                                  (eq n (cancelling-node in))
                                  (some
                                    #'(lambda (L)
                                          (and (not (query-p (resultant-interest L)))
                                                   (not (cancelled-interest (resultant-interest L)))
                                                   (push n (anchored-nodes (resultant-interest L)))
                                                   (pushnew (resultant-interest L) (anchoring-interests n))
                                                   (not (member (resultant-interest L) *dependent-interests*))
                                                   (progn
                                                       (when *d-trace*
                                                            (princ "Node ") (princ (inference-number n))
                                                            (princ " is directly anchored by being the cancelling-node for interest ")
                                                            (princ (interest-number in))
                                                            (princ " which has a right-link to interest ")
                                                            (princ (interest-number (resultant-interest L)))
                                                            (terpri))
                                                       t)))
                                    (right-links in))))
                          (enabling-interests n))
                        ))
                *dependent-nodes*))
            (anchored-interests
              (subset
                #'(lambda (in)
                      (and
                        (not (eq in interest))
                        (or
                          (some #'(lambda (n)
                                            (and
                                              (not (member n *dependent-nodes*))
                                            (progn
                                                (when *d-trace*
                                                     (princ "Interest ") (princ (interest-number in))
                                                     (princ " is directly anchored by the generating-node ")
                                                     (princ (inference-number n)) (terpri)) t)))
                                       (generating-nodes in))
                          (and *independent-reductio-suppositions*
                                   (some #'(lambda (dr)
                                                    (and
                                                      (not (member (car dr) *dependent-nodes*))
                                                      (progn
                                                          (when *d-trace*
                                                               (princ "Interest ") (princ (interest-number in))
                                                               (princ " is directly anchored by being a direct-reductio-interest from the node ")
                                                               (princ (inference-number (car dr))) (terpri)) t)))
                                               (direct-reductio-interest in)))
                          (some #'(lambda (L)
                                            (and
                                              (not (member (resultant-interest L) *dependent-interests*))
                                              (progn
                                                  (when *d-trace*
                                                       (princ "Interest ") (princ (interest-number in))
                                                       (princ " is directly anchored by a right-link to interest ")
                                                       (princ (interest-number (resultant-interest L))) (terpri)) t)))
                                       (right-links in)))))
                *dependent-interests*)))
       (dolist (n anchored-nodes)
           (anchor-node-relative-to-interest n interest 0 "Directly-anchored node: "))
       (dolist (in anchored-interests)
           (anchor-interest-relative-to-interest in interest 0 "Directly-anchored interest: "))))

(defunction anchor-interest-relative-to-interest (interest I indent msg)
    (pull interest *dependent-interests*)
    (when *d-trace*
          (bar-indent indent) (princ msg) (princ interest) (terpri))
    (dolist (L (left-links interest))
        (let ((in (link-interest L)))
            (when (member in *dependent-interests*)
                 (let ((cn (cancelling-node in)))
                    (when cn (anchor-node-relative-to-interest cn I  (1+ indent) "cancelling-node: ")))
                 (when (and (not (eq I in)) (member in *dependent-interests*))
                      (anchor-interest-relative-to-interest in I (1+ indent) "left-link: ")))))
    (dolist (n (generated-suppositions interest))
        (when (member n *dependent-nodes*)
             (anchor-node-relative-to-interest n I (1+ indent) "generated-supposition: "))))

(defunction anchor-node-relative-to-interest (node I indent msg)
    (pull node *dependent-nodes*)
    (when *d-trace*
         (bar-indent indent) (princ msg) (princ node) (terpri))
    (dolist (n (node-consequences node))
        (when
             (and
               (member n *dependent-nodes*)
               (some
                 #'(lambda (L)
                       (every #'(lambda (b)
                                         (and (not (cancelled-node b))
                                                   (not (member b *dependent-nodes*))))
                                    (support-link-basis L)))
                 (support-links n)))
             (anchor-node-relative-to-interest n I (1+ indent) "node-consequence: ")))
    (when (and (eq (node-justification node) :reductio-supposition)
                          (null *independent-reductio-suppositions*))
         (push node *independent-reductio-suppositions*)
         (dolist (in *direct-reductio-interests*)
             (when (and (not (eq I in)) (member in *dependent-interests*)
                                   (some
                                     #'(lambda (dr)
                                           (and
                                             (not (cancelled-node (car dr)))
                                             (not (member (car dr) *dependent-nodes*))))
                                     (direct-reductio-interest in)))
                  (anchor-interest-relative-to-interest
                    in I (1+ indent) "*direct-reductio-interest*: "))
             (let ((n* (cancelling-node in)))
                (when (and n* (member n* *dependent-nodes*))
                     (anchor-node-relative-to-interest
                       n* I (1+ indent) "discharges direct reductio interest: ")))))
    (dolist (in (generated-direct-reductio-interests node))
        (when *independent-reductio-suppositions*
             (when (and (not (eq I in)) (member in *dependent-interests*))
                  (pull in *dependent-interests*)
                  (anchor-interest-relative-to-interest
                    in I (1+ indent) "generated-direct-reductio-interest: "))
             (let ((n* (cancelling-node in)))
                (when (and n* (member n* *dependent-nodes*))
                     (anchor-node-relative-to-interest
                       n* I (1+ indent) "discharges direct reductio interest: "))))))

(defunction anchor-interest-relative-to-node (interest N0 indent msg)
    (pull interest *dependent-interests*)
    (when *d-trace*
         (bar-indent indent) (princ msg) (princ interest) (terpri))
    (dolist (L (left-links interest))
        (let ((in (link-interest L)))
            (when (member in *dependent-interests*)
                 (anchor-interest-relative-to-node in N0 (1+ indent) "left-link: ")
                 (let ((cn (cancelling-node in)))
                    (when (and cn (member cn *dependent-nodes*))
                         (anchor-node-relative-to-interest cn N0  (1+ indent) "cancelling-node: "))))))
    (dolist (n (generated-suppositions interest))
        (when (and (not (eq N N0)) (member n *dependent-nodes*))
             (anchor-node-relative-to-node n N0 (1+ indent) "generated-supposition: "))))

(defunction anchor-node-relative-to-node (node N0 indent msg)
    (pull node *dependent-nodes*)
    (when *d-trace*
         (bar-indent indent) (princ msg) (princ node) (terpri))
    (dolist (n (node-consequences node))
        (when
             (and
               (not (eq N N0))
               (member n *dependent-nodes*)
               (some
                 #'(lambda (L)
                       (every #'(lambda (b)
                                         (and (not (cancelled-node b))
                                                   (not (member b *dependent-nodes*))))
                                    (support-link-basis L)))
                 (support-links n)))
             (anchor-node-relative-to-node n N0 (1+ indent) "node-consequence: ")))
    (when (and (eq (node-justification node) :reductio-supposition)
                          (null *independent-reductio-suppositions*))
         (push node *independent-reductio-suppositions*)
         (dolist (in *direct-reductio-interests*)
             (when (and (member in *dependent-interests*)
                                   (some
                                     #'(lambda (dr)
                                           (and
                                             (not (cancelled-node (car dr)))
                                             (not (member (car dr) *dependent-nodes*))))
                                     (direct-reductio-interest in)))
                  (anchor-interest-relative-to-node
                    in N0 (1+ indent) "*direct-reductio-interest*: "))
             (let ((n* (cancelling-node in)))
                (when (and n* (not (eq n* N0)) (member n* *dependent-nodes*))
                     (anchor-node-relative-to-node
                       n* N0 (1+ indent) "discharges direct reductio interest: ")))))
    (dolist (in (generated-direct-reductio-interests node))
        (when *independent-reductio-suppositions*
             (when (member in *dependent-interests*)
                  (pull in *dependent-interests*)
                  (anchor-interest-relative-to-node
                    in N0 (1+ indent) "generated-direct-reductio-interest: "))
             (let ((n* (cancelling-node in)))
                (when (and n* (not (eq n* N0)) (member n* *dependent-nodes*))
                     (anchor-node-relative-to-node
                       n* N0 (1+ indent) "discharges direct reductio interest: "))))))

(defunction cancel-interest (interest depth)
    (when (and *display?* (not (cancelled-interest interest)))
         (indent depth) (princ "Cancelling  ") (princ interest) (terpri))
    (let ((i-list (interest-i-list interest)))
      (when i-list
           (pull interest (i-list-interests i-list))
           (when (null (i-list-interests i-list))
                (let ((dn (i-list-d-node i-list)))
                   (pull i-list (d-node-i-lists dn))
                   (when (and (null (d-node-c-lists dn))
                                           (null (d-node-i-lists dn))
                                           (null (d-node-forwards-reasons dn))
                                           (null (d-node-backwards-reasons dn))
                                           (null (d-node-interest-schemes dn))
                                           (null (discrimination-tests dn)))
                         (cancel-d-node dn)))
                (dolist (cl (corresponding-c-lists i-list))
                    (pull (assoc i-list (corresponding-i-lists (mem1 cl)))
                            (corresponding-i-lists (mem1 cl)))))))
    (setf (cancelled-interest interest) t)
    (let ((Q (interest-queue-node interest)))
      (when Q (pull Q *inference-queue*)))
    (dolist (IS (generated-interest-schemes interest))
        (cancel-interest-scheme IS))
    (dolist (L (left-links interest))
        (pull L (right-links (link-interest L))))
    (dolist (L (right-links interest))
        (when (not (query-p (resultant-interest L)))
              (pull L (left-links (resultant-interest L)))
              (push L (cancelled-left-links (resultant-interest L)))))
    (when (direct-reductio-interest interest) (pull interest *direct-reductio-interests*))
    (when (and *display?* *graphics-on* *graph-interests*) (invalidate-view *og* t)))

(defunction cancel-interest-scheme (IS)
    (let ((dn (is-d-node IS)))
      (pull IS (d-node-interest-schemes dn))
      (when (and (null (d-node-interest-schemes dn))
                          (null (d-node-c-lists dn))
                          (null (d-node-i-lists dn))
                          (null (d-node-forwards-reasons dn))
                          (null (d-node-backwards-reasons dn))
                          (null (discrimination-tests dn)))
           (cancel-d-node dn)))
    (dolist (IS* (is-derived-interest-schemes IS)) (cancel-interest-scheme IS*)))

(defunction cancel-d-node (d-node)
    (when (not (eq d-node *top-d-node*))
         (let* ((dn (parent-d-node d-node))
                   (test (rassoc d-node (discrimination-tests dn))))
            (setf (discrimination-tests dn) (remove test (discrimination-tests dn)))
            (when (and (null (d-node-c-lists dn)) (null (d-node-i-lists dn))
                                  (null (d-node-forwards-reasons dn))
                                  (null (d-node-backwards-reasons dn))
                                  (null (d-node-interest-schemes dn))
                                  (null (discrimination-tests dn))
                                  (null (d-node-degenerate-backwards-reasons dn)))
                 (cancel-d-node dn)))))

(defunction cancel-interest-in-node (node depth)
   ; (when (eq node (node 353)) (break))
    (when (not (cancelled-node node))
         (when *display?* (indent depth) (princ "Cancelling  ") (princ node) (terpri))
         (setf (cancelled-node node) t)
         (when (eq (node-justification node) :reductio-supposition)
              (pull node *reductio-supposition-nodes*)
              (when (generating-interests node)
                   (let ((i-list (interest-i-list (mem1 (generating-interests node)))))
                      (when (eq (i-list-reductio-supposition i-list) node)
                           (setf (i-list-reductio-supposition i-list) nil)
                           (setf (reductio-trigger i-list) t)))))
         (when (eq (node-justification node) :supposition)
              (setf *skolem-free-suppositions*
                       (remove-if-equal (node-formula node) *skolem-free-suppositions*)))
         (pull node *inherited-non-reductio-suppositions*)
         (pull node *non-reductio-supposition-nodes*)
         (pull node *reductio-supposition-nodes*)
         (pull node *desires*)
         (pull node *processed-desires*)
         (dolist (IN (generated-interests node))
             (pull node (generating-nodes IN)))
         (dolist (IN (generating-interests node))
             (pull node (generated-suppositions IN)))
         (dolist (IN (generated-direct-reductio-interests node))
             (setf (direct-reductio-interest IN) nil))
             ; (pull node (reductio-interests IN)))
         (let ((c-list (node-c-list node)))
            (when c-list
                 (pull node (c-list-nodes c-list))
                 (pull node (c-list-processed-nodes c-list))
                 (when (null (c-list-processed-nodes c-list))
                     (dolist (IS (supported-interest-schemes c-list))
                        (cancel-interest-scheme IS))
                     (dolist (IP (generated-instantiated-premises c-list))
                        (cancel-instantiated-premise IP)))
                 (when (null (c-list-nodes c-list))
                      (let ((dn (c-list-d-node c-list)))
                         (pull c-list (d-node-c-lists dn))
                         (when (and (null (d-node-c-lists dn)) (null (d-node-i-lists dn))
                                                   (null (d-node-forwards-reasons dn))
                                                   (null (d-node-backwards-reasons dn))
                                                   (null (d-node-interest-schemes dn))
                                                   (null (discrimination-tests dn)))
                              (cancel-d-node dn)))
                 (dolist (cl (c-list-contradictors c-list))
                    (pull (assoc c-list (c-list-contradictors (car cl)))
                            (c-list-contradictors (car cl))))
                      (dolist (il (corresponding-i-lists c-list))
                          (pull (assoc c-list (corresponding-c-lists (mem1 il)))
                                   (corresponding-c-lists (mem1 il)))))))
         (let ((Q (node-queue-node node)))
           (when Q (pull Q *inference-queue*)))
         (when (and *display?* *graphics-on*) (invalidate-view *og* t))))

(defunction cancel-instantiated-premise (IP)
    (let ((dn (ip-d-node IP)))
      (pull IP (d-node-forwards-reasons dn))
      (when (and (null (d-node-forwards-reasons dn))
                          (null (d-node-interest-schemes dn))
                          (null (d-node-c-lists dn))
                          (null (d-node-i-lists dn))
                          (null (d-node-backwards-reasons dn))
                          (null (discrimination-tests dn)))
           (cancel-d-node dn)))
    (dolist (IP* (ip-derived-premises IP)) (cancel-instantiated-premise IP*)))

#| old-degree is the maximal-degree-of-support for the node the last
time discharge-interest-schemes was applied to it. |#
(defunction discharge-interest-schemes (node old-degree depth)
   ; (when (equal node (node 54)) (setf n node o old-degree d depth) (break))
    ;; (step (discharge-interest-schemes n o d))
    (catch 'discharge-interest-schemes
        (let* ((c-list (node-c-list node))
                  (d-node (c-list-d-node c-list)))
           (reason-from-dominant-interest-schemes node d-node old-degree depth))))

(defunction reason-from-dominant-interest-schemes (node d-node old-degree depth)
    ; (when (and (eq node (node 6)) (eq d-node (d-node 19)))
    ;      (setf n node dn d-node od old-degree d depth) (break))
    ;; (step (reason-from-dominant-interest-schemes n dn od d))
    (reason-from-current-interest-scheme node d-node old-degree depth)
    (let ((pn (parent-d-node d-node)))
       (when pn (reason-from-dominant-interest-schemes node pn old-degree depth))))

(defunction reason-from-current-interest-scheme (node d-node old-degree depth)
    ; (when (eq node (node 28)) (setf n node dn d-node od old-degree d depth) (break))
    ;; (step (reason-from-current-interest-scheme n dn od d))
    (when *trace* (indent depth) (princ "REASON-FROM-CURRENT-INTEREST-SCHEME: ")
                (princ node) (princ " and ") (princ d-node) (terpri))
    (dolist (is (d-node-interest-schemes d-node))
        (let ((reason (is-reason is))
                (instance-function (is-instance-function is)))
           (when (cancelled-node node) (throw 'discharge-interest-schemes nil))
           (when (and (or (not (deductive-only node)) (not (defeasible-rule reason)))
                                 (or (not (deductive-interest (is-target-interest is))) (deductive-node node)))
                (let ((degree* (degree-of-interest (is-target-interest is))))
                   (when (and (>= (compute-maximal-degree-of-support node) degree*)
                                         (> degree* old-degree))
                        (cond
                          (instance-function (funcall instance-function node (1+ depth) nil))
                          (t (reason-from-interest-scheme
                                node (interest-priority (is-target-interest is)) (1+ depth) is)))))))))

;................................................. COMPUTING BELIEFS ........................................

(proclaim '(special *elapsed-time* *affected-nodes*))

#| Update-defeat-statuses returns the list of affected-nodes, which is then used by
compute-undefeated-degrees-of-support.  The latter returns the pairs
(new-beliefs new-retractions) where new-beliefs is the list of nodes whose
undefeated-degrees-of-support have increased as a result of the computation and new-retractions
is the list of nodes whose undefeated-degrees-of-support have decreased as a result of
this computation.  When the undefeated-degree-of-support of any node other than node is
changed, so is its old-undefeated-degree-of-support. |#
(defunction update-beliefs ()
   ; (when (member (support-link 5) *new-links*) (break))
   ; (when (eql *cycle* 4763) (break))
    ;; (step (update-beliefs))
    (cond
      (*deductive-only*
        (dolist (link *new-links*)
            (let ((node (support-link-target link)))
              (setf (old-undefeated-degree-of-support node) (undefeated-degree-of-support node))
              (setf (undefeated-degree-of-support node) 1.0)
              (setf (support-link-strength link) 1.0)
              (setf (discounted-node-strength node) (support-link-discount-factor link))
              (when (null (old-undefeated-degree-of-support node))
                          (queue-for-inference node))
             ; (display-belief-changes (list link) (list node) nil)
              (discharge-ultimate-epistemic-interests (list node) nil))))
      (t
        (setf *altered-links* *new-links*)
        (update-defeat-statuses)
        (let* ((belief-changes (compute-undefeated-degrees-of-support))
                  (new-beliefs (mem1 belief-changes))
                  (new-retractions (mem2 belief-changes))
                  (altered-interests
                    (compute-interest-graph-defeat-statuses new-beliefs new-retractions)))
          (let ((nodes nil))
             (dolist (L *new-links*)
                 (let ((node (support-link-target L)))
               (pushnew node nodes)))
          (dolist (node nodes)
                  (when (null (old-undefeated-degree-of-support node))
                       (queue-for-inference node))))
          (display-belief-changes *new-links* new-beliefs new-retractions)
          (dolist (node new-beliefs)
              (apply-optative-dispositions-to node)
              (apply-Q&I-modules-to node))
          (let ((altered-queries
                    (discharge-ultimate-epistemic-interests new-beliefs new-retractions)))
            (recompute-priorities new-beliefs new-retractions altered-interests altered-queries))
          (dolist (N new-retractions)
              (when (not (some #'(lambda (link) (eq N (support-link-target link))) *new-links*))
                   (setf (old-undefeated-degree-of-support N) (undefeated-degree-of-support N))))
          (dolist (N new-beliefs)
              (when (not (some #'(lambda (link) (eq N (support-link-target link))) *new-links*))
                   (setf (old-undefeated-degree-of-support N) (undefeated-degree-of-support N))))
          ))))

(defunction complete-tree (tree)
    (and
      (or (triangle-sets tree)
            (every #'(lambda (n) (assoc n (node-UDs *assignment-tree*))) *inference-graph*))
      (every #'(lambda (ts)
                        (and
                          (assignment-trees ts)
                          (every
                            #'(lambda (at)
                                  (every
                                    #'(lambda (link) (assoc link (link-UDs at)))
                                    (triangle-domain ts)))
                            (assignment-trees ts))))
                  (triangle-sets tree))))

(defunction display-belief-changes  (links new-beliefs new-retractions)
    #| (when (member (support-link 12) links) (setf l links nb new-beliefs nr new-retractions) (break))
       (step (display-belief-changes l  nb nr)) |#
    (when *monitor-assignment-tree*
         (monitor-assignment-tree links)
         (loop
           (when (read-char-no-hang) (return))))
    #| (when (and (not (complete-tree *assignment-tree*)) (null *deductive-only*))
	 (princ link) (terpri) (break)) |#
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
                  (or new-retractions
                        (some
                          #'(lambda (N)
                                (or (not (some #'(lambda (L) (eq N (support-link-target L))) links))
                                      (set-difference (support-links N) links)
                                      (not (eql (undefeated-degree-of-support N) 1.0))))
                          new-beliefs))
                  (when *log-on*
                       (push "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" *reasoning-log*))
                  (when *display?* (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri)))
             (dolist (N new-beliefs)
                 (cond ((or (not (some #'(lambda (L) (eq N (support-link-target L))) links))
                                  (set-difference (support-links N) links))
                             (when *log-on*
                                  (push (list :increased-support N (undefeated-degree-of-support N))
                                            *reasoning-log*))
                             (when *display?*
                                  (princ "               The undefeated-degree-of-support of ") (princ N)
                                  (princ " has increased to ") (princ (undefeated-degree-of-support N)) (terpri)
                                  (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri))  ;)
                             (when (and *display?* *graphics-on*)
                                  (let ((posi (node-position N *og*)))
                                    (when posi
                                         (when (and (boundp '*speak*) *speak*)
                                              (speak-text "The undefeeted-degree-of-support of N ")
                                              (speak-text (write-to-string (inference-number N)))
                                              (speak-text "has increased to")
                                              (speak-text (write-to-string (undefeated-degree-of-support N))))
                                         (draw-just-undefeated-node posi *og* N)))))
                           ((not (eql (undefeated-degree-of-support N) 1.0))
                             (when *log-on*
                                  (push (list :new-support N (undefeated-degree-of-support N)) *reasoning-log*))
                             (when *display?*
                                  (princ "               The undefeated-degree-of-support of ") (princ N)
                                  (princ " is ") (princ (undefeated-degree-of-support N)) (terpri)
                                  (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri))
                             (when (and *display?* *graphics-on*)
                                  (when (and (boundp '*speak*) *speak*)
                                              (speak-text "The undefeeted-degree-of-support of N ")
                                              (speak-text (write-to-string (inference-number N)))
                                              (speak-text "is")
                                              (speak-text (write-to-string (undefeated-degree-of-support N))))
                                  (let ((posi (node-position n *og*)))
                                    (cond (posi (draw-just-undefeated-node posi *og* n))
                                              (t
                                                (draw-n n *og* *nodes-displayed*)
                                                (push n *nodes-displayed*)
                                                (setf posi (node-position n *og*))
                                                (draw-just-undefeated-node posi *og* n))))))))
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

#| The following returns the pair (new-beliefs new-retractions)
where new-beliefs is the list of nodes whose undefeated-degrees-of-support have increased
as a result of the computation and new-retractions is the list of nodes whose
undefeated-degrees-of-support have decreased as a result of this computation. |#

(defunction compute-undefeated-degrees-of-support ()
    #| (break)
       (when (member (support-link 2) *new-links*) (break))
       (step (compute-undefeated-degrees-of-support)) |#
    (let* ((immediately-altered-nodes
                (remove-duplicates (mapcar #'support-link-target *altered-links*)))
              (altered-nodes (inference-descendants immediately-altered-nodes))
              (altered-nodes-
                (subset #'(lambda (N) (not (member nil (nearest-defeasible-ancestors N)))) altered-nodes))
              (new-beliefs nil)
              (new-retractions nil))
      (dolist (N altered-nodes)
          (setf (old-undefeated-degree-of-support N) (undefeated-degree-of-support N)))
      (let ((undefeated-links
                (mapcar
                  #'(lambda (N)
                        (cons N
                                  (subset
                                    #'(lambda (L)
                                          (and (null (defeating-assignment-trees L))
                                                   (not (some
                                                             #'(lambda (b) (member b altered-nodes-))
                                                             (support-link-basis L)))))
                                    (support-links N))))
                  (reverse altered-nodes))))
        (dolist (pair undefeated-links)
         (dolist (L (cdr pair))
               (when (every #'undefeated-degree-of-support (support-link-basis L))
                      (setf (support-link-strength L)
                                 (if (and (not (keywordp (support-link-rule L))) (temporal? (support-link-rule L)))
                                   (prog1
                                       (* (support-link-reason-strength L)
                                            (minimum
                                              (mapcar #'compute-undefeated-degree-of-support
                                                                (support-link-basis L))))
                                       (setf (temporal-link L) *cycle*))
                                  (minimum
                                    (cons (support-link-reason-strength L)
                                                (mapcar #'compute-undefeated-degree-of-support
                                                                  (support-link-basis L)))))))))
        (loop
          (when (null undefeated-links) (return))
          (let ((pair (find-if #'(lambda (pair) (every #'support-link-strength (cdr pair))) undefeated-links)))
            (setf undefeated-links (remove pair undefeated-links))
            (let ((N (car pair))
                    (support-values nil)
                    (discounted-support-values nil))
              (dolist (L (cdr pair))
                  (let ((val (support-link-strength L)))
                    (push val support-values)
                    (push (* val (support-link-discount-factor L)) discounted-support-values)))
              (setf (undefeated-degree-of-support N) (maximum0 support-values))
              (setf (discounted-node-strength N) (maximum0 discounted-support-values))
              (dolist (L (consequent-links N))
                  (when (every #'undefeated-degree-of-support (support-link-basis L))
                       (setf (support-link-strength L)
                                (if (and (not (keywordp (support-link-rule L))) (temporal? (support-link-rule L)))
                                  (prog1
                                       (* (support-link-reason-strength L)
                                            (minimum
                                              (mapcar #'compute-undefeated-degree-of-support
                                                                (support-link-basis L))))
                                       (setf (temporal-link L) *cycle*))
                                  (minimum
                                    (cons (support-link-reason-strength L)
                                                (mapcar #'compute-undefeated-degree-of-support
                                                                  (support-link-basis L)))))))))))
        (dolist (N altered-nodes)
            (when (not (zerop (undefeated-degree-of-support N)))
                 (recompute-descendant-udoss N)))
        (dolist (node altered-nodes)
            (let ((old-undefeated-degree-of-support (compute-old-undefeated-degree-of-support node)))
              (cond
                ((null (old-undefeated-degree-of-support node))
                  (cond ((not (zerop (undefeated-degree-of-support node)))
                              (push node new-beliefs))
                            ((not (member nil (nearest-defeasible-ancestors node)))
                              (push node new-retractions))))
                ((> (undefeated-degree-of-support node) old-undefeated-degree-of-support)
                  (push node new-beliefs))
                ((< (undefeated-degree-of-support node) old-undefeated-degree-of-support)
                  (push node new-retractions)))))
        (list new-beliefs new-retractions)
        )))

(defunction inference-descendants (nodes)
    (let ((descendants nodes))
      (loop
        (when (null nodes) (return descendants))
        (let ((node (car nodes)))
          (setf nodes (cdr nodes))
          (dolist (L (consequent-links node))
              (let ((N (support-link-target L)))
                (when (not (member N descendants))
                     (push N descendants)
                     (push N nodes))))))))

(defunction interest-descendants (interests)
    (let ((descendants interests))
      (loop
        (let ((interest (car interests)))
          (setf interests (cdr interests))
          (dolist (L (left-links interest))
              (let ((N (link-interest L)))
                (when (not (member N descendants))
                     (push N descendants)
                     (push N interests))))
          (when (null interests)
               (return (order descendants #'(lambda (x y) (< (interest-number x) (interest-number y))))))))))

#| The nodes inferred by discharging the interest-descendants of interest. |#
(defunction node-descendants-of-interest (interest)
    (let ((interests (interest-descendants (list interest))))
      (order
        (inference-descendants
          (subset #'(lambda (N) (some #'(lambda (int) (member int interests)) (enabling-interests N)))
                        (unionmapcar #'discharging-nodes interests)))
        #'(lambda (x y) (< (inference-number x) (inference-number y))))))

#| Nodes and interests generated by node or interest. |#
(defunction descendants-of (N)
    (let ((interests (if (interest-p N) (list N)))
            (nodes (if (inference-node-p N) (list N)))
            (interest-descendants nil)
            (node-descendants nil))
      (loop
        (when (and (null nodes) (null interests))
             (p-print
               (order interest-descendants #'(lambda (x y) (< (interest-number x) (interest-number y)))))
             (p-print
               (order node-descendants #'(lambda (x y) (< (inference-number x) (inference-number y)))))
             (return nil))
        (cond (nodes
                    (let ((node (car nodes)))
                      (when node
                           (setf nodes (cdr nodes))
                           (dolist (L (consequent-links node))
                               (let ((N (support-link-target L)))
                                 (when (not (member N node-descendants))
                                      (push N node-descendants)
                                      (push N nodes))))
                           (dolist (N (generated-defeat-interests node))
                               (when (not (member N interest-descendants))
                                    (push N interest-descendants)
                                    (push N interests)))
                           (dolist (L *interest-links*)
                               (when (member node (link-clues L))
                                    (let ((N (link-interest L)))
                                      (when (not (member N interest-descendants))
                                           (push N interest-descendants)
                                           (push N interests))))))))
                  (interests
                    (let ((interest (car interests)))
                      (when interest
                           (setf interests (cdr interests))
                           (dolist (L (left-links interest))
                               (let ((N (link-interest L)))
                                 (when (not (member N interest-descendants))
                                      (push N interest-descendants)
                                      (push N interests))))
                           (dolist (N (discharging-nodes interest))
                               (when (member interest (enabling-interests N))
                                    (when (not (member N node-descendants))
                                         (push N node-descendants)
                                         (push N nodes))))
                           )))))))

(defunction recompute-descendant-udoss (node)
    (dolist (L (consequent-links node))
        (when (null (defeating-assignment-trees L))
             (let ((L-udos
                       (if (and (not (keywordp (support-link-rule L)))
                                     (temporal? (support-link-rule L)))
                         (* (support-link-reason-strength L)
                              (minimum (mapcar #'compute-undefeated-degree-of-support (support-link-basis L))))
                       (minimum
                           (cons (support-link-reason-strength L)
                                     (mapcar #'compute-undefeated-degree-of-support (support-link-basis L))))))
                     (target (support-link-target L)))
               (setf (support-link-strength L) L-udos)
                (when (> L-udos (compute-undefeated-degree-of-support target))
                     (setf (undefeated-degree-of-support target) L-udos)
                     (setf (discounted-node-strength target)
                              (* L-udos (support-link-discount-factor L)))
                     (recompute-descendant-udoss target))))))

#|
;(defunction tree-degree (node assignment-tree)
;    (or (zeroed-value (assoc node (node-assignment assignment-tree)))
;          (minimum
;            (mapcar
;              #'(lambda (triangle)
;                    (minimum
;                      (mapcar
;                        #'(lambda (tree)
;                              (tree-degree node tree))
;                        (assignment-trees triangle))))
;              (triangle-sets assignment-tree)))))
;
;(defunction zeroed-value (assoc)
;    (if assoc (or (cdr assoc) 0)))
|#

#| This computes defeat-statuses for interest-links and interests, and returns the list
of all interests whose defeat-statuses change as a result of the computation.  |#
(defunction compute-interest-graph-defeat-statuses (new-beliefs new-retractions)
    (let ((altered-interests nil)
            (altered-links nil))
       (dolist (c new-beliefs)
           (dolist (L (link-defeatees (node-c-list c)))
               (when (not (member L altered-links))
                    (push L altered-links)
                    (let ((defeated?
                                (and
                                  (link-defeaters L)
                                  (or (some
                                          #'(lambda (D)
                                                (and (>= (compute-undefeated-degree-of-support D)
                                                                 (degree-of-interest (resultant-interest L)))
                                                          (subsetp= (node-supposition D)
                                                                             (interest-supposition (resultant-interest L)))))
                                          (c-list-nodes (mem1 (link-defeaters L))))
                                        (some
                                          #'(lambda (D)
                                                (and (>= (compute-undefeated-degree-of-support D)
                                                                 (degree-of-interest (resultant-interest L)))
                                                          (subsetp= (node-supposition D)
                                                                             (interest-supposition (resultant-interest L)))))
                                          (c-list-nodes (mem2 (link-defeaters L))))))))
                       (when (not (eq defeated? (link-defeat-status L)))
                            (setf (link-defeat-status L) defeated?)
                            (pushnew (link-interest L) altered-interests))))))
       (dolist (c new-retractions)
           (dolist (L (link-defeatees (node-c-list c)))
               (when (and (not (member L altered-links))
                                     (subsetp= (node-supposition c)
                                                        (interest-supposition (resultant-interest L))))
                    (push L altered-links)
                    (let ((defeated?
                                (and
                                  (link-defeaters L)
                                  (or (some
                                          #'(lambda (D)
                                                (>= (compute-undefeated-degree-of-support D)
                                                       (degree-of-interest (resultant-interest L))))
                                          (c-list-nodes (mem1 (link-defeaters L))))
                                        (some
                                          #'(lambda (D)
                                                (>= (compute-undefeated-degree-of-support D)
                                                       (degree-of-interest (resultant-interest L))))
                                          (c-list-nodes (mem1 (link-defeaters L))))))))
                       (when (not (eq defeated? (link-defeat-status L)))
                            (setf (link-defeat-status L) defeated?)
                            (pushnew (link-interest L) altered-interests))))))
       altered-interests))

(defunction apply-optative-dispositions-to (conclusion)
   (dolist (O *doxastic-optative-dispositions*)
      (funcall O conclusion)))

#| A Q&I-module is a function which, when applied to an appropriate conclusion, returns
the sequent concluded. |#
(defunction apply-Q&I-modules-to (conclusion)
    (when (not (deductive-only conclusion))
         (dolist (Q&I *Q&I-modules*)
             (let ((S (funcall Q&I conclusion)))
                (when S (draw-conclusion S nil :Q&I nil 1 0 nil nil))))))

(defunction discharge-ultimate-epistemic-interests (new-beliefs new-retractions)
   #| (when (eql *cycle* 19) (setf nb new-beliefs nr new-retractions) (break))
      (setf nb new-beliefs nr new-retractions)
      (step (discharge-ultimate-epistemic-interests nb nr)) |#
   (let ((altered-queries nil))
     (dolist (C new-beliefs)
         (when (answered-queries C)
              (let ((degree (compute-undefeated-degree-of-support C)))
                (dolist (Q (answered-queries C))
                    (when (and (not (zerop (undefeated-degree-of-support C)))
                                        (>= degree (query-strength Q))
                                        (or (null (old-undefeated-degree-of-support C))
                                              (zerop (old-undefeated-degree-of-support C))
                                              (< (old-undefeated-degree-of-support C) (query-strength Q))))
                    (when *log-on* (push (list :answer-query C Q degree) *reasoning-log*))
                         (when *display?*
                              (princ "               ")
                              (princ "=========================================") (terpri)
                              (princ "               ") (princ "Justified belief in ")
                              (prinp (node-formula C)) (terpri)
                              (princ "               with undefeated-degree-of-support ")
                              (princ (compute-undefeated-degree-of-support C)) (terpri)
                              (princ "               ") (princ "answers ") (princ Q)
                              (terpri) (princ "               ")
                              (princ "=========================================") (terpri))
                         (dolist (instruction (positive-query-instructions Q))
                             (funcall instruction C))
                         (setf (answered? Q) t)
                         (when (not (member Q *permanent-ultimate-epistemic-interests*))
                              (push Q altered-queries)))))))
      (dolist (C new-retractions)
          (dolist (Q (answered-queries C))
              (when (and (old-undefeated-degree-of-support C)
                                  (>= (old-undefeated-degree-of-support C) (query-strength Q))
                                    (or (zerop (undefeated-degree-of-support C))
                                          (not (>= (undefeated-degree-of-support C) (query-strength Q)))))
              (when *log-on* (push (list :retract-answer C Q) *reasoning-log*))
                   (when *display?*
                        (princ "               ")
                        (princ "=========================================") (terpri)
                        (princ "               ") (princ "Lowering the undefeated-degree-of-support of ")
                        (prinp (node-formula C)) (terpri)
                        (princ "               ") (princ "retracts the previous answer to ")
                        (princ Q) (terpri) (princ "               ")
                        (princ "=========================================") (terpri))
                    (dolist (instruction (negative-query-instructions Q))
                         (funcall instruction C))
                   (when
                        (every
                          #'(lambda (A) (not (>= (compute-undefeated-degree-of-support A) (query-strength Q))))
                          (query-answers Q))
                        (setf (answered? Q) nil)
                        (when (not (member Q *permanent-ultimate-epistemic-interests*))
                             (push Q altered-queries))))))
      altered-queries))

(defunction affected-items (new-beliefs new-retractions altered-interests altered-queries)
   (let ((affected-nodes (append new-beliefs new-retractions))
           (affected-interests altered-interests))
      (dolist (query altered-queries)
             (pushnew (query-interest query) affected-interests))
      (loop
         (let ((changed? nil))
            (dolist (node affected-nodes)
                (dolist (n (node-consequences node))
                    (when (not (member n affected-nodes))
                         (push n affected-nodes)
                         (setf changed? t)))
                (dolist (in (generated-interests node))
                    (when (not (member in affected-interests))
                         (push in affected-interests)
                         (setf changed? t)))
                (when (eq (node-justification node) :reductio-supposition)
                     (dolist (in *direct-reductio-interests*)
                          (when (not (member in affected-interests))
                               (push in affected-interests)
                               (setf changed? t)))))
            (dolist (interest affected-interests)
                (dolist (L (left-links interest))
                    (let ((in (link-interest L)))
                      (when (not (member in affected-interests))
                           (push in affected-interests)
                           (setf changed? t))))
                (dolist (n (generated-suppositions interest))
                    (when (not (member n affected-nodes))
                         (push n affected-nodes)
                         (setf changed? t))))
            (when (null changed?)
                         (return (list affected-nodes affected-interests)))))))

(defunction broadly-generating-nodes (interest)
    (if (direct-reductio-interest interest)
       (union= *reductio-supposition-nodes* (generating-nodes interest))
       (generating-nodes interest)))

(defunction recompute-priorities (new-beliefs new-retractions altered-interests altered-queries)
    (let* ((affected-items
               (affected-items new-beliefs new-retractions altered-interests altered-queries))
              (affected-nodes (mem1 affected-items))
              (affected-interests (mem2 affected-items))
              (altered-queue nil))
       (dolist (query altered-queries)
           (let ((interest (query-interest query)))
              (pull interest affected-interests)
              (cond ((and (answered? query)
                                    (not (member query *permanent-ultimate-epistemic-interests*)))
                           (setf (interest-priority interest) (* (degree-of-interest interest) *answered-discount*)))
                          (t (setf (interest-priority interest) (degree-of-interest interest))))))
       (dolist (node affected-nodes)
           (cond ((zerop (undefeated-degree-of-support node))
                        ;; If a node is defeated, its discounted-node-strength is *base-priority*.
                        (pull node affected-nodes)
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
                         (let ((Q (node-queue-node node)))
                            (when Q (pushnew Q altered-queue))))))
       ;---------------------------------
       (loop
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
                               (when Q (pushnew Q altered-queue))))))
                (dolist (interest affected-interests)
                    (let ((GN (broadly-generating-nodes interest))
                            (links (subset #'(lambda (L) (null (link-defeat-status L))) (right-links interest))))
                       (cond ((and (null GN) (null links))
                                    ;; If an interest has neither generating-nodes nor undefeated right-links,
                                    ;;  its interest-priority is a0.  (This includes interest in defeaters.)
                                    (setf changes? t)
                                    (pull interest affected-interests)
                                    (setf (interest-priority interest) *base-priority*)
                                    (let ((Q (interest-queue-node interest)))
                                       (when Q (pushnew Q altered-queue))))
                                   ((and (not (some #'(lambda (n) (member n affected-nodes)) GN))
                                              (not (some #'(lambda (in) (member in affected-interests)) links)))
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
                         (let ((Q (interest-queue-node interest)))
                            (when Q (pushnew Q altered-queue))))))))
       ;---------------------------------
       (dolist (Q altered-queue)
           (cond ((eq (item-kind Q) :conclusion)
                        (setf (discounted-strength Q)
                                 (compute-discounted-node-strength (enqued-item Q)))
                        (setf (degree-of-preference Q)
                                 (/ (discounted-strength Q) (item-complexity Q)))
                        (setf *inference-queue*
                                 (ordered-insert Q (remove Q *inference-queue*) #'i-preferred)))
                       ((not (cancelled-interest (enqued-item Q)))
                         (setf (discounted-strength Q) (interest-priority (enqued-item Q)))
                         (setf (degree-of-preference Q)
                                  (/ (discounted-strength Q) (item-complexity Q)))
                         (setf *inference-queue*
                                  (ordered-insert Q (remove Q *inference-queue*) #'i-preferred)))))))

(defunction generating-reductio-interests (N)
    (subset #'(lambda (in) (equal (node-formula N) (neg (interest-formula in))))
      (generating-interests N)))

(defunction generating-non-reductio-interests (N)
    (subset #'(lambda (in) (not (equal (node-formula N) (neg (interest-formula in)))))
      (generating-interests N)))

#| The following function is left undefined pending further specification of the form
of epistemic desires. |#
(defun form-epistemic-desires-for (interest)
    (declare (ignore interest))
    T)

(defun initiate-actions ()
    (let ((act (find-if
                     #'(lambda (x)
                           (every #'(lambda (y) (>= (cdr x) (cdr y))) *executable-operations*))
                     *executable-operations*)))
       (pull act *executable-operations*)
       (try-to-perform act)
       (let ((query
                 (make-query
                   :query-number (incf *query-number*)
                   :query-formula (list "was-not-performed-when-tried" (mem1 act))
                   :query-strength (mem2 act)
                   :positive-query-instructions (list #'(lambda (x) (push x *executable-operations*)))
                   :negative-query-instructions (list #'(lambda (x) (pull x *executable-operations*))))))
          (adopt-ultimate-interest query))))

(defun try-to-perform (act )
    (let ((executor (e-assoc (mem1 act) *act-executors*)))
       (when executor (apply executor (cdr act)))))

(defun update-percepts ()
    T)

(defun update-environmental-input ()
    T)

;;=============================================

(defunction print-undefeated-degrees-of-support ()
    (terpri)
    (princ "========== UNDEFEATED DEGREES OF SUPPORT ==========") (terpri)
    (dolist (node *inference-graph*)
        (princ "Node #") (princ (inference-number node)) (princ ":  ")
        (if (zerop (undefeated-degree-of-support node)) (princ "defeated") (princ "undefeated")) (terpri))
    (princ "======================================") (terpri))

(defunction display-inference-graph ()
    (terpri)
    (princ "================== INFERENCE-GRAPH ===================") (terpri)
    (dolist (node (reverse *inference-graph*))
        (display-inference-node node)
        (princ "---------------------------------------------------") (terpri)))

;========================SKOLEMIZATION=====================

(defun var-kind (var) (get var 'var-kind))

(defun interest-variable (x)
    (and (symbolp x) (eq (var-kind x) :variable)))

(defun conclusion-variable (x)
    (and (symbolp x) (eq (var-kind x) :variable)))

(defun make-interest-variable ()
    (let ((var (gensym "x")))
       (setf (get var 'var-kind) :variable)
       (setf (get var 'i-var) t)
       var))

(defun make-conclusion-variable ()
    (let ((var (gensym "x")))
       (setf (get var 'var-kind) :variable)
       var))

;; This converts interest-variables into conclusion-variables in formula.
(defunction convert-interest-variables (formula variables)
    (let* ((vars nil)
              (substitution
                (mapcar #'(lambda (x)
                                     (let ((var (make-conclusion-variable)))
                                       (push var vars)
                                       (cons x var)))
                               variables)))
      (values (sublis substitution formula) vars)))

;; This converts conclusion-variables into interest-variables in formula.
(defunction convert-conclusion-variables (formula variables)
    (let* ((vars nil)
              (substitution
                (mapcar #'(lambda (x)
                                     (let ((var (make-interest-variable)))
                                       (push var vars)
                                       (cons x var)))
                               variables)))
     ; (setf substitution (mapcar #'(lambda (x) (cons (cdr x) (car x))) substitution))
      (values (sublis substitution formula) vars substitution)))

;; This converts conclusion-variables into interest-variables in a unifier
;(defunction convert-unifier-variables (unifier variables)
;   ; (when (> *gensym-counter* 78) (setf u unifier v variables) (break))
;    (let ((u1 (mem1 unifier)) (u2 (mem2 unifier)))
;      (if (eq u2 t) unifier
;           (let* ((vars nil)
;                     (substitution
;                       (mapcar #'(lambda (x)
;                                            (let ((var (make-interest-variable)))
;                                              (push var vars)
;                                              (cons x var)))
;                                      variables)))
;             (list u1 (mapcar #'(lambda (x) (cons (car x) (sublis substitution (cdr x)))) u2))))))

#| These are changed to allow conses in formulas. |#
(defunction formula-node-variables (p)
    (cond ((and (symbolp p) (eq (get p 'var-kind) :variable)) (list p))
              ((and (listp p) p)
                (union (formula-node-variables (car p)) (formula-node-variables (cdr p))))))

(defun make-skolem-e-function ()
    (let ((fun (gensym "s")))
       (setf (get fun 'var-kind) :skolem-function)
       fun))

(defun make-skolem-i-function ()
    (let ((fun (gensym "s")))
       (setf (get fun 'var-kind) :skolem-function)
       fun))

(defun make-skolem-e-constant ()
    (let ((fun (gensym "c")))
       (setf (get fun 'var-kind) :skolem-function)
       fun))

(defun make-skolem-i-constant ()
    (let ((fun (gensym "c")))
       (setf (get fun 'var-kind) :skolem-function)
       fun))

(defun skolem-function (x)
    (and (symbolp x) (eq (get x 'var-kind) :skolem-function)))

(defun skolem-functions (p)
    (cond ((symbolp p)
                 (if (skolem-function p) (list p)))
                ((stringp p) nil)
                ((listp p) (unionmapcar= #'skolem-functions p))))

#| P contains no skolem constants, functions, or variables. |#
(defunction skolem-free (P)
    (cond ((symbolp P)
                 (let ((kind (get P 'var-kind)))
                    (and (not (eq kind :variable)) (not (eq kind :skolem-function)))))
                ((listp P) (every #'skolem-free P))
                (t t)))

;========================UNIFICATION=====================

#| This does the substitutions sequentially rather than in parallel, and in
the reverse order from their occurrence in m. |#
(defunction sequential-sublis (m X)
    (cond ((eq (length m) 1)
                 (subst (cdr (mem1 m)) (mem1 (mem1 m)) X))
                (t (subst (cdr (mem1 m)) (mem1 (mem1 m)) (sequential-sublis (cdr m) X)))))

#| This substitutes in accordance with a match m. |#
(defunction match-sequential-sublis (m x)
    (cond ((eq m t) x)
                (t (sequential-sublis m x))))

#| This turns a sequential-match into a parallel match (to be applied by match-sublis). |#
(defunction parallelize-match (sm vars)
    (cond ((eq sm t) t)
                (t (let ((m nil))
                      (dolist (x vars)
                          (let ((x* (sequential-sublis sm x)))
                             (if (not (equal x x*)) (push (cons x x*) m))))
                      (if m m t)))))

(defun merge-sequential-matches (m m*)
    (cond ((equal m t) m*)
                ((equal m* t) m)
                (t (append m m*))))

(defunction reverse-match (m)
    (if (eq m t) t
         (mapcar #'(lambda (x) (cons (cdr x) (mem1 x))) m)))

#| If p and q have free variables in common, they must be rewritten before we can
apply the unification algorithm.  The following produces a pair of substitutions
(m1 m2) such that applying m1 to p and m2 to q unifies them.  m1 and m2 are
parallel matches to be applied by match-sublis.  The p-vars and q-vars are the
node-variables. |#
(defunction unifier (p q p-vars q-vars)
    (cond ((and (null p-vars) (null q-vars))
               ;  (if (equal p q) (list t t)))
                 (if (or (equal p q) (notational-variant p q)) (list t t)))
                (t (catch 'unifier
                       (let ((terms (variable-correspondence p q p-vars q-vars (list nil nil nil))))
                          (unifier* (mem1 terms) (mem2 terms) p-vars q-vars))))))

(defunction ni-unifier (n m)
    (unifier (node-formula (node n)) (interest-formula (interest m))
                 (node-variables (node n)) (interest-variables (interest m))))

(defunction node-unifier (n m)
    (unifier (node-formula (node n)) (node-formula (node m))
                 (node-variables (node n)) (node-variables (node m))))

(defunction reductio-unifier (n m)
    (unifier (neg (node-formula (node n))) (node-formula (node m))
                 (node-variables (node n)) (node-variables (node m))))

#| This returns the list (terms1 terms quantifier-variables) where terms1 and terms are the lists
of corresponding terms to be unified and quantifier-variables is the list of pairs (x . y) of
corresponding quantifier-variables used for testing for notational variants. |#
(defunction variable-correspondence (P Q P-vars Q-vars terms)
    (cond
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

(defunction unifier* (p q p-vars q-vars)
   ; (let ((intersection (intersection p-vars q-vars :test 'equal)))
    (let ((intersection (intersection p-vars q-vars)))
       (cond (intersection
                    (let ((mr nil)
                            (p*-vars (setdifference p-vars intersection)))
                       (setf mr
                                (mapcar
                                  #'(lambda (x)
                                        (if (interest-variable x)
                                           (let ((x* (make-interest-variable)))
                                              (push x* p*-vars)
                                              (cons x x*))
                                           (let ((x* (make-conclusion-variable)))
                                              (push x* p*-vars)
                                              (cons x x*))))
                                  intersection))
                       (let* ((mgu (mgu (sublis mr p) q (append p*-vars q-vars)))
                               (rm (reverse-match mr)))
                          (list
                            (parallelize-match
                              (append rm (merge-sequential-matches mgu mr)) p-vars)
                            (parallelize-match (merge-sequential-matches rm mgu) q-vars)))))
                   (t (let ((mgu (mgu p q (append p-vars q-vars))))
                         (list
                           (parallelize-match mgu p-vars)
                           (parallelize-match mgu q-vars)))))))

#| (mgu p q) is a most general unifier for p and q for purposes of forwards
reasoning..  This assumes that they have no free variables in common.  vars are
the free variables (possibly) occurring in x y.  They are assumed to be
interest-variables and node-variables.  This produces a serial match that
must be applied by match-sequential-sublis rather than match-sublis. |#
(defunction mgu (x y vars)
    (cond ((atom x)
                (cond ((eql x y) t)
                          ((member x vars)
                            (cond ((and (listp y) (eq (car y) 'q-var)) (throw 'unifier nil))
                                      ((occur x y) (throw 'unifier nil))
                                      (t (list (cons x y)))))
                          ((member y vars)
                            (cond ((and (listp x) (eq (car x) 'q-var)) (throw 'unifier nil))
                                      ((occur y x) (throw 'unifier nil))
                                      ((not (eq x '=))
                                        (list (cons y x)))
                                      (t (throw 'unifier nil))))
                          (t (throw 'unifier nil))))
              ((atom y)
                (cond ((member y vars)
                            (cond ((and (listp x) (eq (car x) 'q-var)) (throw 'unifier nil))
                                      ((occur y x) (throw 'unifier nil))
                                      (t (list (cons y x)))))
                          (t (throw 'unifier nil))))
              ((listp x)
                (cond ((not (listp y)) (throw 'unifier nil))
                          ((and (listp (cdr x)) (listp (cdr y)) (not (eql (length x) (length y)))) (throw 'unifier nil))
                          (t (mgu-list x y vars))))))

(defunction mgu-list (x y vars)
   (let ((m (mgu (mem1 x) (mem1 y) vars)))
     (cond ((null m) (throw 'unifier nil)))
     (cond ((null (cdr x)) m)
               ((eq m t)
                 (mgu-list (cdr x) (cdr y) vars))
               (t (let ((m* (mgu-list
                                   (sequential-sublis m (cdr x))
                                   (sequential-sublis m (cdr y))
                                   vars)))
                    (cond ((eq m* t) m)
                              (t (append m* m))))))))

(defunction permutations (X)
    (cond ((null X) (list nil))
                ((null (cdr X)) (list X))
                (t (let ((X1 nil) (X2 X) (permutations nil) (done nil))
                      (loop
                         (let ((y (car X2)))
                            (setf X2 (cdr X2))
                            (when (not (mem y done))
                                 (push y done)
                                 (dolist (Z (mapcar #'(lambda (p) (cons y p)) (permutations (append X1 X2))))
                                     (push Z permutations)))
                            (when (null X2) (return permutations))
                            (setf X1 (cons y X1))))))))

#| (Set-unifier X Y c-vars i-vars) returns the list of unifiers unifying X into Y. |#
;(defunction set-unifier (X Y x-vars y-vars)
;    (let ((length-x (length X))
;            (length-y (length Y)))
;       (when (<= length-x length-y)
;            (let ((unifiers nil)
;                    (n (- length-y length-x)))
;               (dolist (Y* (permutations Y))
;                   (let ((unifier (unifier X (nthcdr n Y*) x-vars y-vars)))
;                      (when unifier (pushnew unifier unifiers :test 'equal))))
;               unifiers))))

(defunction set-mgu (X Y vars)
    (cond (X
                 (let ((p (mem1 X))
                         (unifiers nil))
                    (dolist (q Y)
                        (let ((mgu (catch 'unifier (mgu p q vars))))
                           (when mgu (pushnew mgu unifiers :test 'equal))))
                    (when unifiers
                         (cond ((cdr X)
                                      (let ((new-unifiers nil))
                                         (dolist (unifier unifiers)
                                             (let ((unifiers*
                                                       (set-mgu (match-sublis unifier (cdr X))
                                                                            (match-sublis unifier Y)
                                                                            vars)))
                                                (dolist (U unifiers*)
                                                    (push (merge-matches* unifier U) new-unifiers))))
                                         new-unifiers))
                                     (t unifiers)))))
                (t (list t))))

(defunction set-unifier (X Y X-vars Y-vars)
   ; (setf x0 x y0 y xv x-vars yv y-vars)
    (let ((intersection (intersection X-vars Y-vars)))
       (cond (intersection
                    (let ((mr nil)
                            (X*-vars (setdifference X-vars intersection)))
                       (setf mr
                                (mapcar
                                  #'(lambda (x)
                                        (if (interest-variable x)
                                           (let ((x* (make-interest-variable)))
                                              (push x* X*-vars)
                                              (cons x x*))
                                           (let ((x* (make-conclusion-variable)))
                                              (push x* X*-vars)
                                              (cons x x*))))
                                  intersection))
                       (let* ((mgus (set-mgu (sublis mr X) Y (append X*-vars Y-vars)))
                                 (rm (reverse-match mr)))
                          (mapcar
                            #'(lambda (mgu)
                                  (list
                                    (parallelize-match
                                      (append rm (merge-sequential-matches mgu mr)) X-vars)
                                    (parallelize-match (merge-sequential-matches rm mgu) Y-vars)))
                            mgus))))
                   (t (let ((mgus (set-mgu X Y (append X-vars Y-vars))))
                         (mapcar
                           #'(lambda (mgu)
                                 (list
                                   (parallelize-match mgu X-vars)
                                   (parallelize-match mgu Y-vars)))
                           mgus))))))

#|
(set-unifier '((F c) (G y)) '((G a) (H c) (G b) (F z)) '(x y) '(z))
yields ((((y . a)) ((z . c))) (((y . b)) ((z . c))))
|#

#| This checks that interest-variables in vars1 and vars2 do not instantiate
each other.
(defunction constrained-assignment (unifier vars1 vars2)
    (let ((u1 (mem1 unifier)))
       (or (eq u1 t)
             (not (some
                       #'(lambda (v)
                             (some #'(lambda (w) (occur w (e-assoc v u1))) vars2))
                       vars1))))
    (let ((u2 (mem2 unifier)))
       (or (eq u2 t)
             (not (some
                       #'(lambda (v)
                             (some #'(lambda (w) (occur w (e-assoc v u2))) vars1))
                       vars2)))))
 |#

#| This checks that interest-variables in vars1 and vars2 are not instantiated
by terms containing those same variables. |#
(defunction constrained-assignment (unifier vars1 vars2)
    (let ((u1 (mem1 unifier))
            (u2 (mem2 unifier)))
      (and (or (eq u1 t)
                    (not (some #'(lambda (v) (occur v (e-assoc v u1))) vars1)))
               (or (eq u2 t)
                     (not (some #'(lambda (v) (occur v (e-assoc v u2))) vars2))))))

(setf *comparison-log*
 '(OSCAR_3.31 0.23 0.23 10 0.95
 ((104 35 37 78) (103 145 63 296) (102 21 30 44) (100 3 9 10) (99 623 145 471) (98 42 41 120) (97 13 33 42) (96 5 12 19) (95 13 40 46) (94 31 35 66)
  (93 6 18 24) (92 6 14 14) (91 2 8 8) (90 81 43 101) (89 15 25 47) (88 6 13 20) (87 7 12 14) (86 255 111 297) (85 16 31 45) (84 5 19 20)
  (83 4 16 17) (82 5 13 17) (81 16 39 47) (80 6 22 23) (79 12 26 27) (78 13 38 44) (77 3 12 13) (76 9 32 36) (75 10 19 27) (74 3 14 15) (73 9 17 27)
  (72 6 13 16) (71 10 13 24) (70 5 8 12) (69 3 5 5) (68 2 4 4) (67 2 4 4) (66 1 4 4) (65 6 16 18) (64 5 18 20) (63 5 15 17) (62 2 8 8) (61 6 17 21)
  (60 10 23 32) (59 3 6 6) (58 2 8 8) (57 2 7 7) (56 3 8 10) (55 1 4 4) (54 7 15 18) (53 7 21 23) (52 3 11 11) (51 3 9 9) (50 2 8 8) (49 3 5 6)
  (48 1 4 5) (47 3 6 6) (46 4 12 12) (45 2 5 5) (44 2 6 8) (43 1 3 3) (42 1 5 5) (41 2 3 3) (37 18 36 51) (36 1 5 7) (35 1 4 5) (34 5 18 24)
  (33 8 27 36) (32 28 80 95) (31 1 3 3) (30 4 18 18) (29 4 12 12) (28 2 4 5) (27 1 3 3) (26 2 3 3) (25 2 11 12) (24 4 11 15) (23 2 4 6) (22 1 3 3)
  (21 4 11 14) (20 23 24 32) (19 10 12 16) (18 3 7 8) (17 14 21 27) (16 17 21 29) (15 5 12 13) (14 7 13 14) (13 6 12 13) (12 3 10 11) (11 4 8 9)
  (10 3 4 5) (9 11 13 16) (8 9 9 13) (7 11 9 14) (6 8 16 19) (5 7 11 14) (4 4 8 10) (3 5 14 17) (2 4 7 10) (1 3 7 8)))
)


nil
