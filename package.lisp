;; OSCAR-loader

(eval-when (:compile-toplevel :load-toplevel :execute)
  (when (null (find-package "OSCAR"))
    (make-package "OSCAR"
                  :use '("COMMON-LISP-USER" "CCL" "COMMON-LISP"))))

(in-package "OSCAR")

(defvar *version* "OSCAR_3.31")
(princ "Loading ") (princ *version*) (terpri)

(proclaim
  '(special *act-executors* *altered-nodes* *answered-discount*
 *auxiliary-backwards-rules* *auxiliary-forwards-rules*
 *auxiliary-forwards-rules* *backwards-logical-reasons* *backwards-reasons* *backwards-rules*
 *backwards-substantive-reasons* *base-interest* *base-priority* *blocked-conclusions*
 *cancelled-c-lists* *comparison-log* *concluded-interest-priority* *d-trace*
 *dependent-interests* *dependent-nodes* *desires* *direct-reductio-interests*
 *display-inference-queue* *display?* *environmental-input* *executable-operations*
 *forwards-logical-reasons* *forwards-reasons* *forwards-rules* *forwards-substantive-reasons*
 *independent-reductio-suppositions* *inference-graph* *inference-number* *inference-number*
 *inference-queue* *inherited-non-reductio-suppositions* *interest-links* *interest-map*
 *interest-number* *interest-record* *interest-scheme-number* *interest-schemes* *interests*
 *link-number* *log-on* *non-reductio-supposition-nodes* *optative-dispositions* *pause* *percepts*
 *permanent-ultimate-epistemic-interests* *premises* *priority-interests* *prob-compiler-loaded*
 *problem-number* *problems* *problems-loaded* *processed-conclusions* *processed-desires*
 *q&i-modules* *query-number* *queue-number* *reasoning-log* *reductio-discount*
 *reductio-interest* *reductio-supposition-nodes* *skolem-free-suppositions* *skolem-multiplier*
 *start-trace* *support-link-number* *support-links* *test-log* *time-limit* *tools-loaded*
 *trees-loaded* *ultimate-epistemic-interests* *unused-suppositions* *proofs?*
 *use-logic* *use-reductio* *version* ei adjunction is-desire is-inference is-percept oscar-pathname reductio
  *deleted-arguments* *relevant-nodes* *open-position-for-assignment-tree-window*
 *flash-affected-nodes* *flash-defeatees* *flash-defeaters* *flash-ancestors*
 *flash-consequences* *flash-support-link-bases* *flash-support-links* *deductive-only*
 *flash-relevant-nodes* *graph-ancestors* *graph-relevant-nodes* *menu-dialog*
 *message* *start-display* *cycle* *assignment-tree-window* *assignment-tree-subview*
 *monitor-assignment-tree* *assignment-tree-window-size* *assignment-tree-dialog*
 *graphics-initialized* *graphics-on* *graph-log* *graphics-pause* *nodes-displayed*
 *og-nodes* *og* *graph-interests* *speak* *d-node-number* *discrimination-net*
 *top-d-node* *operators* *quantifier-number* *conditional-node* *disjunction-node*
 *undercutter-node* *conjunctive-undercutter-node* *ip-number* *is-number* *display-box*
 *quantifier-discount* *package-name* *display-button* *trace-button* *constructed-plans*
  *constructed-goals* *constructed-desires* *plan-number* *goal-number*
 *fixed-ultimate-epistemic-interests* *temporal-decay* *temporal-projection* *causal-implication*
 *new-links* *used-nodes* *used-interests* *unprocessed-nodes* *unprocessed-interests*
 *interests-used-in-proof* *temporal-decay-minimum* *instantiated-premise-number*
 *strictly-relevant-nodes* *not-strictly-relevant-nodes* ug))

(defvar *package-name* (package-name *package*))

(defvar *temporal-projection* nil)
(defvar *causal-implication* nil)
(defvar *temporal-decay* .9999)
(defvar *temporal-decay-minimum* (/ (log .5) (log *temporal-decay*)))
(defvar *pause* nil)
(defvar *time-limit* 5)
(defvar *syntax-loaded* nil)
(defvar *prob-compiler-loaded* nil)
(defvar *problems-loaded* nil)
(defvar *tools-loaded* nil)
(defvar *premises* nil)
(defvar *ultimate-epistemic-interests* nil)
(defvar *permanent-ultimate-epistemic-interests* nil)
(defvar *fixed-ultimate-epistemic-interests* nil)
(defvar *forwards-rules* nil)
(defvar *backwards-rules* nil)
(defvar *auxiliary-forwards-rules* nil)
(defvar *auxiliary-backwards-rules* nil)
(defvar *optative-dispositions* nil)
(defvar *doxastic-optative-dispositions* nil)
(defvar *trees-loaded* nil)
(defvar *display-inference-queue* nil)
(defvar *display?* nil)
(defvar *trace* nil)
(defvar *d-trace* nil)
(defvar *start-trace* nil)
(defvar *start-display* nil)
(defvar *proofs?* nil)
(defvar *use-logic* t)
(defvar *use-reductio* t)
(defvar *log-on* nil)
(defvar *priority-interests* nil)
(defvar *blocked-conclusions* nil)
(defvar *answered-discount* .5)
(defvar *base-priority* .1)
(defvar *reductio-interest* .23)
(defvar *reductio-discount* .23)
(defvar *quantifier-discount* .95)
(defvar *EI-adjustment* 2.5)
(defvar *skolem-multiplier* 10)
(defvar *concluded-interest-priority* .001)
(defvar *forwards-substantive-reasons* nil)
(defvar *backwards-substantive-reasons* nil)
(defvar *environmental-input* nil)
(defvar *executable-operations* nil)
(defvar *assignment-tree-dialog* nil)
(defvar *assignment-tree-subview* nil)
(defvar *monitor-assignment-tree* nil)
(defvar *deductive-only* nil)
(defvar *affected-nodes* nil)
(defvar *graphics-on* nil)
(defvar *graph-log* nil)
(defvar *graphics-pause* nil)

;; This variable is now for MCL only
(defvar oscar-pathname
  #+MCL #p"Macintosh HD:Users:binghe:Lisp:OSCAR-Lisp:")
