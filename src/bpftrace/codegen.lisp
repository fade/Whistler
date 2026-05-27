;;; codegen.lisp — AST → Whistler forms
;;;
;;; SPDX-License-Identifier: MIT
;;;
;;; Two passes:
;;;   1. INFER-MAPS walks every probe body, classifies each `@name` by
;;;      how it's written, and assembles a map-info table.
;;;   2. GEN-PROBE emits a (whistler:defprog …) form per kernel probe.
;;;
;;; BEGIN, END and interval probes don't compile to BPF — they run
;;; userspace-only and are returned in the :user-probes plist key so
;;; the runtime can fire them at the right time.

(in-package #:whistler/bpftrace)

;;; ========== Symbols & names ==========

(defun w-sym (name)
  "Intern NAME into the WHISTLER package, dashes for underscores."
  (intern (string-upcase (substitute #\- #\_ name)) :whistler))

(defun var-sym (name)
  "Intern a $-variable name (used inside defprog bodies)."
  (intern (string-upcase (concatenate 'string "$" name)) :whistler))

;;; ========== Map inference ==========

(defstruct minfo
  name             ; whistler symbol (defmap name)
  raw-name         ; original bpftrace name or NIL for anonymous
  kind             ; :counter | :scalar | :hist
  key-size         ; bytes (set by inference; 0 if scalar-only)
  value-size       ; bytes
  max-entries
  key-builtin)     ; hint for printing; :pid / :arg / NIL

(defun builtin-size (kw)
  (case kw
    ((:pid :tid :uid :gid :cpu) 4)
    (t 8)))

(defun expr-size (expr)
  "Best-effort byte-size for EXPR when used as a map key. Must match
   what the lowering will store on the stack — a mismatch trips the
   BPF verifier with `invalid read from stack`."
  (case (first expr)
    (:int     8)
    (:builtin (builtin-size (second expr)))
    (:arg     8)
    (:retval  8)
    (:var     8)
    (:bin     8)
    ;; args->FIELD: tracepoint fields are u32 in the vast majority of
    ;; sched_*, syscalls_*, block_* tracepoints (pid, tid, prev_pid,
    ;; next_pid, prio, state, dev, ...). Default to 4. Phase 2 should
    ;; parse the tracepoint format file for exact widths.
    (:field   (if (and (consp (getf (cdr expr) :base))
                       (eq (first (getf (cdr expr) :base)) :args))
                  4
                  8))
    (t        8)))

(defun key-hint (expr)
  (case (first expr)
    (:builtin (second expr))
    (:arg     :arg)
    (:retval  :retval)
    (t        nil)))

(defun infer-maps (script)
  "Return a hash table RAW-NAME (or \"@\") → MINFO."
  (let ((table (make-hash-table :test 'equal)))
    (labels ((ensure (mref)
               (let* ((raw (getf (cdr mref) :name))
                      (key (or raw "@")))
                 (or (gethash key table)
                     (setf (gethash key table)
                           (make-minfo :name (w-sym (or raw "at"))
                                       :raw-name raw
                                       :kind :counter
                                       :key-size 0
                                       :value-size 8
                                       :max-entries 1024)))))
             (note-keys (mref)
               (let ((info (ensure mref))
                     (keys (getf (cdr mref) :keys)))
                 (when keys
                   (setf (minfo-key-size info)
                         (max (minfo-key-size info)
                              (apply #'+ (mapcar #'expr-size keys))))
                   (when (and (null (minfo-key-builtin info))
                              (= (length keys) 1))
                     (setf (minfo-key-builtin info) (key-hint (first keys)))))))
             (note-rhs (mref rhs)
               (let ((info (ensure mref)))
                 (cond
                   ((and (consp rhs) (eq (first rhs) :call))
                    (let ((fn (getf (cdr rhs) :name)))
                      (cond
                        ((string= fn "count")
                         (setf (minfo-kind info) :counter))
                        ((string= fn "hist")
                         (setf (minfo-kind info) :hist
                               (minfo-key-size info) 4
                               (minfo-max-entries info) 64))
                        ((string= fn "lhist")
                         (setf (minfo-kind info) :hist
                               (minfo-key-size info) 4
                               (minfo-max-entries info) 256)))))
                   (t (when (eq (minfo-kind info) :counter)
                        (setf (minfo-kind info) :scalar)))))))
      (dolist (probe (rest script))
        (let ((body (getf (cdr probe) :body))
              (pred (getf (cdr probe) :predicate)))
          (when pred (when (eq (first pred) :map) (note-keys pred)))
          (dolist (stmt body)
            (case (first stmt)
              (:assign
               (let ((lhs (getf (cdr stmt) :lhs))
                     (rhs (getf (cdr stmt) :rhs)))
                 (when (eq (first lhs) :map)
                   (note-keys lhs)
                   (note-rhs lhs rhs))))
              (:incdec
               (let ((lhs (getf (cdr stmt) :lhs)))
                 (when (eq (first lhs) :map)
                   (note-keys lhs)
                   (setf (minfo-kind (ensure lhs)) :counter))))
              (:expr
               (let ((e (second stmt)))
                 (when (and (consp e) (eq (first e) :call)
                            (or (string= (getf (cdr e) :name) "delete")
                                (string= (getf (cdr e) :name) "clear")
                                (string= (getf (cdr e) :name) "zero"))
                            (consp (first (getf (cdr e) :args)))
                            (eq (first (first (getf (cdr e) :args))) :map))
                   (note-keys (first (getf (cdr e) :args))))))))))
      ;; Histogram maps with no explicit user key always have 4-byte key.
      (loop for info being the hash-values of table
            when (eq (minfo-kind info) :hist)
              do (setf (minfo-key-size info) 4))
      table)))

;;; ========== Defmap forms ==========

(defun gen-defmap (info)
  (let ((mtype (case (minfo-kind info)
                 (:hist :percpu-array)
                 (t     :hash))))
    `(whistler:defmap ,(minfo-name info)
       :type ,mtype
       :key-size ,(if (eq mtype :percpu-array) 4 (max 1 (minfo-key-size info)))
       :value-size ,(minfo-value-size info)
       :max-entries ,(or (minfo-max-entries info)
                         (if (eq mtype :percpu-array) 64 1024)))))

;;; ========== Expression lowering ==========

(defvar *probe-spec* nil)
(defvar *map-table* nil)

(defun lower-expr (expr)
  (ecase (first expr)
    (:int        (second expr))
    (:str        (second expr))
    (:var        (var-sym (second expr)))
    (:builtin    (lower-builtin (second expr)))
    (:arg        (lower-arg (second expr)))
    (:retval     (lower-retval))
    (:comm       (unsupported "comm in expression position"))
    (:args       (unsupported "args without ->field"))
    (:probe-name (unsupported "probe builtin"))
    (:func       (unsupported "func builtin"))
    (:bin        (lower-bin expr))
    (:un         (lower-un expr))
    (:tern       (lower-tern expr))
    (:call       (lower-call expr))
    (:field      (lower-field expr))
    (:index      (unsupported "array indexing outside @maps"))
    (:map        (lower-map-read expr))))

(defun lower-builtin (kw)
  (case kw
    (:pid    `(whistler::ash (whistler::get-current-pid-tgid) -32))
    (:tid    `(whistler::logand (whistler::get-current-pid-tgid) #xffffffff))
    (:uid    `(whistler::logand (whistler::get-current-uid-gid)  #xffffffff))
    (:gid    `(whistler::ash (whistler::get-current-uid-gid)  -32))
    (:nsecs  '(whistler::ktime-get-ns))
    (:cpu    '(whistler::get-smp-processor-id))
    (:cgroup '(whistler::get-current-cgroup-id))
    (:rand   '(whistler::get-prandom-u32))
    (t       (unsupported "builtin ~A" kw))))

(defun lower-arg (n)
  (ecase (first *probe-spec*)
    (:kprobe
     (case n
       (0 '(whistler:pt-regs-parm1)) (1 '(whistler:pt-regs-parm2))
       (2 '(whistler:pt-regs-parm3)) (3 '(whistler:pt-regs-parm4))
       (4 '(whistler:pt-regs-parm5)) (5 '(whistler:pt-regs-parm6))
       (t (unsupported "arg~D — only arg0..arg5 are wired up" n))))
    (:kretprobe (unsupported "arg~D in kretprobe — retval is the only accessor" n))
    (:tracepoint (unsupported "tracepoint arg~D — use args->field" n))))

(defun lower-retval ()
  (ecase (first *probe-spec*)
    (:kretprobe '(whistler:pt-regs-ret))))

(defun lower-bin (expr)
  (let ((op  (getf (cdr expr) :op))
        (lhs (lower-expr (getf (cdr expr) :lhs)))
        (rhs (lower-expr (getf (cdr expr) :rhs))))
    (ecase op
      (:+    `(whistler::+ ,lhs ,rhs))
      (:-    `(whistler::- ,lhs ,rhs))
      (:*    `(whistler::* ,lhs ,rhs))
      (:/    `(whistler::/ ,lhs ,rhs))
      (:%    `(whistler::mod ,lhs ,rhs))
      (:==   `(whistler::= ,lhs ,rhs))
      (:!=   `(whistler::/= ,lhs ,rhs))
      (:<    `(whistler::< ,lhs ,rhs))
      (:>    `(whistler::> ,lhs ,rhs))
      (:<=   `(whistler::<= ,lhs ,rhs))
      (:>=   `(whistler::>= ,lhs ,rhs))
      (:&&   `(whistler::and ,lhs ,rhs))
      (:\|\| `(whistler::or ,lhs ,rhs))
      (:&    `(whistler::logand ,lhs ,rhs))
      (:\|   `(whistler::logior ,lhs ,rhs))
      (:^    `(whistler::logxor ,lhs ,rhs))
      (:<<   `(whistler::ash ,lhs ,rhs))
      (:>>   `(whistler::>> ,lhs ,rhs)))))

(defun lower-un (expr)
  (let ((op  (getf (cdr expr) :op))
        (arg (lower-expr (getf (cdr expr) :arg))))
    (ecase op
      (:!  `(whistler::if ,arg 0 1))
      (:-  `(whistler::- 0 ,arg))
      (:~  `(whistler::logxor ,arg #xffffffffffffffff)))))

(defun lower-tern (expr)
  `(whistler::if ,(lower-expr (getf (cdr expr) :cond))
                      ,(lower-expr (getf (cdr expr) :then))
                      ,(lower-expr (getf (cdr expr) :else))))

(defun lower-call (expr)
  (let ((name (getf (cdr expr) :name)))
    (cond
      ((string= name "count") (unsupported "count() must be on the RHS of @map = …"))
      ((string= name "hist")  (unsupported "hist() must be on the RHS of @map = …"))
      ((string= name "lhist") (unsupported "lhist() — Phase 1 ships hist() only"))
      ((string= name "exit")  0)            ; exit() is userspace-only
      ((string= name "printf") 0)           ; printf() is userspace-only
      ((string= name "clear") 0)
      ((string= name "zero")  0)
      ((string= name "delete") 0)           ; lower-expr-stmt handles the real call
      (t (unsupported "function ~A" name)))))

(defun lower-field (expr)
  (let ((base (getf (cdr expr) :base))
        (name (getf (cdr expr) :name)))
    (cond
      ((and (consp base) (eq (first base) :args))
       (list (w-sym (concatenate 'string "tp-" name))))
      (t (unsupported "field access .~A on non-args expressions" name)))))

(defun lower-key-form (keys)
  (cond
    ((null keys)           0)
    ((= (length keys) 1)   (lower-expr (first keys)))
    (t (unsupported "composite map keys (~D parts) — Phase 1 supports 1 key"
                    (length keys)))))

(defun lower-map-read (expr)
  (let* ((info (or (gethash (or (getf (cdr expr) :name) "@") *map-table*)
                   (unsupported "unknown map @~A" (getf (cdr expr) :name))))
         (mname (minfo-name info))
         (keys  (getf (cdr expr) :keys))
         (key   (lower-key-form keys)))
    `(whistler:getmap ,mname ,key)))

;;; ========== Statement lowering ==========

(defun collect-vars (stmts)
  "Collect every $var name written or read inside STMTS. Returns a list
   of (canonical) symbols suitable for binding."
  (let ((seen (make-hash-table :test 'equal)))
    (labels ((walk (form)
               (when (consp form)
                 (case (first form)
                   (:var (setf (gethash (second form) seen) t))
                   (:bin   (walk (getf (cdr form) :lhs))
                           (walk (getf (cdr form) :rhs)))
                   (:un    (walk (getf (cdr form) :arg)))
                   (:tern  (walk (getf (cdr form) :cond))
                           (walk (getf (cdr form) :then))
                           (walk (getf (cdr form) :else)))
                   (:call  (dolist (a (getf (cdr form) :args)) (walk a)))
                   (:field (walk (getf (cdr form) :base)))
                   (:index (walk (getf (cdr form) :base))
                           (dolist (k (getf (cdr form) :keys)) (walk k)))
                   (:map   (dolist (k (getf (cdr form) :keys)) (walk k)))))))
      (labels ((walk-stmt (s)
                 (case (first s)
                   (:if      (walk (getf (cdr s) :cond))
                             (mapc #'walk-stmt (getf (cdr s) :then))
                             (mapc #'walk-stmt (getf (cdr s) :else)))
                   (:assign  (walk (getf (cdr s) :rhs))
                             (let ((lhs (getf (cdr s) :lhs)))
                               (when (eq (first lhs) :var)
                                 (setf (gethash (second lhs) seen) t))
                               (walk lhs)))
                   (:incdec  (walk (getf (cdr s) :lhs)))
                   (:expr    (walk (second s))))))
        (mapc #'walk-stmt stmts))
      (loop for k being the hash-keys of seen collect (var-sym k)))))

(defun lower-stmts (stmts)
  (mapcar #'lower-stmt stmts))

(defun lower-stmt (stmt)
  (ecase (first stmt)
    (:if      (lower-if stmt))
    (:assign  (lower-assign stmt))
    (:incdec  (lower-incdec stmt))
    (:expr    (lower-expr-stmt stmt))))

(defun lower-if (stmt)
  (let ((c (lower-expr (getf (cdr stmt) :cond)))
        (then (lower-stmts (getf (cdr stmt) :then)))
        (else (lower-stmts (getf (cdr stmt) :else))))
    (if else
        `(whistler::if ,c (progn ,@then) (progn ,@else))
        `(when ,c ,@then))))

(defun lower-assign (stmt)
  (let* ((lhs (getf (cdr stmt) :lhs))
         (op  (getf (cdr stmt) :op))
         (rhs (getf (cdr stmt) :rhs)))
    (ecase (first lhs)
      (:var
       (let ((sym (var-sym (second lhs))))
         (ecase op
           (:=  `(setf ,sym ,(lower-expr rhs)))
           (:+= `(whistler:incf ,sym ,(lower-expr rhs)))
           (:-= `(whistler:decf ,sym ,(lower-expr rhs))))))
      (:map (lower-map-assign lhs op rhs)))))

(defun lower-map-assign (mref op rhs)
  (let* ((info (or (gethash (or (getf (cdr mref) :name) "@") *map-table*)
                   (error "internal: missing map ~A" (getf (cdr mref) :name))))
         (mname (minfo-name info))
         (key   (lower-key-form (getf (cdr mref) :keys))))
    (cond
      ((and (consp rhs) (eq (first rhs) :call))
       (let ((fn (getf (cdr rhs) :name)))
         (cond
           ((string= fn "count")
            `(whistler:incf (whistler:getmap ,mname ,key)))
           ((string= fn "hist")
            (gen-hist-update mname (lower-expr (first (getf (cdr rhs) :args)))))
           ((string= fn "lhist")
            (unsupported "lhist() — Phase 1 ships hist() only"))
           (t (gen-scalar-set mname key (lower-expr rhs) op)))))
      (t (gen-scalar-set mname key (lower-expr rhs) op)))))

(defun gen-scalar-set (mname key value op)
  (ecase op
    (:=  `(setf (whistler:getmap ,mname ,key) ,value))
    (:+= `(whistler:incf (whistler:getmap ,mname ,key) ,value))
    (:-= `(whistler:decf (whistler:getmap ,mname ,key) ,value))))

(defun gen-hist-update (mname value-form)
  (let ((val  (gensym "V"))
        (slot (gensym "S"))
        (p    (gensym "P")))
    `(let* ((,val ,value-form)
                    (,slot (whistler::log2 ,val)))
       (when (whistler::>= ,slot 64) (setf ,slot 63))
       (whistler:when-let ((,p (whistler::map-lookup ,mname ,slot)))
         (whistler::atomic-add ,p 0 1)))))

(defun lower-incdec (stmt)
  (let* ((lhs   (getf (cdr stmt) :lhs))
         (op    (getf (cdr stmt) :op))
         (info  (or (gethash (or (getf (cdr lhs) :name) "@") *map-table*)
                    (error "internal: missing map ~A" (getf (cdr lhs) :name))))
         (mname (minfo-name info))
         (key   (lower-key-form (getf (cdr lhs) :keys))))
    (ecase op
      (:inc `(whistler:incf (whistler:getmap ,mname ,key)))
      (:dec `(whistler:decf (whistler:getmap ,mname ,key))))))

(defun lower-expr-stmt (stmt)
  (let ((e (second stmt)))
    (cond
      ((and (consp e) (eq (first e) :call)
            (string= (getf (cdr e) :name) "delete"))
       (let* ((arg (first (getf (cdr e) :args)))
              (info (or (gethash (or (getf (cdr arg) :name) "@") *map-table*)
                        (error "internal: delete of unknown @map")))
              (mname (minfo-name info)))
         `(whistler:remmap ,mname ,(lower-key-form (getf (cdr arg) :keys)))))
      ;; clear/zero/printf/exit are userspace-only — kernel side is a no-op.
      ((and (consp e) (eq (first e) :call)
            (member (getf (cdr e) :name)
                    '("clear" "zero" "printf" "exit" "time")
                    :test #'string=))
       0)
      (t (lower-expr e)))))

;;; ========== Probe lowering ==========

(defparameter *kernel-spec-tags* '(:kprobe :kretprobe :tracepoint))

(defun spec->section (spec)
  (ecase (first spec)
    (:kprobe     (values :kprobe       (format nil "kprobe/~A" (second spec))))
    (:kretprobe  (values :kretprobe    (format nil "kretprobe/~A" (second spec))))
    (:tracepoint (values :tracepoint
                         (format nil "tracepoint/~A/~A" (second spec) (third spec))))))

(defun gen-probe-forms (probe index)
  "Return ((kernel-form …) (user-spec …)) for PROBE — multiple specs
   may share a body, so we emit one defprog per kernel spec and one
   user-side entry per user spec."
  (let* ((specs (getf (cdr probe) :specs))
         (pred  (getf (cdr probe) :predicate))
         (body  (getf (cdr probe) :body))
         (kernel-forms nil)
         (user-specs nil))
    (loop for spec in specs
          for sub from 0
          do (cond
               ((member (first spec) *kernel-spec-tags*)
                (push (gen-kernel-prog spec pred body index sub) kernel-forms))
               (t (push (list :spec spec :body body) user-specs))))
    (values (nreverse kernel-forms) (nreverse user-specs))))

(defun gen-kernel-prog (spec pred body index sub)
  (multiple-value-bind (ptype section) (spec->section spec)
    (let* ((*probe-spec* spec)
           (prog-name (intern (format nil "BT-PROBE-~D-~D" index sub) :whistler))
           (vars      (collect-vars body))
           (body-forms (lower-stmts body))
           (pred-form (when pred (lower-expr pred)))
           (gated (if pred-form
                      `((when ,pred-form ,@body-forms))
                      body-forms))
           (with-vars (if vars
                          `((let* ,(loop for v in vars collect `(,v 0))
                              ,@gated 0))
                          (append gated '(0)))))
      `(whistler:defprog ,prog-name
           (:type ,ptype :section ,section :license "GPL")
         ,@with-vars))))

(defun collect-tracepoint-fields (script)
  "Walk SCRIPT and return ((CAT EVENT) . (FIELD …)) entries —
   one per unique tracepoint, with the union of args->FIELD names
   referenced by any probe attached to it. Used to emit a single
   (deftracepoint …) at the top so common field macros aren't
   redefined per probe."
  (let ((table (make-hash-table :test 'equal)))
    (labels ((collect-fields (form acc)
               (cond
                 ((not (consp form)) acc)
                 ((and (eq (first form) :field)
                       (consp (getf (cdr form) :base))
                       (eq (first (getf (cdr form) :base)) :args))
                  (cons (getf (cdr form) :name)
                        ;; Field nodes can still contain nested args->X if
                        ;; someone wrote args->a.b — recurse to be safe.
                        (reduce (lambda (a x) (collect-fields x a))
                                (rest form) :initial-value acc)))
                 (t
                  ;; Walk every child whether or not the head is a keyword:
                  ;; the keys list of a :map is a plain list of nodes that
                  ;; itself isn't tagged, so reduce over the *whole* form
                  ;; including head — recurse on every cons cell.
                  (reduce (lambda (a x) (collect-fields x a))
                          form :initial-value acc)))))
      (dolist (probe (rest script))
        (let ((body (getf (cdr probe) :body)))
          (dolist (spec (getf (cdr probe) :specs))
            (when (eq (first spec) :tracepoint)
              (let* ((key (list (second spec) (third spec)))
                     (cur (gethash key table))
                     (here (reduce (lambda (a s) (collect-fields s a))
                                   body :initial-value nil)))
                (setf (gethash key table)
                      (remove-duplicates (append cur here) :test #'string=))))))))
    (loop for k being the hash-keys of table
          using (hash-value v)
          collect (cons k v))))

(defun gen-deftracepoint-preamble (script)
  "Emit one (deftracepoint …) per unique tracepoint. To avoid
   `redefining TP-X' warnings when the same field name (e.g. `pid')
   appears in several tracepoints, every field name is emitted into
   exactly one deftracepoint — the first tracepoint that references
   it. This is safe as long as same-named fields share offsets across
   the tracepoints involved (true for the sched_/syscalls_/block_
   families that share a common prefix layout)."
  (let ((emitted-fields (make-hash-table :test 'equal)))
    (loop for entry in (collect-tracepoint-fields script)
          for (cat event) = (car entry)
          for fields      = (cdr entry)
          for new-fields  = (loop for f in fields
                                  unless (gethash f emitted-fields)
                                    collect (progn
                                              (setf (gethash f emitted-fields) t)
                                              f))
          ;; Skip when this tracepoint contributes no new field names.
          ;; whistler:deftracepoint with no fields means "import them
          ;; all", which would re-define the same tp-X macros and
          ;; trigger redefinition warnings.
          when new-fields
            collect `(whistler:deftracepoint
                         ,(intern (format nil "~A/~A"
                                          (string-upcase cat)
                                          (substitute #\- #\_ (string-upcase event)))
                                  :whistler)
                       ,@(mapcar (lambda (f) (w-sym f)) new-fields)))))

;;; ========== Public entry ==========

(defun generate (script)
  "Translate normalised SCRIPT to a plist:
     :maps        (defmap forms)
     :progs       (defprog/preamble forms, one per kernel probe)
     :user-probes (list of (:spec … :body …) for BEGIN/END/interval)
     :info        (raw-name :name :kind :key-builtin :key-size :value-size :max-entries)"
  (let* ((map-table (infer-maps script))
         (*map-table* map-table)
         (maps      (loop for info being the hash-values of map-table
                          collect (gen-defmap info)))
         (probes    nil)
         (user      nil)
         (tp-preamble (gen-deftracepoint-preamble script)))
    (loop for probe in (rest script)
          for i from 0
          do (multiple-value-bind (kforms us) (gen-probe-forms probe i)
               (setf probes (append probes kforms)
                     user   (append user us))))
    (list :maps maps
          :progs (append tp-preamble probes)
          :user-probes user
          :info (loop for raw being the hash-keys of map-table
                      using (hash-value info)
                      collect (list (or raw "@")
                                    :name (minfo-name info)
                                    :kind (minfo-kind info)
                                    :key-builtin (minfo-key-builtin info)
                                    :key-size (minfo-key-size info)
                                    :value-size (minfo-value-size info)
                                    :max-entries (minfo-max-entries info))))))
