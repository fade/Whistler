;;; runtime.lisp — userspace runtime (load, attach, print loop)
;;;
;;; SPDX-License-Identifier: MIT
;;;
;;; Given a generated plist from codegen.lisp, builds a live BPF
;;; session: compiles the defmap/defprog forms, creates the maps,
;;; loads the programs, attaches every kernel probe by parsing the
;;; ELF section name, then enters a print loop that periodically
;;; dumps each map's contents in a bpftrace-style layout.

(in-package #:whistler/bpftrace)

;;; ========== Compiling generated forms ==========

(defun compile-generated (gen)
  "Run the BPF compiler over the maps + programs in GEN.
   Returns (values map-specs prog-specs info-list) — same as
   compile-bpf-forms but driven by our dynamically generated forms.
   :info is augmented with the map's runtime key/value sizes so the
   printer doesn't have to re-introspect."
  (let* ((map-forms  (getf gen :maps))
         (prog-forms (getf gen :progs))
         (info-list  (getf gen :info)))
    (multiple-value-bind (map-specs prog-specs)
        (whistler/loader::compile-bpf-forms map-forms prog-forms)
      (values map-specs prog-specs info-list))))

;;; ========== Attaching kernel probes ==========

(defun split-section (section)
  "Split \"kprobe/foo\" or \"tracepoint/cat/event\" into a list of parts."
  (let ((parts nil)
        (start 0))
    (loop for i from 0 below (length section)
          when (char= (char section i) #\/)
            do (push (subseq section start i) parts)
               (setf start (1+ i)))
    (push (subseq section start) parts)
    (nreverse parts)))

(defun attach-probe (prog-info)
  "Inspect the program's section name and call the appropriate attach-*.
   Translates BPF errors into BPFTRACE-ATTACH-ERROR with hints."
  (let* ((section (whistler/loader::prog-info-section-name prog-info))
         (parts   (split-section section))
         (kind    (first parts))
         (target  (if (string= kind "tracepoint")
                      section
                      (second parts)))
         (fd      (whistler/loader::prog-info-fd prog-info)))
    (handler-case
        (cond
          ((string= kind "kprobe")
           (whistler/loader:attach-kprobe fd target))
          ((string= kind "kretprobe")
           (whistler/loader:attach-kprobe fd target :retprobe t))
          ((string= kind "tracepoint")
           (whistler/loader:attach-tracepoint fd target))
          (t (error 'bpftrace-attach-error
                    :section section :target target
                    :reason (format nil "unknown probe kind ~A" kind))))
      (error (e)
        (error 'bpftrace-attach-error
               :section section :target target :reason e)))))

(define-condition bpftrace-attach-error (error)
  ((section :initarg :section :reader attach-error-section)
   (target  :initarg :target  :reader attach-error-target)
   (reason  :initarg :reason  :reader attach-error-reason))
  (:report
   (lambda (c s)
     (format s "failed to attach probe ~A (target ~A): ~A"
             (attach-error-section c) (attach-error-target c)
             (attach-error-reason c))
     (let ((kind (first (split-section (attach-error-section c)))))
       (cond
         ((or (string= kind "kprobe") (string= kind "kretprobe"))
          (format s "~%~
                  Hint: ~A may not exist on this kernel.~%~
                        Check /proc/kallsyms or /sys/kernel/tracing/available_filter_functions.~%~
                        For storage I/O latency on modern kernels, use~%~
                          tracepoint:block:block_rq_issue / block_rq_complete~%~
                        (note: those require composite keys, not in Phase 1)."
                  (attach-error-target c)))
         ((string= kind "tracepoint")
          (format s "~%~
                  Hint: ensure the tracepoint exists in /sys/kernel/tracing/events.~%~
                        Run as root and make sure tracefs is mounted.")))))))

;;; ========== Pretty-printing maps ==========

(defun map-keys (info)
  "Walk the map (or array) and return a list of integer keys present."
  (let ((keys nil)
        (cur  nil))
    (loop
      (let ((next (whistler/loader::map-get-next-key
                   info
                   (or cur (whistler/loader::encode-int-key
                            0
                            (whistler/loader::map-info-key-size info))))))
        (unless next (return))
        (push (whistler/loader::decode-int-value next) keys)
        (setf cur next)))
    (nreverse keys)))

(defun lookup-int (info key)
  (let ((bytes (whistler/loader::map-lookup-int info key)))
    (or bytes 0)))

(defun lookup-percpu-sum (info key)
  "For a percpu map, sum the per-CPU values at KEY (treated as u64)."
  (let* ((kbytes (whistler/loader::encode-int-key
                  key (whistler/loader::map-info-key-size info)))
         (per (whistler/loader::map-lookup info kbytes)))
    (if (and per (vectorp per))
        (loop for cpu-val across per
              sum (whistler/loader::decode-int-value cpu-val))
        0)))

(defun render-bar (count maxc width)
  (if (zerop maxc) ""
      (let* ((n (round (/ (* count width) maxc)))
             (out (make-string width :initial-element #\Space)))
        (dotimes (i n) (when (< i width) (setf (char out i) #\@)))
        out)))

(defun format-key (key)
  "Render KEY (an integer) as bpftrace does: bare decimal."
  (format nil "~D" key))

(defun si-number (n)
  "bpftrace-style SI suffix: 1024 → \"1K\", 1048576 → \"1M\"."
  (cond ((>= n (ash 1 60)) (format nil "~D~A" (ash n -60) "E"))
        ((>= n (ash 1 50)) (format nil "~D~A" (ash n -50) "P"))
        ((>= n (ash 1 40)) (format nil "~D~A" (ash n -40) "T"))
        ((>= n (ash 1 30)) (format nil "~D~A" (ash n -30) "G"))
        ((>= n (ash 1 20)) (format nil "~D~A" (ash n -20) "M"))
        ((>= n (ash 1 10)) (format nil "~D~A" (ash n -10) "K"))
        (t (format nil "~D" n))))

(defun hist-bucket-label (i)
  "bpftrace's bucket labels: [0], [1], [2, 4), [4, 8), …"
  (case i
    (0 "[0]")
    (1 "[1]")
    (t (format nil "[~A, ~A)"
               (si-number (ash 1 (1- i)))
               (si-number (ash 1 i))))))

(defun print-hist (label info)
  "Render a log2 histogram (percpu-array of u64, 64 buckets), bpftrace style."
  (let* ((buckets (loop for i below 64
                        collect (lookup-percpu-sum info i)))
         (last    (or (position-if-not #'zerop buckets :from-end t) -1))
         (maxc    (or (reduce #'max buckets) 0)))
    (format t "~%@~A:~%" label)
    (when (minusp last)
      (format t "    (no samples)~%")
      (return-from print-hist))
    (loop for i from 0 to last
          for count = (nth i buckets)
          do (format t "~16A ~10D |~A|~%"
                     (hist-bucket-label i)
                     count
                     (render-bar count maxc 52)))))

(defun print-scalar-map (label info)
  "Print a hash map's contents in bpftrace's END-dump style:
   @LABEL[key]: count, one per line, sorted ascending by count.
   Anonymous maps (`@[k]++` with no name) print as `@[k]: …`."
  (let* ((keys (map-keys info))
         (pairs (sort (mapcar (lambda (k) (cons k (lookup-int info k))) keys)
                      #'< :key #'cdr))
         (prefix (if (or (null label) (string= label "@")) "@" (format nil "@~A" label))))
    (dolist (kv pairs)
      (format t "~A[~A]: ~D~%" prefix (format-key (car kv)) (cdr kv)))))

(defun print-all-maps (info-list map-alist)
  "Dump every known map in bpftrace END style."
  (dolist (info-rec info-list)
    (let* ((raw-name    (first info-rec))
           (mname       (getf (cdr info-rec) :name))
           (kind        (getf (cdr info-rec) :kind))
           (alist-key   (string-downcase
                         (substitute #\_ #\- (symbol-name mname))))
           (entry       (assoc alist-key map-alist :test #'string=))
           (mapinfo     (when entry (cdr entry))))
      (when mapinfo
        (case kind
          (:hist (print-hist raw-name mapinfo))
          (t     (print-scalar-map raw-name mapinfo)))))))

;;; ========== Userspace BEGIN/END ==========

(defun run-user-probe (probe)
  "Run a BEGIN/END/interval probe userspace-side. Phase 1 only
   recognises (printf …) inside these blocks; everything else is
   skipped with a notice."
  (dolist (stmt (getf probe :body))
    (when (and (consp stmt) (eq (first stmt) :expr))
      (let ((e (second stmt)))
        (when (and (consp e) (eq (first e) :call)
                   (string= (getf (cdr e) :name) "printf"))
          (let ((args (getf (cdr e) :args)))
            (when (and args (eq (first (first args)) :str))
              (format t "~A" (second (first args)))
              (force-output))))))))

;;; ========== The runtime entry ==========

(defvar *bpftrace-running* nil)

(defun run-generated (gen)
  "Bring up GEN as a live BPF session and block until Ctrl-C.
   Maps are dumped once on exit, matching real bpftrace's behavior
   for scripts without an explicit interval: probe."
  (multiple-value-bind (map-specs prog-specs info-list)
      (compile-generated gen)
    (let* ((map-alist  (whistler/loader::session-create-maps map-specs))
           (prog-alist (whistler/loader::session-load-progs prog-specs map-alist))
           (atts       nil)
           (user       (getf gen :user-probes)))
      (unwind-protect
           (handler-case
               (progn
                 (dolist (entry prog-alist)
                   (push (attach-probe (cdr entry)) atts))
                 ;; BEGIN probes
                 (dolist (p user)
                   (when (eq (first (getf p :spec)) :begin)
                     (run-user-probe p)))
                 ;; Sleep until interrupted.
                 (setf *bpftrace-running* t)
                 (handler-case
                     (loop while *bpftrace-running* do (sleep 1))
                   (sb-sys:interactive-interrupt ()
                     (format t "~&^C~%"))))
             (bpftrace-attach-error (e)
               (format *error-output* "~&~A~%" e)))
        ;; END probes + final dump.
        (dolist (p user)
          (when (eq (first (getf p :spec)) :end)
            (run-user-probe p)))
        (print-all-maps info-list map-alist)
        (dolist (a atts) (handler-case (whistler/loader::detach a) (error () nil)))
        (dolist (e prog-alist)
          (let ((fd (whistler/loader::prog-info-fd (cdr e))))
            (when (plusp fd)
              (handler-case (sb-posix:close fd) (error () nil)))))
        (dolist (e map-alist)
          (let ((fd (whistler/loader::map-info-fd (cdr e))))
            (when (plusp fd)
              (handler-case (sb-posix:close fd) (error () nil)))))))))
