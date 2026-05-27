;;; bpftrace.lisp — public API
;;;
;;; SPDX-License-Identifier: MIT
;;;
;;; whistler/bpftrace:compile-script SOURCE   →  generated forms
;;; whistler/bpftrace:run            SOURCE   →  compile, load, attach, print loop
;;; whistler/bpftrace:run-file       PATH     →  read file, then RUN.
;;;
;;; COMPILE-SCRIPT is pure: it returns a plist with the generated
;;; Whistler forms but does not evaluate them. Tests and tools can
;;; inspect the output without involving the kernel.
;;;
;;; RUN evaluates the forms inside a temporary BPF session, attaches
;;; every kernel probe to its target, fires any BEGIN probes
;;; userspace-side, and then loops reading the maps and printing
;;; histograms until SIGINT, at which point END probes fire and the
;;; session is torn down.

(in-package #:whistler/bpftrace)

(defun compile-script (source)
  "Parse SOURCE (a bpftrace script string) and return a plist
   :maps :progs :user-probes :info — see codegen.lisp for the shape."
  (let* ((tree (parse-script source))
         (ast  (normalize tree)))
    (generate ast)))

(defun read-file-to-string (path)
  (with-open-file (s path :direction :input)
    (let* ((buf (make-string (file-length s)))
           (n (read-sequence buf s)))
      (subseq buf 0 n))))

(defun compile-file (path)
  (compile-script (read-file-to-string path)))

;;; ---- run / run-file ----
;;;
;;; The runtime layer is defined in runtime.lisp; this file just calls
;;; into it after parsing.

(defun run (source)
  "Compile, load, and run SOURCE. Blocks until SIGINT, prints map
   contents periodically (default every 1s) and on exit."
  (let ((gen (compile-script source)))
    (run-generated gen)))

(defun run-file (path)
  (run (read-file-to-string path)))
