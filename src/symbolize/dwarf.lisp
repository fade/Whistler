;;; dwarf.lisp — minimal DWARF .debug_line reader
;;;
;;; SPDX-License-Identifier: MIT
;;;
;;; Parses the `.debug_line' section of an ELF debug file and turns
;;; it into a sorted address → (file . line) table. Just enough to
;;; render `file:line' alongside each frame of a userspace stack
;;; trace; no .debug_info, no DIE walking, no inline frames (those
;;; live in a future PR).
;;;
;;; Supports DWARF 4 and DWARF 5 line-number programs. The output of
;;; the line-program state machine is a sequence of rows, each one a
;;; (vaddr, file-index, line) triple. We collect every row from every
;;; compilation unit into three parallel arrays, sort by vaddr, and
;;; binary-search at lookup time.
;;;
;;; Forms we recognise in DWARF 5 entry-format tables:
;;;   DW_FORM_data1/2/4/8/16, udata, sdata, flag, string, strp,
;;;   line_strp. Anything else aborts parsing for that CU.

(in-package #:whistler/symbolize)

;;; ========== LEB128 ==========

(defun uleb128 (buf off)
  "Decode an unsigned LEB128 from BUF starting at OFF.
   Returns (values VALUE BYTES-CONSUMED)."
  (let ((result 0) (shift 0) (n 0))
    (loop
      (let ((byte (aref buf (+ off n))))
        (incf n)
        (setf result (logior result (ash (logand byte #x7f) shift)))
        (incf shift 7)
        (when (zerop (logand byte #x80))
          (return (values result n)))))))

(defun sleb128 (buf off)
  "Decode a signed LEB128. Returns (values VALUE BYTES-CONSUMED)."
  (let ((result 0) (shift 0) (n 0))
    (loop
      (let ((byte (aref buf (+ off n))))
        (incf n)
        (setf result (logior result (ash (logand byte #x7f) shift)))
        (incf shift 7)
        (when (zerop (logand byte #x80))
          (when (and (< shift 64) (not (zerop (logand byte #x40))))
            (setf result (logior result (ash -1 shift))))
          (return (values result n)))))))

(defun cstring-at* (buf off)
  "Like cstring-at, but also returns bytes consumed (string length + NUL)."
  (let ((end off) (n (length buf)))
    (loop while (and (< end n) (not (zerop (aref buf end))))
          do (incf end))
    (values
     (sb-ext:octets-to-string buf :start off :end end :external-format :utf-8)
     (- (1+ end) off))))

;;; ========== DWARF constants ==========

(defconstant +dw-lns-copy+                #x01)
(defconstant +dw-lns-advance-pc+          #x02)
(defconstant +dw-lns-advance-line+        #x03)
(defconstant +dw-lns-set-file+            #x04)
(defconstant +dw-lns-set-column+          #x05)
(defconstant +dw-lns-negate-stmt+         #x06)
(defconstant +dw-lns-set-basic-block+     #x07)
(defconstant +dw-lns-const-add-pc+        #x08)
(defconstant +dw-lns-fixed-advance-pc+    #x09)
(defconstant +dw-lns-set-prologue-end+    #x0a)
(defconstant +dw-lns-set-epilogue-begin+  #x0b)
(defconstant +dw-lns-set-isa+             #x0c)

(defconstant +dw-lne-end-sequence+        #x01)
(defconstant +dw-lne-set-address+         #x02)
(defconstant +dw-lne-define-file+         #x03)
(defconstant +dw-lne-set-discriminator+   #x04)

(defconstant +dw-lnct-path+               #x01)
(defconstant +dw-lnct-directory-index+    #x02)
(defconstant +dw-lnct-timestamp+          #x03)
(defconstant +dw-lnct-size+               #x04)
(defconstant +dw-lnct-md5+                #x05)

(defconstant +dw-form-addr+               #x01)
(defconstant +dw-form-data2+              #x05)
(defconstant +dw-form-data4+              #x06)
(defconstant +dw-form-data8+              #x07)
(defconstant +dw-form-string+             #x08)
(defconstant +dw-form-block+              #x09)
(defconstant +dw-form-block1+             #x0a)
(defconstant +dw-form-data1+              #x0b)
(defconstant +dw-form-flag+               #x0c)
(defconstant +dw-form-sdata+              #x0d)
(defconstant +dw-form-strp+               #x0e)
(defconstant +dw-form-udata+              #x0f)
(defconstant +dw-form-data16+             #x1e)
(defconstant +dw-form-line-strp+          #x1f)

;;; ========== Form readers ==========
;;;
;;; A form reader returns (values VALUE BYTES-CONSUMED). VALUE is a
;;; string for the path forms, a number for everything else, and we
;;; don't care about its semantics for fields other than path and
;;; directory-index.

(defun read-form (buf off form line-str debug-str)
  "Read a value encoded with FORM at OFF. Returns
   (values VALUE BYTES). Throws on an unsupported form; caller is
   expected to catch and abort this CU."
  (cond
    ((= form +dw-form-data1+)  (values (u8  buf off) 1))
    ((= form +dw-form-data2+)  (values (u16 buf off) 2))
    ((= form +dw-form-data4+)  (values (u32 buf off) 4))
    ((= form +dw-form-data8+)  (values (u64 buf off) 8))
    ((= form +dw-form-data16+) (values nil           16))
    ((= form +dw-form-flag+)   (values (u8  buf off) 1))
    ((= form +dw-form-udata+)  (uleb128 buf off))
    ((= form +dw-form-sdata+)  (sleb128 buf off))
    ((= form +dw-form-string+) (cstring-at* buf off))
    ((= form +dw-form-strp+)
     (let ((o (u32 buf off)))
       (values (and debug-str (cstring-at debug-str o)) 4)))
    ((= form +dw-form-line-strp+)
     (let ((o (u32 buf off)))
       (values (and line-str (cstring-at line-str o)) 4)))
    (t (error "Unsupported DWARF form ~D" form))))

(defun read-entry-format (buf off)
  "Read a DWARF 5 entry-format descriptor (used for directories and
   file_names). Returns (values FORMAT-LIST BYTES-CONSUMED), where
   FORMAT-LIST is a list of (CONTENT-CODE . FORM-CODE) pairs."
  (let* ((count (u8 buf off))
         (n 1)
         (acc '()))
    (dotimes (i count)
      (multiple-value-bind (ct used) (uleb128 buf (+ off n))
        (incf n used)
        (multiple-value-bind (fm used2) (uleb128 buf (+ off n))
          (incf n used2)
          (push (cons ct fm) acc))))
    (values (nreverse acc) n)))

(defun read-entry (buf off fmt line-str debug-str)
  "Read one entry using FMT (list of (content-code . form)).
   Returns (values PATH DIR-INDEX BYTES-CONSUMED)."
  (let ((n 0) (path nil) (dir 0))
    (dolist (slot fmt)
      (multiple-value-bind (val used)
          (read-form buf (+ off n) (cdr slot) line-str debug-str)
        (incf n used)
        (cond
          ((= (car slot) +dw-lnct-path+)            (setf path val))
          ((= (car slot) +dw-lnct-directory-index+) (setf dir (or val 0))))))
    (values path dir n)))

;;; ========== Sequence/row collection ==========

(defstruct collector
  (vaddrs (make-array 4096 :element-type '(unsigned-byte 64)
                          :adjustable t :fill-pointer 0))
  (file-idx (make-array 4096 :element-type '(unsigned-byte 32)
                            :adjustable t :fill-pointer 0))
  (lines (make-array 4096 :element-type '(unsigned-byte 32)
                         :adjustable t :fill-pointer 0))
  (files-out (make-array 64 :adjustable t :fill-pointer 0)))

(defun collector-push-row (c vaddr file-idx line)
  (when (plusp vaddr)
    (vector-push-extend vaddr     (collector-vaddrs c))
    (vector-push-extend file-idx  (collector-file-idx c))
    (vector-push-extend line      (collector-lines c))))

(defun collector-intern-files (c per-cu-paths)
  "Append PER-CU-PATHS (a list of full path strings) to the collector's
   global file vector. Returns the base index this CU's files start at."
  (let ((base (length (collector-files-out c))))
    (dolist (p per-cu-paths)
      (vector-push-extend (or p "") (collector-files-out c)))
    base))

;;; ========== Line program parsing ==========

(defun parse-cu (buf off c line-str debug-str)
  "Parse the line-number program starting at OFF inside BUF. Pushes
   rows into C. Returns the offset just past this CU's payload (so
   the caller can move on to the next CU). Returns NIL on parse
   failure — the caller treats that as end-of-section."
  (handler-case
      (parse-cu* buf off c line-str debug-str)
    (error () nil)))

(defun parse-cu* (buf off c line-str debug-str)
  (let ((unit-length (u32 buf off)))
    (when (= unit-length #xffffffff)
      (error "DWARF64 line section unsupported"))
    (let* ((unit-end (+ off 4 unit-length))
           (version  (u16 buf (+ off 4))))
      (cond
        ((= version 5)        (parse-cu-v5 buf off unit-end c line-str debug-str))
        ((<= 2 version 4)     (parse-cu-v4 buf off unit-end c line-str debug-str))
        (t                    unit-end)))))

(defun read-common-header (buf cur version)
  "Read min-inst, mo-per-inst, line-base, line-range, opcode-base
   starting at CUR. Returns (values min-inst line-base line-range
   opcode-base new-cur). DEFAULT-STMT is consumed but not returned."
  (let* ((min-inst   (u8 buf cur))
         (mo-per     (if (>= version 4) (u8 buf (+ cur 1)) 1))
         (cur1       (if (>= version 4) (+ cur 2) (+ cur 1))))
    (declare (ignore mo-per))
    (let ((line-base (let ((b (u8 buf (+ cur1 1))))
                       (if (>= b #x80) (- b 256) b)))
          (line-range (u8 buf (+ cur1 2)))
          (opcode-base (u8 buf (+ cur1 3))))
      ;; default-stmt at cur1, then line-base/range/opcode-base, then
      ;; standard-opcode-lengths array of length (opcode-base - 1).
      (values min-inst line-base line-range opcode-base
              (+ cur1 4 (- opcode-base 1))))))

(defun parse-cu-v5 (buf off unit-end c line-str debug-str)
  (let* ((addr-size (u8 buf (+ off 4 2)))
         (header-base (+ off 4 2 1 1 4))
         (header-length (u32 buf (+ off 4 2 1 1)))
         (prog-start (+ header-base header-length)))
    (multiple-value-bind (min-inst line-base line-range opcode-base cur)
        (read-common-header buf header-base 5)
      (multiple-value-bind (dirs cur1) (read-v5-dirs buf cur line-str debug-str)
        (multiple-value-bind (paths cur2)
            (read-v5-files buf cur1 dirs line-str debug-str)
          (declare (ignore cur2))
          (let ((file-base (collector-intern-files c paths))
                (file-count (length paths)))
            (run-line-program buf prog-start unit-end c
                              :min-inst min-inst
                              :line-base line-base
                              :line-range line-range
                              :opcode-base opcode-base
                              :addr-size addr-size
                              :file-base file-base
                              :file-count file-count
                              :start-file 0))))))
  unit-end)

(defun read-v5-dirs (buf cur line-str debug-str)
  (multiple-value-bind (fmt used) (read-entry-format buf cur)
    (incf cur used)
    (multiple-value-bind (count used2) (uleb128 buf cur)
      (incf cur used2)
      (let ((dirs (make-array count :initial-element "")))
        (dotimes (i count)
          (multiple-value-bind (path dir n) (read-entry buf cur fmt line-str debug-str)
            (declare (ignore dir))
            (setf (aref dirs i) (or path ""))
            (incf cur n)))
        (values dirs cur)))))

(defun read-v5-files (buf cur dirs line-str debug-str)
  (multiple-value-bind (fmt used) (read-entry-format buf cur)
    (incf cur used)
    (multiple-value-bind (count used2) (uleb128 buf cur)
      (incf cur used2)
      (let ((out '()))
        (dotimes (i count)
          (multiple-value-bind (path dir n) (read-entry buf cur fmt line-str debug-str)
            (incf cur n)
            (let ((d (and (< dir (length dirs)) (aref dirs dir))))
              (push (resolve-path d path) out))))
        (values (nreverse out) cur)))))

(defun parse-cu-v4 (buf off unit-end c line-str debug-str)
  (declare (ignore line-str debug-str))
  (let* ((header-base (+ off 4 2 4))
         (header-length (u32 buf (+ off 4 2)))
         (prog-start (+ header-base header-length)))
    (multiple-value-bind (min-inst line-base line-range opcode-base cur)
        (read-common-header buf header-base 4)
      (multiple-value-bind (dirs cur1) (read-v4-dirs buf cur)
        (multiple-value-bind (paths cur2) (read-v4-files buf cur1 dirs)
          (declare (ignore cur2))
          (let ((file-base (collector-intern-files c paths))
                (file-count (length paths)))
            (run-line-program buf prog-start unit-end c
                              :min-inst min-inst
                              :line-base line-base
                              :line-range line-range
                              :opcode-base opcode-base
                              :addr-size 8
                              :file-base file-base
                              :file-count file-count
                              :start-file 1))))))
  unit-end)

(defun read-v4-dirs (buf cur)
  (let ((dirs (make-array 8 :adjustable t :fill-pointer 0)))
    (loop until (zerop (aref buf cur)) do
      (multiple-value-bind (s n) (cstring-at* buf cur)
        (vector-push-extend s dirs)
        (incf cur n)))
    (incf cur) ; the NUL terminator
    (values dirs cur)))

(defun read-v4-files (buf cur dirs)
  (let ((out '()))
    (loop until (zerop (aref buf cur)) do
      (multiple-value-bind (name n) (cstring-at* buf cur)
        (incf cur n)
        (multiple-value-bind (dir-idx n2) (uleb128 buf cur)
          (incf cur n2)
          (multiple-value-bind (mtime n3) (uleb128 buf cur)
            (declare (ignore mtime))
            (incf cur n3))
          (multiple-value-bind (sz n4) (uleb128 buf cur)
            (declare (ignore sz))
            (incf cur n4))
          (let ((d (cond
                     ((zerop dir-idx) nil)
                     ((<= dir-idx (length dirs)) (aref dirs (1- dir-idx))))))
            (push (resolve-path d name) out)))))
    (incf cur)
    (values (nreverse out) cur)))

(defun resolve-path (dir name)
  (cond
    ((null name) nil)
    ((or (null dir) (zerop (length dir))) name)
    ;; Absolute name overrides dir
    ((char= (char name 0) #\/) name)
    ;; Ensure single slash join
    ((char= (char dir (1- (length dir))) #\/)
     (concatenate 'string dir name))
    (t (concatenate 'string dir "/" name))))

(defun run-line-program (buf start end c
                         &key min-inst mo-per-inst line-base line-range
                              opcode-base addr-size file-base file-count
                              start-file)
  "Run the line-number-program state machine over BUF[START..END).
   Push (address, file-base + (file-1-or-0), line) tuples into C."
  (declare (ignore mo-per-inst))
  (let ((pc start)
        (addr 0)
        (file start-file)
        (line 1))
    (flet ((emit ()
             (let* ((slot (cond
                            ((= start-file 1) (1- file)) ; DWARF 4: 1-based
                            (t                file)))    ; DWARF 5: 0-based
                    (idx (if (and (>= slot 0) (< slot file-count))
                             (+ file-base slot)
                             0)))
               (collector-push-row c addr idx (max 0 line)))))
      (loop while (< pc end) do
        (let ((op (aref buf pc)))
          (incf pc)
          (cond
            ;; Extended opcode
            ((zerop op)
             (multiple-value-bind (sz used) (uleb128 buf pc)
               (incf pc used)
               (let ((eop (aref buf pc))
                     (eop-end (+ pc sz)))
                 (incf pc)
                 (cond
                   ((= eop +dw-lne-end-sequence+)
                    ;; Reset state — do not emit a row for end-of-seq.
                    (setf addr 0 file start-file line 1)
                    (setf pc eop-end))
                   ((= eop +dw-lne-set-address+)
                    (setf addr (if (= addr-size 8)
                                   (u64 buf pc)
                                   (u32 buf pc)))
                    (setf pc eop-end))
                   ((= eop +dw-lne-set-discriminator+)
                    (setf pc eop-end))
                   (t (setf pc eop-end))))))
            ;; Standard opcodes (1 .. opcode-base-1)
            ((< op opcode-base)
             (cond
               ((= op +dw-lns-copy+)         (emit))
               ((= op +dw-lns-advance-pc+)
                (multiple-value-bind (v u) (uleb128 buf pc)
                  (incf pc u)
                  (incf addr (* v min-inst))))
               ((= op +dw-lns-advance-line+)
                (multiple-value-bind (v u) (sleb128 buf pc)
                  (incf pc u)
                  (incf line v)))
               ((= op +dw-lns-set-file+)
                (multiple-value-bind (v u) (uleb128 buf pc)
                  (incf pc u)
                  (setf file v)))
               ((= op +dw-lns-set-column+)
                (multiple-value-bind (v u) (uleb128 buf pc)
                  (declare (ignore v)) (incf pc u)))
               ((= op +dw-lns-negate-stmt+))
               ((= op +dw-lns-set-basic-block+))
               ((= op +dw-lns-const-add-pc+)
                (let* ((adj (- 255 opcode-base))
                       (op-adv (floor adj line-range)))
                  (incf addr (* min-inst op-adv))))
               ((= op +dw-lns-fixed-advance-pc+)
                (incf addr (u16 buf pc))
                (incf pc 2))
               ((= op +dw-lns-set-prologue-end+))
               ((= op +dw-lns-set-epilogue-begin+))
               ((= op +dw-lns-set-isa+)
                (multiple-value-bind (v u) (uleb128 buf pc)
                  (declare (ignore v)) (incf pc u)))
               (t
                ;; Skip unknown standard opcodes by their operand count.
                ;; We don't have the operand-length array threaded
                ;; through; bail out conservatively.
                (return))))
            ;; Special opcode (>= opcode-base)
            (t
             (let* ((adj (- op opcode-base))
                    (op-adv (floor adj line-range))
                    (line-delta (+ line-base (mod adj line-range))))
               (incf line line-delta)
               (incf addr (* min-inst op-adv))
               (emit)))))))))

;;; ========== Public entry ==========

(defstruct dwarf-line-info
  vaddrs    ; (simple-array (unsigned-byte 64) *)
  file-idx  ; (simple-array (unsigned-byte 32) *)
  lines     ; (simple-array (unsigned-byte 32) *)
  files)    ; simple-vector of file path strings

(defun parse-debug-line (line-buf line-str-buf debug-str-buf)
  "Walk every CU in LINE-BUF, returning a DWARF-LINE-INFO with rows
   sorted by vaddr. LINE-STR-BUF and DEBUG-STR-BUF may be NIL."
  (when line-buf
    (let ((c (make-collector))
          (off 0))
      (loop while (< (+ off 11) (length line-buf)) do
        (let ((next (parse-cu line-buf off c line-str-buf debug-str-buf)))
          (cond
            ((or (null next) (<= next off)) (return))
            (t (setf off next)))))
      (finalize-collector c))))

(defun finalize-collector (c)
  (let* ((n (length (collector-vaddrs c)))
         (idx (make-array n :element-type '(unsigned-byte 32))))
    (dotimes (i n) (setf (aref idx i) i))
    (sort idx #'< :key (lambda (k) (aref (collector-vaddrs c) k)))
    (let ((va (make-array n :element-type '(unsigned-byte 64)))
          (fi (make-array n :element-type '(unsigned-byte 32)))
          (ln (make-array n :element-type '(unsigned-byte 32))))
      (dotimes (i n)
        (let ((k (aref idx i)))
          (setf (aref va i) (aref (collector-vaddrs c) k))
          (setf (aref fi i) (aref (collector-file-idx c) k))
          (setf (aref ln i) (aref (collector-lines c) k))))
      (make-dwarf-line-info
       :vaddrs va :file-idx fi :lines ln
       :files (coerce (collector-files-out c) 'simple-vector)))))

(defun dwarf-line-find (info vaddr)
  "Binary search for the row whose vaddr is the greatest ≤ VADDR.
   Returns (values FILE LINE) or NIL if no row qualifies."
  (when info
    (let* ((arr (dwarf-line-info-vaddrs info))
           (n (length arr))
           (lo 0) (hi n))
      (loop while (< lo hi) do
        (let ((mid (ash (+ lo hi) -1)))
          (if (<= (aref arr mid) vaddr)
              (setf lo (1+ mid))
              (setf hi mid))))
      (when (plusp lo)
        (let* ((i (1- lo))
               (fi (aref (dwarf-line-info-file-idx info) i))
               (line (aref (dwarf-line-info-lines info) i))
               (files (dwarf-line-info-files info)))
          (when (and (< fi (length files)) (plusp line))
            (values (aref files fi) line)))))))
