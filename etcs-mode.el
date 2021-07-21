;;; -*- emacs-lisp -*-
;;; to use this mode, you will need to do something along the lines of
;;; the following and have it in your .emacs file:
;;;    (setq hol-executable "<fullpath to HOL executable>")
;;;    (load "<fullpath to this file>")

;;; The fullpath to this file can be just the name of the file, if
;;; your elisp variable load-path includes the directory where it
;;; lives.

(require 'thingatpt)
(require 'cl-lib)
(require 'subr-x)

(defgroup etcs nil
  "Customising the Emacs interface to the ETCS4 proof assistant."
  :group 'external)

(define-prefix-command 'etcs-map)
(define-prefix-command 'etcs-d-map)
(define-prefix-command 'etcs-movement-map)
(make-variable-buffer-local 'etcs-buffer-name)
(set-default 'etcs-buffer-name "*ETCS*")

(set-default 'etcs-default-buffer nil)

(defcustom etcs-executable 
  "/Users/yimingxu/Documents/GitHub/ETCS/bin/etcs"
  "Path-name for the ETCS executable."
  :group 'etcs
  :type '(file :must-match t))

(defcustom etcsmake-executable 
  "/Users/yimingxu/Documents/GitHub/ETCS/bin/Etcsmake"
  "Path-name for the Etcsmake executable."
  :group 'etcs
  :type '(file :must-match t))

(defcustom etcs-show-tooltips-in-minibuffer t
  "Whether to additionally show tooltips in minibuffer."
  :group 'etcs
  :type '(choice
          (const :tag "Yes; messages appear in minibuffer" t)
          (const :tag "No; messages only in tooltips" nil)))

(defconst etcs-dir
  (file-name-directory
   (directory-file-name (file-name-directory etcs-executable))))
(setq load-path (cons (concat etcs-dir "tools/") load-path))
(require 'etcsscript-mode)

(defcustom etcs-new-buffer-style-default 'new-frame
  "Default style for creating new ETCS buffers. Possible values are
new-frame (create in a new-frame); horizontal (create in a new buffer
that is horizontally adjacent and to the right); and vertical (create in
a new buffer that is vertically adjacent and below)."
  :group 'etcs
  :type '(choice (const new-frame :tag "new-frame")
                 (const horizontal :tag "horizontal")
                 (const vertical :tag "vertical")))

(defun etcs-set-executable (filename)
  "*Set etcs executable variable to be NAME."
  (interactive "fETCS executable: ")
  (setq etcs-executable filename)
  (setq etcs-bare-p nil))

(defun etcsmake-set-executable (filename)
  "*Set etcsmake executable variable to be NAME."
  (interactive "fETCS executable: ")
  (setq etcsmake-executable filename))

(defvar etcs-mode-sml-init-command
   "use (Globals.ETCSDIR ^ \"/tools/etcs-mode.sml\")"
  "*The command to send to ETCS to load the ML-part of etcs-mode.")


(defcustom etcs-echo-commands-p nil
  "Whether or not to echo the text of commands originating elsewhere."
  :group 'etcs
  :type 'boolean)

(defcustom etcs-raise-on-recentre nil
  "Controls if etcs-recentre (\\[etcs-recentre]) also raises the ETCS frame."
  :group 'etcs
  :type 'boolean)

(defcustom etcs-unicode-print-font-filename
  "/usr/share/fonts/truetype/ttf-dejavu/DejaVuSans.ttf"
  "File name of font to use when printing ETCS output to a PDF file."
  :group 'etcs
  :type '(file :must-match t))



(defvar etcs-generate-locpragma-p t
  "*Whether or not to generate (*#loc row col *) pragmas for ETCS.")

(defvar etcs-emit-time-elapsed-p nil
  "*Whether or not to print time elapsed messages after causing ETCS
evaluations.")

(defvar etcs-auto-load-p t
  "*Do automatic loading?")

(defvar etcs-bare-p nil
  "*use etcs.bare?")

;;; For compatability between both Emacs and XEmacs, please use the following
;;; two functions to determine if the mark is active, or to set it active.

(defun etcs-is-region-active ()
  (and transient-mark-mode (boundp 'mark-active) mark-active))

(defvar-local etcs-term-end-delim nil)
(put 'etcs-term 'end-op
     (function
      (lambda ()
        (let ((pthm-point
               (save-excursion
                 (let ((ok t))
                   (while
                       (and ok
                            (re-search-forward
                             "^Proof\\|^Theorem\\|^Triviality" nil t))
                     (let ((ppss (syntax-ppss)))
                       (if (or (nth 3 ppss) (nth 4 ppss)) nil
                         (setq ok nil))))
                   (not ok)))))
          (if (and pthm-point (equal (match-string 0) "Proof"))
              (progn (goto-char (match-beginning 0))
                     (setq etcs-term-end-delim "Proof"))
            (re-search-forward "[`’”]\\|^End\\|^Termination" nil t)
            (setq etcs-term-end-delim (match-string 0))
            (goto-char (match-beginning 0)))))))
(defvar etcs-beg-pos nil) ; ugh, global, but easiest this way
(defvar etcs-name-attrs-colon-re
  "[[:space:]]+[A-Za-z0-9'_]+\\(\\[[A-Za-z0-9_,]+\\]\\)?[[:space:]]*:")
(defvar etcs-quoted-theorem-proof-re-begin
  (concat "\\(Theorem\\|Triviality\\)" etcs-name-attrs-colon-re))
(defvar etcs-quoted-definition-re-begin
  (concat "\\(Definition\\|\\(Co\\)?Inductive\\)" etcs-name-attrs-colon-re))
(put 'etcs-term 'beginning-op
     (function
      (lambda ()
        (let ((beg
               (cond
                ((equal etcs-term-end-delim "`") "`")
                ((equal etcs-term-end-delim "’") "‘")
                ((equal etcs-term-end-delim "”") "“")
                ((equal etcs-term-end-delim "Proof")
                 etcs-quoted-theorem-proof-re-begin)
                ((or (equal etcs-term-end-delim "End")
                     (equal etcs-term-end-delim "Termination"))
                 etcs-quoted-definition-re-begin))))
          (re-search-backward beg nil t)
          (goto-char (match-end 0))
          (setq etcs-beg-pos (point))))))

(defun etcs-term-at-point ()
  (let ((s (thing-at-point 'etcs-term t)))
    (with-etcs-locpragma etcs-beg-pos s)))

(defun etcs-buffer-ok (string)
  "Checks a string to see if it is the name of a good ETCS buffer.
In reality this comes down to checking that a buffer-name has a live
process in it."
  (and string (get-buffer-process string)
       (eq 'run
           (process-status
            (get-buffer-process string)))))

(defun ensure-etcs-buffer-ok ()
  "Ensures by prompting that a ETCS buffer name is OK, and returns it."
  (if (etcs-buffer-ok etcs-buffer-name) etcs-buffer-name
    (message
     (cond (etcs-buffer-name (concat etcs-buffer-name " not valid anymore."))
           (t "Please choose a ETCS to attach this buffer to.")))
    (sleep-for 1)
    (setq etcs-buffer-name (read-buffer "ETCS buffer: " etcs-default-buffer t))
    (while (not (etcs-buffer-ok etcs-buffer-name))
      (ding)
      (message "Not a valid ETCS process")
      (sleep-for 1)
      (setq etcs-buffer-name
            (read-buffer "ETCS buffer: " etcs-default-buffer t)))
    (setq etcs-default-buffer etcs-buffer-name)
    etcs-buffer-name))



(defun with-etcs-locpragma (pos s)
  (if etcs-generate-locpragma-p
      (concat (etcs-locpragma-of-position pos) s)
      s))

(defun etcs-locpragma-of-position (pos)
  "Convert Elisp position into ETCS location pragma.  Not for interactive use."
  (let ((initial-point (point)))
    (goto-char pos)
    (let* ((rowstart (point-at-bol))  ;; (line-beginning-position)
           (row      (+ (count-lines 1 pos)
                      (if (= rowstart pos) 1 0)))
           (col      (+ (current-column) 1)))
      (goto-char initial-point)
      (format " (*#loc %d %d *)\n" (- row 1) col))))

(defun send-raw-string-to-etcs (string echoit)
  "Sends a string in the raw to ETCS.  Not for interactive use."
  (let ((buf (ensure-etcs-buffer-ok)))
    (if echoit
        (with-current-buffer buf
          (goto-char (point-max))
          (princ (concat string ";") (get-buffer buf))
          (goto-char (point-max))
          (comint-send-input)
          (etcs-recentre 1))
      (comint-send-string buf (concat string ";\n")))))

(defun send-timed-string-to-etcs (string echo-p &optional loud-opens)
  "Send STRING to ETCS (with send-string-to-etcs), and emit information about
how long this took."
  (interactive)
  (send-raw-string-to-etcs
   "val etcs_mode_time0 = #usr (Timer.checkCPUTimer Globals.etcs_clock);" nil)
  (send-string-to-etcs string echo-p)
  (send-raw-string-to-etcs
       "val _ = let val t = #usr (Timer.checkCPUTimer Globals.etcs_clock)
                      val elapsed = Time.-(t, etcs_mode_time0)
                in
                      print (\"\\n*** Time taken: \"^
                             Time.toString elapsed^\"s\\n\")
                  end" nil))

(defvar tactic-connective-regexp
  "[[:space:]]*\\(THEN1\\|THENL\\|THEN\\|>>\\|>|\\|>-\\|>~\\|\\\\\\\\\\)[[:space:]]*[[(]?"
  "Regular expression for strings used to put tactics together.")

(defun tactic-cleanup-leading (string)
  "Remove leading instances of tactic connectives from a string.
A tactic connective is any one of \"THEN\", \"THENL\", \"THEN1\", \">>\", \">|\"
or \">-\"."
  (let* ((case-fold-search nil)
         (pattern (concat "\\`" tactic-connective-regexp)))
    (replace-regexp-in-string pattern "" string)))

(defun tactic-cleanup-trailing (string)
  "Remove trailing instances of tactic connectives from a string.
A tactic connective is any one of \"THEN\", \"THENL\", \"THEN1\", \">>\", \">|\"
or \">-\"."
  (let* ((case-fold-search nil)
         (pattern (concat tactic-connective-regexp "\\'")))
    (replace-regexp-in-string pattern "" string)))

(defun etcs-find-eval-next-tactic (arg)
  "Highlights the next tactic in the source and evaluates in the ETCS buffer.
With a prefix ARG, uses `expandf' rather than `e'."
  (interactive "P")
  (deactivate-mark)
  (skip-syntax-forward " ")
  (let
      ((term (thing-at-point 'tactic-terminator))
       (sqb (char-equal (following-char) ?\[)))
    (while (or term sqb)
      (cond (term (forward-tactic-terminator 1))
            (sqb (forward-char)))
      (skip-syntax-forward " ")
      (setq term (thing-at-point 'tactic-terminator))
      (setq sqb (char-equal (following-char) ?\[))))
  (mark-etcs-tactic)
  (copy-region-as-etcs-tactic (region-beginning) (region-end) arg)
  (goto-char (region-end)))

(defun copy-region-as-etcs-tactic (start end arg)
  "Send selected region to ETCS process as tactic."
  (interactive "r\nP")
  (let*
      ((region-string0 (buffer-substring start end))
       (region-string1 (tactic-cleanup-leading region-string0))
       (region-string2 (tactic-cleanup-trailing region-string1))
       (start-offset (- (length region-string0) (length region-string1)))
       (region-string3 (with-etcs-locpragma (+ start start-offset) region-string2))
       (ste "\"show_typecheck_errors\"")
       (region-string (concat "let val old = Feedback.current_trace "
                              ste
                              " val _ = Feedback.set_trace "
                              ste
                              " 0 in ("
                              region-string3
                              ") before "
                              "Feedback.set_trace " ste " old end"))
       (e-string (concat "proofManagerLib." (if arg "expandf" "e")))
       (tactic-string (format "%s (%s)" e-string region-string))
       (sender (if etcs-emit-time-elapsed-p
                   'send-timed-string-to-etcs
                 'send-string-to-etcs)))
    (funcall sender tactic-string etcs-echo-commands-p)))

;;; For goaltrees
(defun copy-region-as-goaltree-tactic (start end)
  "Send selected region to ETCS process as goaltree tactic."
  (interactive "r\nP")
  (let* ((region-string (with-etcs-locpragma start
                          (buffer-substring-no-properties start end)))
         (tactic-string
           (format "proofManagerLib.expandv (%S,%s) handle e => Raise e"
                   region-string region-string))
         (sender (if etcs-emit-time-elapsed-p
                     'send-timed-string-to-etcs
                   'send-string-to-etcs)))
    (funcall sender tactic-string etcs-echo-commands-p)))

(defun send-string-as-etcs-goal (s)
  (let ((goal-string (format  "proofManagerLib.g \"%s\"" s)))
    (send-raw-string-to-etcs goal-string etcs-echo-commands-p)
    (send-raw-string-to-etcs "proofManagerLib.set_backup 100;" nil)))

(defun count-text-match (regex string)
  (let ((case-fold-search nil)
        (i 0)
        (c 0))
    (while (string-match regex string i)
      (progn (setq i (match-end 0))
             (setq c (+ c 1))))
    c))

(defun etcs-string-contains-term-delimiters-p (s)
  (< 0 (count-text-match
        (concat "^Theorem\\|^Definition\\|^Proof\\|^\\(Co\\)?Inductive\\|"
                "^Termination\\|^End\\|[“”‘’`]\\|^Triviality")
        s)))


(defun etcs-do-goal (arg)
  "Send term around point to ETCS process as goal.
If prefix ARG is true, or if in transient mark mode, region is active and
the region contains no term-delimiters, then send region instead."
  (interactive "P")
  (let ((txt (condition-case nil
                 (with-etcs-locpragma (region-beginning)
                    (buffer-substring (region-beginning) (region-end)))
               (error nil))))
    (if (or (and (etcs-is-region-active)
                 (not (etcs-string-contains-term-delimiters-p txt)))
            arg)
      (send-string-as-etcs-goal txt)
    (send-string-as-etcs-goal (etcs-term-at-point)))))


(defun send-string-as-etcs-goaltree (s)
  (let ((goal-string
         (format  "proofManagerLib.gt `%s` handle e => Raise e" s)))
    (send-raw-string-to-etcs goal-string etcs-echo-commands-p)
    (send-raw-string-to-etcs "proofManagerLib.set_backup 100;" nil)))


(defun etcs-do-goaltree (arg)
  "Send term around point to ETCS process as goaltree.
If prefix ARG is true, or if in transient mark mode, region is active and
the region contains no backquotes, then send region instead."
  (interactive "P")
  (let ((txt (condition-case nil
                 (with-etcs-locpragma (region-beginning)
                    (buffer-substring (region-beginning) (region-end)))
               (error nil))))
    (if (or (and (etcs-is-region-active) (= (cl-count ?\` txt) 0))
            arg)
      (send-string-as-etcs-goaltree txt)
    (send-string-as-etcs-goaltree (etcs-term-at-point)))))

(defun copy-region-as-etcs-definition (start end arg &optional loud-opens0)
  "Send selected region to ETCS process as definition/expression.  With a
prefix arg of 4 (hit control-u once), wrap what is sent so that it becomes
( .. ) handle e => Raise e, allowing ETCS_ERRs to be displayed cleanly.
With a prefix arg of 16 (hit control-u twice), toggle `quiet-declarations'
before and after the region is sent."
  (interactive "r\np")
  (let* ((buffer-string
            (with-etcs-locpragma start (buffer-substring start end)))
         (send-string
          (if (= arg 4)
              (concat "(" buffer-string ") handle e => Raise e")
            buffer-string))
         (loud-opens (if (= arg 16) t loud-opens0))
         (sender (if etcs-emit-time-elapsed-p
                     'send-timed-string-to-etcs
                   'send-string-to-etcs)))
    (if (= arg 16) (etcs-toggle-quietdec))
    (unwind-protect
        (progn
          (funcall sender send-string etcs-echo-commands-p loud-opens)
          (if (> (length send-string) 300)
              (send-string-to-etcs
               (concat "val _ = print \"\\n*** Emacs/ETCS command completed "
                       "***\\n\\n\""))))
      (if (= (prefix-numeric-value arg) 16) (etcs-toggle-quietdec)))))



(defun copy-region-as-etcs-definition-quietly (start end)
   (interactive "r")
   (etcs-toggle-quiet-quietdec)
   (copy-region-as-etcs-definition start end 0 t)
   (etcs-toggle-quiet-quietdec))


(defun etcs-name-top-theorem (string arg)
  "Name the top theorem of the proofManagerLib.
With prefix argument, drop the goal afterwards."
  (interactive "sName for top theorem: \nP")
  (if (not (string= string ""))
      (send-raw-string-to-etcs
       (format "val %s = top_thm()" string)
       etcs-echo-commands-p))
  (if arg
      (send-raw-string-to-etcs "proofManagerLib.drop()" etcs-echo-commands-p)))

(defun etcs-start-termination-proof (arg)
  "Send definition around point to ETCS process as Defn.tgoal.
If prefix ARG is true, or if in transient mark mode, region is active and
the region contains no term delimiters, then send region instead."
  (interactive "P")
  (let ((txt (condition-case nil
                 (with-etcs-locpragma (region-beginning)
                    (buffer-substring (region-beginning) (region-end)))
               (error nil))))
    (if (or (and (etcs-is-region-active)
                 (not (etcs-string-contains-term-delimiters-p txt)))
            arg)
      (etcs-send-string-as-termination-proof txt)
    (etcs-send-string-as-termination-proof (etcs-term-at-point)))))

(defun etcs-send-string-as-termination-proof (str)
  (send-raw-string-to-etcs
   (concat "Defn.tgoal (Defn.Etcs_defn \"ETCSmode_defn\" `"
           str "`) handle e => Raise e")
   nil))

(defun remove-sml-comments (end)
  (let (done (start (point)))
    (while (and (not done) (re-search-forward "(\\*\\|\\*)" end t))
        (if (string= (match-string 0) "*)")
            (progn
              (delete-region (- start 2) (point))
              (setq done t))
          ;; found a comment beginning
          (if (not (remove-sml-comments end)) (setq done t))))
      (if (not done) (message "Incomplete comment in region given"))
      done))

(defun remove-quoted-etcs-term (bq eq end-marker &optional extra)
  (let ((start (point))
        (bqsize (length bq))
        (i (if extra extra 0)))
    (if (re-search-forward eq end-marker t)
        (delete-region (- start (- bqsize i)) (point))
      (error
       (format "Incomplete (%s...%s-quoted) ETCS term in region given; \
starts >%s%s<"
               bq eq
               bq
               (buffer-substring (point) (+ (point) 10)))))))

(defun remove-etcs-string (end-marker)
  (let ((start (point)))
    (if (re-search-forward "\n\\|[^\\]?\"" end-marker t)
        (if (string= (match-string 0) "\n")
            (message "String literal terminated by newline - not allowed!")
          (delete-region (- start 1) (point))))))


(setq etcs-open-terminator-regexp
      (concat
       (mapconcat (lambda (s) (concat "^" s "\\>"))
                  '("Theorem" "Definition" "Inductive" "CoInductive"
                    "Triviality" "Datatype" "Type" "Overload")
                  "\\|")
       "\\|;\\|"
       (regexp-opt
        '("val" "fun" "in" "infix" "infixl" "infixr" "open" "local" "type"
          "datatype" "nonfix" "exception" "end" "structure") 'symbols)))

(setq sml-struct-id-regexp "[A-Za-z][A-Za-z0-9_]*")

(defun send-string-to-etcs (string &optional echoit leave-loud-opens)
  "Send a string to ETCS process."
  (let ((buf (ensure-etcs-buffer-ok))
        (old-mark-active (etcs-is-region-active)))
    (unwind-protect
        (with-temp-buffer
          (etcsscript-mode)
          (setq etcs-buffer-name buf) ; version of this variable in tmpbuf
          (setq case-fold-search nil) ; buffer-local version
          (insert string)
          (goto-char (point-min))
          ;; first thing to do is to search through buffer looking for
          ;; identifiers of form id.id.  When spotted such identifiers need
          ;; to have the first component of the name loaded.
          (let ((regexp
                 (concat "`\\|“\\|‘\\|"
                         etcs-quoted-theorem-proof-re-begin "\\|"
                         etcs-quoted-definition-re-begin "\\|"
                         "\\(" sml-struct-id-regexp "\\)\\.\\w+" "\\|"
                         "\\_<open\\_>")))
            (while (re-search-forward regexp (point-max) t)
              (let ((pp (syntax-ppss))
                    (ms (match-string-no-properties 0)))
                (if (and (not (nth 3 pp)) (not (nth 4 pp)))
                    ;; maybe looking at termish thing that needs dodging
                    (cond
                     ((string= ms "`")
                      (let ((term
                             (if (looking-at "`") ; double backtick
                                 (progn (forward-char 1) "``") "`")))
                        (if (not (re-search-forward term nil t))
                            (error
                             (concat "Unbalanced " term " in region")))))
                     ((string= ms "“")
                      (if (not (re-search-forward "”" nil t))
                          (error "Unbalanced “ in region")))
                     ((string= ms "‘")
                      (if (not (re-search-forward "’" nil t))
                          (error "Unbalanced “ in region")))
                     ((and (or (string-prefix-p "Theorem" ms)
                               (string-prefix-p "Triviality" ms))
                           (char-equal (char-before) ?:))
                      (if (not (re-search-forward "^Proof" nil t))
                          (error "Unbalanced `Theorem/Triviality' in region")))
                     ((and (string-prefix-p "Definition" ms)
                           (char-equal (char-before) ?:))
                      (if (not
                           (re-search-forward "^Termination\\|^End" nil t))
                          (error "Unbalanced `Definition' in region")))
                     ((and (or (string-prefix-p "Inductive" ms)
                               (string-prefix-p "CoInductive" ms))
                           (char-equal (char-before) ?:))
                      (if (not (re-search-forward "^End" nil t))
                          (error "Unbalanced [Co]Inductive in region")))
                     ((string= ms "open")
                      ;; point now after an open, now search forward
                      ;; to end of buffer or a semi-colon, or an infix
                      ;; declaration or a val or a fun or another open
                      ;; or whatever, (as per the regexp defined just
                      ;; before this function definition)
                      (let ((open-start (match-beginning 0))
                            (start (point))
                            (end
                             (save-excursion
                               (let ((case-fold-search nil)
                                     (foundp nil)
                                     (abortedp nil))
                                 ;; complicated loop required to avoid being
                                 ;; confused by input such as
                                 ;; open listSyntax (* ; *) integerTheory;
                                 (while (and (not foundp) (not abortedp))
                                   (if (re-search-forward
                                        etcs-open-terminator-regexp
                                        nil t)
                                       (setq foundp
                                             (let ((pp (syntax-ppss)))
                                               (and (not (nth 3 pp))
                                                    (not (nth 4 pp)))))
                                     (setq abortedp t)))
                                 (if foundp
                                     (- (point) (length (match-string 0)))
                                   (point-max)))))
                            (endm (make-marker)))
                        ; (message "Handling an open")
                        (if etcs-auto-load-p
                            (etcs-load-modules-in-region start end))
                        (if leave-loud-opens nil
                            ;; now bracket the open decl with quietdec toggles
                          (set-marker endm end)
                          (goto-char end)
                          (insert
                           ";val _ = ETCS_Interactive.toggle_quietdec();\n")
                          (goto-char open-start)
                          (insert
                           "val _ = ETCS_Interactive.toggle_quietdec();\n")
                          (goto-char endm) (set-marker endm nil))))
                     (t
                      ; (message "Saw \"%s\"; position = %d; loading: %s"
                      ;           ms (point) (match-string 6))
                      (if etcs-auto-load-p
                          (etcs-load-string (match-string 6))))))))
          ;; send the string
          (goto-char (point-min))
            (send-buffer-to-etcs-maybe-via-file echoit)))
      )
    ;; deactivate-mark will have likely been set by all the editting actions
    ;; in the temporary buffer.  We fix this here, thereby keeping the mark
    ;; active, if it is active.
    ;; if in XEmacs, use (zmacs-activate-region) instead.
    (if (boundp 'deactivate-mark)
        (if deactivate-mark (setq deactivate-mark nil))
        (if (and old-mark-active (fboundp 'zmacs-activate-region))
            (zmacs-activate-region)))))

(defun interactive-send-string-to-etcs (string &optional echoit)
   "Send a string to ETCS process."
   (interactive "sString to send to ETCS process: \nP")
   (if etcs-emit-time-elapsed-p
       (send-timed-string-to-etcs string echoit)
     (send-string-to-etcs string echoit)))

(if (null temporary-file-directory)
    (if (equal system-type 'windows-nt)
        (if (not (null (getenv "TEMP")))
            (setq temporary-file-directory (getenv "TEMP")))
      (setq temporary-file-directory "/tmp")))

(defun make-temp-file-xemacs (prefix &optional dir-flag)
  "Create a temporary file.
The returned file name (created by appending some random characters at the end
of PREFIX, and expanding against `temporary-file-directory' if necessary,
is guaranteed to point to a newly created empty file.
You can then use `write-region' to write new data into the file.

If DIR-FLAG is non-nil, create a new empty directory instead of a file."
  (let (file)
    (while (condition-case ()
	       (progn
		 (setq file
		       (make-temp-name
			(expand-file-name prefix temporary-file-directory)))
		 (if dir-flag
		     (make-directory file)
		   (write-region "" nil file nil 'silent nil)) ;; 'excl
		 nil)
	    (file-already-exists t))
      ;; the file was somehow created by someone else between
      ;; `make-temp-name' and `write-region', let's try again.
      nil)
    file))

(defvar etcs-mode-to-delete nil
  "String optionally containing name of last temporary file used to transmit
ETCS sources to a running session (using \"use\")")

(defun send-buffer-to-etcs-maybe-via-file (&optional echoit)
  "Send the contents of current buffer to ETCS, possibly putting it into a
file to \"use\" first."
  (if (< 500 (buffer-size))
          (let ((fname (if (fboundp 'make-temp-file)
                              ;; then
                                    (make-temp-file "etcs" nil "Script.sml")
                              ;; else
                                    (make-temp-file-xemacs "etcs")
                                 )))
            (if (stringp etcs-mode-to-delete)
                (progn (condition-case nil
                           (delete-file etcs-mode-to-delete)
                         (error nil))
                       (setq etcs-mode-to-delete nil)))
            ; below, use visit parameter = 1 to stop message in mini-buffer
            (write-region (point-min) (point-max) fname nil 1)
            (send-raw-string-to-etcs (format "use \"%s\"" fname) nil)
            (setq etcs-mode-to-delete fname))
    (send-raw-string-to-etcs (buffer-string) echoit)))


(defun etcs-backup ()
  "Perform a ETCS backup."
  (interactive)
  (send-raw-string-to-etcs "proofManagerLib.b()" etcs-echo-commands-p))

(defun etcs-user-backup ()
  "Perform a ETCS backup to a user-defined save-point."
  (interactive)
  (send-raw-string-to-etcs "proofManagerLib.restore()" etcs-echo-commands-p))

(defun etcs-print-info ()
  "Show some information about the currently running ETCS and the settings of etcs-mode."
  (interactive)
  (send-raw-string-to-etcs
   (concat "print_current_etcs_status" "\""
           etcs-executable "\" \"" etcsmake-executable "\" ();")
   etcs-echo-commands-p))

(defun etcs-user-save-backup ()
  "Saves the current status of the proof for later backups to this point."
  (interactive)
  (send-raw-string-to-etcs "proofManagerLib.save()" etcs-echo-commands-p))

(defun etcs-print-goal ()
  "Print the current ETCS goal."
  (interactive)
  (send-raw-string-to-etcs "proofManagerLib.p()" etcs-echo-commands-p))

(defun etcs-print-all-goals ()
  "Print all the current ETCS goals."
  (interactive)
  (send-raw-string-to-etcs "proofManagerLib.status()" etcs-echo-commands-p))

(defun etcs-interrupt ()
  "Perform a ETCS interrupt."
  (interactive)
  (let ((buf (ensure-etcs-buffer-ok)))
    (interrupt-process (get-buffer-process buf))))


(defun etcs-kill ()
  "Kill ETCS process."
  (interactive)
  (let ((buf (ensure-etcs-buffer-ok)))
    (kill-process (get-buffer-process buf))))

(defun etcs-recentre (arg)
  "Display the ETCS window in such a way that it displays most text, with the
cursor at the bottom.
With prefix arg, instead orient the ETCS window so as to put the cursor in
the middle of the window, and keep the cursor in its current position.

If the variable `etcs-raise-on-recentre' is non-nil, also raise the frame
containing the ETCS window, but keep the current frame uppermost."
  (interactive "p")
  (let ((f (selected-frame)))
    (if (get-buffer-window etcs-buffer-name t)
        (save-mark-and-excursion
          (select-window (get-buffer-window etcs-buffer-name t))
          (and etcs-raise-on-recentre (progn (raise-frame) (raise-frame f)))
          (if (= arg 1) (goto-char (point-max)))
          (recenter (if (= arg 1) -1 nil))))))

(defun etcs-rotate (arg)
  "Rotate the goal stack N times.  Once by default."
  (interactive "p")
  (send-raw-string-to-etcs (format "proofManagerLib.r %d" arg)
                          etcs-echo-commands-p))

(defun etcs-scroll-up (arg)
  "Scrolls the ETCS window."
  (interactive "P")
  (ensure-etcs-buffer-ok)
  (save-excursion
    (select-window (get-buffer-window etcs-buffer-name t))
    (scroll-up arg)))

(defun etcs-scroll-down (arg)
  "Scrolls the ETCS window."
  (interactive "P")
  (ensure-etcs-buffer-ok)
  (save-excursion
    (select-window (get-buffer-window etcs-buffer-name t))
    (scroll-down arg)))

(defun etcs-use-file (filename)
  "Gets ETCS session to \"use\" a file."
  (interactive "fFile to use: ")
  (send-raw-string-to-etcs (concat "use \"" filename "\";")
                          etcs-echo-commands-p))

(defun etcs-load-string (s)
  "Loads the ML object file NAME.uo; checking that it isn't already loaded."
  (let* ((buf (ensure-etcs-buffer-ok))
         (mys (format "%s" s)) ;; gets rid of text properties
         (commandstring
          (concat "val _ = if List.exists (fn s => s = \""
                  mys
                  "\") (emacs_etcs_mode_loaded()) then () else "
                  "(print  \"Loading " mys
                  "\\n\"; " "Meta.load \"" mys "\");\n")))
    (comint-send-string buf commandstring)))

(defun etcs-load-modules-in-region (start end)
  "Attempts to load all of the words in the region as modules."
  (interactive "rP")
  (save-excursion
    (goto-char start)
    (while (re-search-forward (concat "\\b" sml-struct-id-regexp "\\b") end t)
      (let ((ppss (syntax-ppss)))
        (if (and (not (nth 4 ppss)) (not (nth 3 ppss)))
            (etcs-load-string (match-string 0)))))))

(defun etcs-load-file (arg)
  "Gets ETCS session to \"load\" the file at point.
If there is no filename at point, then prompt for file.  If the region
is active (in transient mark mode) and it looks like it might be a
module name or a white-space delimited list of module names, then send
region instead. With prefix ARG prompt for a file-name to load."
  (interactive "P")
  (let* ((wap (word-at-point))
         (txt (condition-case nil
                  (buffer-substring (region-beginning) (region-end))
                (error nil))))
    (cond (arg (etcs-load-string (read-string "Library to load: ")))
          ((and (etcs-is-region-active)
                (string-match (concat "^\\(\\s-*" sml-struct-id-regexp
                                      "\\)+\\s-*$") txt))
           (etcs-load-modules-in-region (region-beginning) (region-end)))
          ((and wap (string-match "^\\w+$" wap)) (etcs-load-string wap))
          (t (etcs-load-string (read-string "Library to load: "))))))


(defun etcs-mode-init-sml ()
   (etcs-toggle-quiet-quietdec)
   (send-raw-string-to-etcs etcs-mode-sml-init-command nil)
   (etcs-toggle-quiet-quietdec))

(defun turn-off-etcs-font-lock (oldvar)
  (interactive)
  (if (not oldvar)
      (progn
        (message "Turning on font-lock mode does nothing in ETCS mode")
        (setq font-lock-defaults nil)))
  (setq font-lock-mode nil))

(defun etcsmake (&optional dir)
   (interactive "DRun Etcsmake in dir: ")
   (if (not (null dir))
      (with-current-buffer (get-buffer-create "*Etcsmake*")
         (delete-region (point-min) (point-max))
         (cd (expand-file-name dir)))
      )
   (let* ((buf (make-comint "Etcsmake"
                  etcsmake-executable nil "--qof" "-k")))
      (with-current-buffer buf
         (font-lock-mode 0)
         (make-local-variable 'font-lock-function)
         (setq font-lock-function 'turn-off-etcs-font-lock)
         (setq comint-preoutput-filter-functions '(etcsmakepp-output-filter)))
         (setq comint-scroll-show-maximum-output t)
         (setq comint-scroll-to-bottom-on-output t)
      (display-buffer buf)
   ))

;** etcs map keys and function definitions
(defun etcs-executable-with-bare ()
  (if etcs-bare-p (concat etcs-executable ".bare")
                 etcs-executable))

(defun etcs--looks-like-root-etcsdir (dir)
  (cl-every
   (lambda (s) (file-exists-p (concat (file-name-as-directory dir) s)))
   '("COPYRIGHT" "tools" "tools-poly" "std.prelude" "bin")))

(defun etcs--find-alternate-executable (dir0 original-name0)
  (let ((dir (expand-file-name dir0))
        (original-name (expand-file-name original-name0)))
    ;; check for lastmaker file
    (if-let*
        (((file-readable-p ".ETCSMK/lastmaker"))
         ((> 500 (file-attribute-size (file-attributes ".ETCSMK/lastmaker"))))
         (lines (with-temp-buffer
                  (insert-file-contents-literally ".ETCSMK/lastmaker")
                  (split-string (buffer-string) "\n" t)))
         ((not (null lines)))
         (dir1 (file-name-directory (car lines)))
         (name (concat dir1 "etcs"))
         ((not (equal name original-name))))
        (list (concat dir1 "etcs") "(honouring last build in this directory)")
      (while (and (not (etcs--looks-like-root-etcsdir dir))
                  (not (equal "/" dir)))
        (setq dir (file-name-directory (directory-file-name dir))))
      (if (equal "/" dir) nil
        (let ((bindir
               (file-name-as-directory
                (concat (file-name-as-directory dir) "bin"))))
          (cond
           ((equal (file-name-directory original-name) bindir) nil)
           ((file-exists-p (concat bindir "etcs.state"))
            (list (concat bindir "etcs") "(as we are in its ETCS directory)"))
           ((file-exists-p (concat bindir "etcs.state0"))
            (list
             (concat bindir "etcs.bare")
             "(as we are in its ETCS directory and etcs.state doesn't exist)"))))))))

(defun etcs--get-executable ()
  (let ((first-option (etcs-executable-with-bare)))
    (or (let ((alternate
               (etcs--find-alternate-executable default-directory first-option)))
          (if alternate
              (progn (message "Using %s as ETCS executable %s"
                              (car alternate) (cadr alternate))
                     (sleep-for 1 500)
                     (car alternate))))
        first-option)))

(defun etcs (&optional display-actions display-alist)
  "Runs a ETCS session in a comint window."
  (interactive)
  (let* ((original-buffer (current-buffer))
         (my-dir (or (ignore-errors (file-name-directory buffer-file-name))
                     default-directory))
         (etcs-executable (etcs--get-executable)))
    (if (not (file-executable-p etcs-executable))
        (error "Wanted to execute %s as ETCS, but can not find/execute it"
               etcs-executable))
    (if (get-buffer etcs-buffer-name)
        (progn
          (set-buffer etcs-buffer-name)
          (if (etcs-buffer-ok etcs-buffer-name)
              (progn
                (message "Killing existing ETCS process")
                (comint-send-eof)
                (sleep-for 0 500)))
          (setq default-directory my-dir)
          (make-comint-in-buffer "ETCS" etcs-buffer-name etcs-executable))
      (let* ((buf (make-comint "ETCS" etcs-executable)))
        (setq etcs-buffer-name (buffer-name buf))
        (set-buffer etcs-buffer-name)))

    (setq comint-prompt-regexp "^- ")
    ;; must go to ridiculous lengths to ensure that font-lock-mode is
    ;; turned off and stays off
    (font-lock-mode 0)
    (make-local-variable 'font-lock-function)
    (setq font-lock-function 'turn-off-etcs-font-lock)
    (make-local-variable 'comint-preoutput-filter-functions)
    (etcspp-quiet-reset)
    (setq comint-preoutput-filter-functions '(etcspp-output-filter))
    (setq comint-scroll-show-maximum-output t)
    (setq comint-scroll-to-bottom-on-output t)
    (etcs-mode-init-sml)
    (send-raw-string-to-etcs
     "val _ = Parse.current_backend := PPBackEnd.emacs_terminal;" nil)
    (if etcs-show-tooltips-in-minibuffer
       (progn (setq help-at-pt-display-when-idle t)
              (help-at-pt-set-timer)))

    (if (eq (get-buffer etcs-buffer-name) original-buffer)
        nil
      (display-buffer etcs-buffer-name
                      (cons
                       (append display-actions
                               '(display-buffer-use-some-frame
                                 display-buffer-pop-up-frame))
                       display-alist))
      (select-frame-set-input-focus
       (window-frame (get-buffer-window original-buffer t))))))

(defun etcs-toggle-bare ()
  "Toggles the elisp variable 'etcs-bare-p."
  (interactive)
  (setq etcs-bare-p (not etcs-bare-p))
  (concat "using " (etcs-executable-with-bare)))

(defun etcs-display ()
   "Attempts to bring the ETCS buffer to the fore (calling `display-buffer')."
   (interactive)
   (display-buffer etcs-buffer-name))

(defun etcs-vertical ()
  "Runs a ETCS session after splitting the window"
  (interactive)
  (etcs '(display-buffer-below-selected)))

(defun etcs-horizontal ()
  "Runs a ETCS session after splitting the window"
  (interactive)
  (etcs '(display-buffer-reuse-window
         (lambda (b al)
           (let ((split-height-thresetcsd nil)
                 (split-width-thresetcsd 0))
             (display-buffer-pop-up-window b al))))
       '((window-width . 83) (reusable-frames . nil))))

(defvar etcs-new-buffer-style etcs-new-buffer-style-default)

(setq etcs-new-buffer-style-alist
      '((horizontal . etcs-horizontal)
        (vertical . etcs-vertical)
        (new-frame . etcs)))

(defun etcs-with-region ()
  "Starts a ETCS session and pastes selected region into it. If there is no active region, pastes wetcse buffer."
  (interactive)
  (let* ((style-str (completing-read
                     (concat "ETCS buffer position ("
                             (symbol-name etcs-new-buffer-style)
                             "): ")
                     '("horizontal" "vertical" "new-frame")
                     nil
                     t
                     nil
                     nil
                     (symbol-name etcs-new-buffer-style)
                     t))
         (style (intern style-str))
         (starter (cdr (assoc style etcs-new-buffer-style-alist))))
    (setq etcs-new-buffer-style style)
    (save-mark-and-excursion (funcall starter))
    (if (region-active-p)
        (copy-region-as-etcs-definition-quietly (region-beginning) (region-end))
      (let ((beg (point-min))
            (end (progn
                   (while (looking-at "[[:space:]]*\n") (forward-line 1))
                   (search-backward "\n\n")
                   (while (looking-at "[[:space:]]*\n") (forward-line 1))
                   (point))))
        (push-mark (point-min))
        (activate-mark t)
        (copy-region-as-etcs-definition-quietly beg end)))))

(defun run-program (filename niceness)
  "Runs a PROGRAM in a comint window, with a given (optional) NICENESS."
  (interactive "fProgram to run: \nP")
  (let* ((niceval (cond ((null niceness) 0)
                        ((listp niceness) 10)
                        (t (prefix-numeric-value niceness))))
         (progname (format "%s(n:%d)"
                          (file-name-nondirectory filename)
                          niceval))
         (buf (cond ((> niceval 0)
                     (make-comint progname "nice" nil
                                  (format "-%d" niceval)
                                  (expand-file-name filename)))
                   (t (make-comint progname
                                   (expand-file-name filename)
                                   nil)))))
    (switch-to-buffer buf)))

(defun etcs-toggle-var (s)
  "Toggles the boolean variable STRING."
  (message (concat "Toggling " s))
  (send-raw-string-to-etcs
   (format (concat "val _ = (%s := not (!%s);"
                   "print (\"*** %s now \" ^"
                   "Bool.toString (!%s)^\" ***\\n\"))")
           s s s s)
   nil))

(defun etcs-toggle-var-quiet (s)
  "Toggles the boolean variable STRING."
  (send-raw-string-to-etcs
   (format "val _ = (%s := not (!%s));" s s) nil))

(defun etcs-toggle-trace (s &optional arg)
  "Toggles the trace variable STRING between zero and non-zero.  With prefix
argument N, sets the trace to that value in particular."
  (interactive "sTrace name: \nP")
  (if (null arg)
      (progn
        (message (concat "Toggling " s))
        (send-raw-string-to-etcs
         (format "val _ = let val nm = \"%s\"
                      fun findfn r = #name r = nm
                      val old =
                            #trace_level (valOf (List.find findfn (traces())))
                  in
                      print (\"** \"^nm^\" trace now \");
                      if 0 < old then (set_trace nm 0; print \"off\\n\")
                      else (set_trace nm 1; print \"on\\n\")
                  end handle Option =>
                        print \"** No such trace var: \\\"%s\\\"\\n\""
                 s s)
         nil))
    (let ((n (prefix-numeric-value arg)))
      (message (format "Setting %s to %d" s n))
      (send-raw-string-to-etcs
       (format "val _ = (set_trace \"%s\" %d; print \"** %s trace now %d\\n\")
                        handle ETCS_ERR _ =>
                           print \"** No such trace var: \\\"%s\\\"\\n\""
               s n s n s)
       nil))))

(defun etcs-toggle-unicode ()
  "Toggles the \"Unicode\" trace."
  (interactive)
  (etcs-toggle-trace "Unicode"))


(defun etcs-toggle-emacs-tooltips ()
  "Toggles whether ETCS produces tooltip information while pretty-printing."
  (interactive)
  (etcs-toggle-trace "PPBackEnd show types"))

(defun etcs-toggle-pp-styles ()
  "Toggles whether ETCS produces style informations while pretty-printing."
  (interactive)
  (etcs-toggle-trace "PPBackEnd use styles"))

(defun etcs-toggle-pp-cases ()
  "Toggles the \"pp_cases\" trace."
  (interactive)
  (etcs-toggle-trace "pp_cases")
  (etcs-toggle-trace "use pmatch_pp"))

(defun etcs-toggle-pp-annotations ()
  "Toggles whether ETCS produces annotations while pretty-printing."
  (interactive)
  (etcs-toggle-trace "PPBackEnd use annotations"))

(defun etcs-toggle-goalstack-fvs ()
  "Toggles the trace \"Goalstack.print_goal_fvs\"."
  (interactive)
  (etcs-toggle-trace "Goalstack.print_goal_fvs"))

(defun etcs-toggle-goalstack-print-goal-at-top ()
  "Toggles the trace \"Goalstack.print_goal_at_top\"."
  (interactive)
  (etcs-toggle-trace "Goalstack.print_goal_at_top"))

(defun etcs-toggle-goalstack-num-assums (arg)
  "Toggles the number of assumptions shown in a goal."
  (interactive "nMax. number of visible assumptions: ")
  (etcs-toggle-trace "Goalstack.howmany_printed_assums" arg))

(defun etcs-toggle-goalstack-num-subgoals (arg)
  "Toggles the number of shown subgoals."
  (interactive "nMax. number of shown subgoals: ")
  (etcs-toggle-trace "Goalstack.howmany_printed_subgoals" arg))

(defun etcs-toggle-simplifier-trace (arg)
  "Toggles the trace \"simplifier\".  With ARG sets trace to this value."
  (interactive "P")
  (etcs-toggle-trace "simplifier" arg))

(defun etcs-toggle-show-types (arg)
  "Toggles the global show_types variable. With prefix ARG sets trace to this value (setting trace to 2, is the same as setting the show_types_verbosely variable)."
  (interactive "P")
  (etcs-toggle-trace "types" arg))

(defun etcs-toggle-show-types-verbosely ()
  "Toggles the global show_types_verbosely variable."
  (interactive)
  (etcs-toggle-var "Globals.show_types_verbosely"))

(defun etcs-toggle-show-numeral-types()
  "Toggles the global show_numeral_types variable."
  (interactive)
  (etcs-toggle-var "Globals.show_numeral_types"))

(defun etcs-toggle-show-assums()
  "Toggles the global show_assums variable."
  (interactive)
  (etcs-toggle-var "Globals.show_assums"))

(defun etcs-toggle-show-tags()
  "Toggles the global show_tags variable."
  (interactive)
  (etcs-toggle-var "Globals.show_tags"))

(defun etcs-toggle-show-axioms()
  "Toggles the global show_axioms variable."
  (interactive)
  (etcs-toggle-var "Globals.show_axioms"))

(defun etcs-toggle-quietdec ()
  "Toggles quiet declarations in the interactive system."
  (interactive)
  (message "Toggling 'Quiet declaration'")
  (send-raw-string-to-etcs
   (concat
    "val _ = print (\"*** 'Quiet declaration' now \" ^"
    "Bool.toString (ETCS_Interactive.toggle_quietdec()) ^ \" ***\\n\")")
   nil)
  (etcs-toggle-var "Globals.interactive"))

(defun etcs-toggle-quiet-quietdec ()
  "Toggles quiet declarations in the interactive system."
  (interactive)
  (send-raw-string-to-etcs "val _ = ETCS_Interactive.toggle_quietdec()" nil)
  (etcs-toggle-var-quiet "Globals.interactive"))

(defun etcs-toggle-show-times()
  "Toggles the elisp variable 'etcs-emit-time-elapsed-p."
  (interactive)
  (setq etcs-emit-time-elapsed-p (not etcs-emit-time-elapsed-p))
  (message (if etcs-emit-time-elapsed-p "Elapsed times WILL be displayed"
             "Elapsed times WON'T be displayed")))

(defun etcs-toggle-echo-commands ()
  "Toggles the elisp variable 'etcs-echo-commands-p."
  (interactive)
  (setq etcs-echo-commands-p (not etcs-echo-commands-p))
  (message (if etcs-echo-commands-p "Commands WILL be echoed"
             "Commands WON'T be echoed")))

(defun etcs-toggle-auto-load ()
  "Toggles the elisp variable 'etcs-auto-load-p."
  (interactive)
  (setq etcs-auto-load-p (not etcs-auto-load-p))
  (message (if etcs-auto-load-p "automatic loading ON"
             "automatic loading OFF")))

(defun etcs-toggle-ppbackend ()
  "Toggles between using the Emacs and \"raw\" terminal pretty-printing."
  (interactive)
  (send-raw-string-to-etcs
   (concat
    "val _ = if #name (#extras (!Parse.current_backend)) = \"emacs_terminal\" then"
    "(Parse.current_backend := PPBackEnd.raw_terminal;"
    "print \"*** PP Backend now \\\"raw\\\" ***\\n\")"
    "else (Parse.current_backend := PPBackEnd.emacs_terminal;"
    "print \"*** PP Backend now \\\"emacs\\\" ***\\n\")")
   nil))

(defun etcs-restart-goal ()
  "Restarts the current goal."
  (interactive)
  (send-raw-string-to-etcs "proofManagerLib.restart()" etcs-echo-commands-p))

(defun etcs-drop-goal ()
  "Drops the current goal."
  (interactive)
  (send-raw-string-to-etcs "proofManagerLib.drop()" etcs-echo-commands-p))

(defun etcs-open-string (prefixp)
  "Opens ETCS modules, prompting for the name of the module to load.
With prefix ARG, toggles quietdec variable before and after opening,
potentially saving a great deal of time as tediously large modules are
printed out.  (That's assuming that quietdec is false to start with.)"
  (interactive "P")
  (let* ((prompt0 "Name of module to (load and) open")
         (prompt (concat prompt0 (if prefixp " (toggling quietness)") ": "))
         (module-name (read-string prompt)))
    (etcs-load-string module-name)
    (if prefixp (etcs-toggle-quietdec))
    (send-raw-string-to-etcs (concat "open " module-name) etcs-echo-commands-p)
    (if prefixp (etcs-toggle-quietdec))))

(defun etcs-db-match (tm)
  "Does a DB.match [] on the given TERM (given as a string, without quotes) and formats the result nicely."
  (interactive "sTerm to match on: ")
  (send-raw-string-to-etcs (format "Etcs_pp.print_match [] (Term`%s`)" tm)
                          etcs-echo-commands-p))

(defun etcs-check-dbselector (s)
  (if (string-prefix-p "'" s) (string-suffix-p "'" s)
    (if (string-prefix-p "\"" s) (string-suffix-p "\"" s)
      t)))

(defun etcs-make-db-select-string (args)
  (let ((sels (mapconcat (lambda (s) (if (string-prefix-p "'" s)
                                      (concat "DB.SelTHY \""
                                              (substring s 1 -1) "\"")
                                    (if (string-prefix-p "\"" s)
                                        (concat "DB.SelNM \""
                                                (substring s 1 -1) "\"")
                                      (concat "DB.SelTM “" s "”"))))
                         args ", ")))
    (concat "DB.selectDB [" sels "]")))

(defconst etcs-db-select-info "('thy'; \"name\"; term pattern)" "")
(defun etcs-db-select (arg1)
  "Calls DB.selectDB on the sequence of `selectors' provided.
A selector is a string (as per DB.find) that matches against the name of
the theorem, given in double quotes; a theory name, given in single quotes,
or a term pattern, given without delimiters."
  (interactive "sFirst selector pattern('thy'; \"name\"; term pattern): ")
  (or (string-equal arg1 "")
      (and (not (etcs-check-dbselector arg1))
           (error "Malformed DB selector: %s" arg1))
      (let ((args (list arg1)) next-arg)
        (while (and (setq next-arg
                          (read-string (concat "Next DB selector"
                                               etcs-db-select-info
                                               ": ")))
                    (not (string-equal next-arg "")))
          (if (etcs-check-dbselector next-arg)
              (setq args (cons next-arg args))
            (error "Malformed DB selector: %s" next-arg)))
        (send-string-to-etcs (etcs-make-db-select-string args)))))

(defun etcs-db-find (tm)
  "Does a DB.find on the given string and formats the result nicely."
  (interactive "sTheorem name part: ")
  (send-raw-string-to-etcs (format "Etcs_pp.print_find \"%s\"" tm)
                          etcs-echo-commands-p))

(defun etcs-db-check (ty)
  "Does a sanity check on the current theory."
  (interactive "sTheory name: ")
  (send-raw-string-to-etcs (format "Sanity.sanity_check_theory \"%s\"" ty)
                          etcs-echo-commands-p))

(defun etcs-db-check-current ()
  "Does a sanity check on the current theory."
  (interactive)
  (send-raw-string-to-etcs "Sanity.sanity_check()" etcs-echo-commands-p))

(defun etcs-db-find-consts (ty)
  "Does bossLib.find_consts on a given type and prints the result."
  (interactive "sType of constant: ")
  (send-raw-string-to-etcs (format "bossLib.find_consts ``%s``" ty)
                          etcs-echo-commands-p))

(defun etcs-drop-all-goals ()
  "Drops all ETCS goals from the current proofs object."
  (interactive)
  (send-raw-string-to-etcs "proofManagerLib.drop_all()" etcs-echo-commands-p))

(defun etcs-subgoal-tactic (p)
  "Without a prefix argument, sends term at point (delimited by backquote
characters) as a subgoal to prove.  Will usually create at least two sub-
goals; one will be the term just sent, and the others will be the term sent
STRIP_ASSUME'd onto the assumption list of the old goal.  This mimicks what
happens with the \"by\" command.

With a prefix argument, sends the delimited term as if the
argument of a \"suffices_by\" command, making two new goals: the
first is to show that the new term implies the old goal, and the
second is to show the new term.

(Loads the BasicProvers module if not already loaded.)"
  (interactive "P")
  (let ((tactic (if p "Tactical.Q_TAC Tactic.SUFF_TAC"
                      "(fn q => BasicProvers.byA(q,ALL_TAC))")))
    (send-string-to-etcs
     (format "proofManagerLib.e (%s `%s`)"
             tactic
             (etcs-term-at-point)))))


;; (defun etcs-return-key ()
;;   "Run comint-send-input, but only if both: the user is editting the
;; last command in the buffer, and that command ends with a semicolon.
;; Otherwise, insert a newline at point."
;;   (interactive)
;;   (let ((comand-finished
;;          (let ((process (get-buffer-process (current-buffer))))
;;            (and (not (null process))
;;                 (let ((pmarkpos (marker-position
;;                                  (process-mark process))))
;;                   (and (< (point) pmarkpos)
;;                        (string-match ";[ \t\n\r]*$"
;;                                      (buffer-substring pmarkpos
;;                                                        (point-max)))))))))
;;     (if command-finished
;;         (progn
;;           (goto-char (point-max))
;;           (comint-send-input))
;;       (insert "\n"))))

;; (define-key comint-mode-map "\r" 'etcs-return-key)

(defun etcs-overload-info-for (term-name)
  "Get ETCS to print overload information for term-name"
  (interactive "sOverloaded name: ")
  (send-string-to-etcs (format "overload_info_for \"%s\"" term-name)))


;;load-path
(defun ml-quote (s)
   (let* (
     (s1 (replace-regexp-in-string "\\\\" "\\\\\\\\" s))
     (s2 (replace-regexp-in-string "\n" "\\\\n" s1))
     (s3 (replace-regexp-in-string "\t" "\\\\t" s2))
     (s4 (replace-regexp-in-string "\"" "\\\\\"" s3))
   ) s4))

(defun etcs-add-load-path (path)
  (interactive "DAdd new load-path: ")
  (let ((epath (expand-file-name path)))
  (if (file-accessible-directory-p epath)
     (progn
        (send-raw-string-to-etcs
            (concat "loadPath := \"" (ml-quote epath) "\" :: !loadPath;")
            nil)
        (message (concat "Load-path \"" epath "\" added.")))
     (progn (ding) (message "Not a directory!")))
))


(defun etcs-show-current-load-paths ()
   (interactive)
   (send-raw-string-to-etcs "print_current_load_paths ()" nil))

(defun etcs-type-info ()
   "Gives informations about the type of a term"
   (interactive)
   (let* ((txt (buffer-substring-no-properties (region-beginning) (region-end)))
          (use-marked (and (etcs-is-region-active) (= (cl-count ?\` txt) 0)))
          (at-point-term (thing-at-point 'etcs-term))

          (main-term (ml-quote (if use-marked txt at-point-term)))
          (context-term (ml-quote (if use-marked at-point-term "")))
          (command-s (concat "print_type_of_in_context true "
                      (if use-marked (concat "(SOME \"" context-term "\")") "NONE")
                      " \"" main-term "\"")))
   (send-raw-string-to-etcs command-s nil)))


(defun etcspp-decode-color (code)
  (cond ((equal code "0") "#000000")
        ((equal code "1") "#840000")
        ((equal code "2") "#008400")
        ((equal code "3") "#848400")
        ((equal code "4") "#000084")
        ((equal code "5") "#840084")
        ((equal code "6") "#008484")
        ((equal code "7") "#555555")
        ((equal code "8") "#949494")
        ((equal code "9") "#FF0000")
        ((equal code "A") "#00C600")
        ((equal code "B") "#FFFF00")
        ((equal code "C") "#0000FF")
        ((equal code "D") "#FF00FF")
        ((equal code "E") "#00FFFF")
        ((equal code "F") "#FFFFFF")
))

(defun etcspp-decode-full-style (style)
   (let* (
       (fg (substring style 0 1))
       (bg (substring style 1 2))
       (b (substring style 2 3))
       (u (substring style 3 4))
       (fg-face (if (equal fg "-") nil
                    (cons :foreground (cons (etcspp-decode-color fg) ()))))
       (bg-face (if (equal bg "-") nil
                    (cons :background (cons (etcspp-decode-color bg) ()))))
       (b-face  (if (equal b "-") nil
                    (cons :weight (cons 'bold ()))))
       (u-face  (if (equal u "-") nil
                    (cons :underline (cons t ())))))
       (cons 'face (cons (append fg-face bg-face b-face u-face) ()))))


(defun etcspp-find-comment-end (n)
   (if (not (re-search-forward "\\((\\*(\\*(\\*\\)\\|\\(\\*)\\*)\\*)\\)" nil t 1))
       nil
       (if (save-excursion (goto-char (- (point) 6))
                           (looking-at "(\\*(\\*(\\*"))
           (progn
              (etcspp-find-comment-end (+ n 1)))
           (if (= n 1) t (etcspp-find-comment-end (- n 1))))))

(defun etcspp-execute-code-face-tooltip (start end toolprop codeface)
  (let ((tooltipprop
         (if (equal toolprop nil) nil (list 'help-echo toolprop))))
    (add-text-properties start end (append codeface tooltipprop))))

(defun etcspp-execute-code (code arg1 start end)
  (cond ((equal code "FV")
             (etcspp-execute-code-face-tooltip start end arg1
             '(face etcs-free-variable)))
        ((equal code "BV")
             (etcspp-execute-code-face-tooltip start end arg1
             '(face etcs-bound-variable)))
        ((equal code "TV")
             (etcspp-execute-code-face-tooltip start end arg1
             '(face etcs-type-variable)))
        ((equal code "TY")
             (etcspp-execute-code-face-tooltip start end arg1
             '(face etcs-type)))
        ((equal code "CO")
         (etcspp-execute-code-face-tooltip start end arg1 nil))
        ((equal code "ST")
           (add-text-properties start end
             (etcspp-decode-full-style arg1)))))

(setq temp-etcs-output-buf nil)

(defun etcspp-quiet-reset ()
  (let ((tmpbuf (or temp-etcs-output-buf
                     (generate-new-buffer " *ETCS output filter*)"))))
      (setq temp-etcs-output-buf tmpbuf)
      (with-current-buffer tmpbuf
        (delete-region (point-min) (point-max)))))

(defun etcspp-reset ()
  (interactive)
  (etcspp-quiet-reset)
  (send-raw-string-to-etcs "print \"\\n\\n*** etcs-mode reset ***\\n\";" nil))

; this filter function is complicated by the fact that comint chunks
; output (in 1024 character chunks in my tests) and so doesn't
; necessarily give complete (in the sense of containing matching
; comment-blocks) strings to the filter. This means that a solution
; with with-temp-buffer won't work. Instead, there is a persistent
; working space buffer, and if the code finds a non-matching comment
; start (a "(*(*(*" substring), it just leaves that in the working
; space so that the next piece of output can be appended and processed
; properly.
(defun etcspp-output-filter (s)
  "Converts a munged emacs_terminal string into a pretty one with text properties."
  (interactive "sinput: ")
  (let* ((tmpbuf (or temp-etcs-output-buf
                     (generate-new-buffer " *ETCS output filter*)")))
         end)
    (setq temp-etcs-output-buf tmpbuf)
    (with-current-buffer tmpbuf
      (unwind-protect
          (progn
            (goto-char (point-max))
            (insert s)
            (goto-char (point-min))
            (while (and (not end) (search-forward "(*(*(*" nil t))
              (let ((uptoann (- (point) 6))
                    (start (point)))
                (if (not (etcspp-find-comment-end 1))
                    (progn
                      (goto-char uptoann)
                      (setq end t))
                  (delete-region uptoann start)
                  (let*
                      ((start (- start 6))
                       (code (buffer-substring start (+ start 2)))
                       (argument
                        (save-excursion
                          (goto-char (+ start 2))
                          (if (equal (following-char) 0)
                              (progn
                                (goto-char (+ (point) 1))
                                (skip-chars-forward "^\^@")
                                (prog1
                                    (if (equal (+ start 3) (point)) nil
                                    (buffer-substring (+ start 3)
                                                            (point)))
                                  (delete-region (+ start 2) (1+ (point)))))
                            nil))))
                       (etcspp-execute-code code argument
                        (+ start 2)
                        (- (point) 6))
                       (delete-region start (+ start 2))
                       (delete-region (- (point) 6) (point))
                       (goto-char start)))))
            (if (not end)
                (progn
                  (goto-char (point-max))
                  (skip-chars-backward "(*")))
            (prog1
                (buffer-substring (point-min) (point))
              (delete-region (point-min) (point))))))))

(defun etcsmakepp-mark-error (start end)
   (add-text-properties start end '(face etcsmake-error)))


(defun etcsmakepp-mark-mosml-error ()
  (interactive)
  (goto-char (point-min))
  (while (re-search-forward "^!" nil t)
     (let* ((start (match-beginning 0)))
     (forward-line)
     (while (or (looking-at "!") (looking-at " ")) (forward-line))
     (etcsmakepp-mark-error start (- (point) 1))))
)

(setq temp-etcsmake-output-buf nil)
(defun etcsmakepp-output-filter (s)
  "Converts a munged emacs_terminal string into a pretty one with text properties."
  (interactive "sinput: ")
  (let* ((tmpbuf (or temp-etcsmake-output-buf
                     (generate-new-buffer " *ETCSMAKE output filter*)")))
         end)
    (setq temp-etcsmake-output-buf tmpbuf)
    (with-current-buffer tmpbuf
      (unwind-protect
          (progn
            (goto-char (point-max))
            (insert s)
            (etcsmakepp-mark-mosml-error)
            (prog1
                (buffer-substring (point-min) (point-max))
              (delete-region (point-min) (point-max))))))))

(add-hook 'sml-mode-hook
          (lambda ()
            (local-set-key "`" 'etcsscript-dbl-backquote)
            (message "Running ETCS SML hook")
))

(defun etcs-find-quoted-material (limit)
  (let ((beginmatch (re-search-forward etcs-term-begin-re limit t))
        (ppss (syntax-ppss)))
    (while (and beginmatch (or (nth 3 ppss) (nth 4 ppss)))
      (setq beginmatch (re-search-forward etcs-term-begin-re limit t))
      (setq ppss (syntax-ppss)))
    (if (not beginmatch) nil
      (let* ((start-delim (match-string-no-properties 0))
             (begin-marker
              (if (= (length start-delim) 1)
                  (set-marker (make-marker) (1- (point)))
                (point-marker)))
             (endre (etcs-term-matching-delim start-delim))
             (endmatch (if endre (re-search-forward endre limit t)
                         (message (format "No end-delim for %s" start-delim))
                         nil)))
        (if (not endmatch) nil
          (if (= (length start-delim) 1) nil (goto-char (match-beginning 0)))
          (set-match-data (list begin-marker (point-marker)))
          t)))))
;  (re-search-forward "^Theorem[[:space:]]+[A-Za-z0-9'_]+\\(?:\\[[A-Za-z0-9_,]+\\]\\)?[[:space:]]*:\\(\\(?:\n  \\|.\\)+\\)\nProof" limit t))

(defun etcs-thm-prefix (s)
  (or (string-prefix-p "Theorem" s) (string-prefix-p "Triviality" s)))
(defun etcs-defn-prefix (s) (string-prefix-p "Definition" s))
(defun etcs-indn-prefix (s)
  (or (string-prefix-p "Inductive" s) (string-prefix-p "CoInductive" s)))

(defun etcs-term-matching-delim (start-delim)
  (pcase start-delim
    ("“" "”")
    ("‘" "’")
    ("Datatype:" "^End\\>")
    ((pred etcs-thm-prefix) "^Proof\\>")
    ((pred etcs-indn-prefix) "^End\\>")
    ((pred etcs-defn-prefix) "^Termination\\>\\|^End\\>")))


(defgroup etcs-faces nil "Faces used in pretty-printing ETCS values"
  :group 'faces
  :group 'etcs)

(defface etcsmake-error
  '((((class color))
     :foreground "red"
     :weight bold))
  "The face for errors shown by ETCSMAKE."
  :group 'etcs-faces)

(defface etcs-free-variable
  '((((class color))
     :foreground "blue"
     :weight bold))
  "The face for presenting free variables in ETCS terms."
  :group 'etcs-faces)

(defface etcs-bound-variable
  '((((class color))
     :foreground "#009900"))
  "The face for presenting bound variables in ETCS terms."
  :group 'etcs-faces)

(defface etcs-type-variable
  '((((class color))
     :foreground "purple"
     :slant italic))
  "The face for presenting free type variables in ETCS terms."
  :group 'etcs-faces)

(defface etcs-type
  '((((class color))
     :foreground "cyan3"
     :slant italic))
  "The face for presenting ETCS types."
  :group 'etcs-faces)

(defun etcs-region-to-unicode-pdf (filename beg end)
  "Print region to FILE as a PDF, handling Unicode characters."
  (interactive "FFile to write to: \nr")
  (if (and transient-mark-mode (not mark-active))
      (error "No active region"))
  (let* ((temp-ps-file (make-temp-file "etcsprint" nil ".ps"))
         (lpr-switches
          (list "-font" etcs-unicode-print-font-filename
                "-out" temp-ps-file))
         (lpr-add-switches nil)
         (lpr-command "uniprint"))
    (lpr-region beg end)
    (shell-command (concat "ps2pdf " temp-ps-file " " filename))
    (delete-file temp-ps-file)))

(setq etcs-term-beginend-re
      (concat
       (regexp-opt
        '("Theorem" "End" "Definition" "Inductive" "Termination" "Proof"
          "CoInductive" "Datatype" "Triviality") "^\\(")
       "\\|"
       (regexp-opt '("“" "‘" "”" "’"))))
(defvar etcs-term-end-re (regexp-opt '("End" "Termination" "Proof" "”" "’")))
(defvar etcs-term-begin-re
  (concat
   (regexp-opt '("“" "‘")) "\\|"
   etcs-quoted-theorem-proof-re-begin "\\|"
   etcs-quoted-definition-re-begin "\\|"
   "Datatype[[:space:]]*:"))

(defun etcs-fl-term-bump-backwards (pos)
  (save-excursion
    (goto-char pos)
    (let ((match (re-search-backward etcs-term-beginend-re nil t)))
      (if (not match) pos
        (if (looking-at etcs-term-end-re) pos
          (if (looking-at etcs-term-begin-re) (match-beginning 0) pos))))))

(defun etcs-fl-term-bump-forwards (pos)
  (save-excursion
    (goto-char pos)
    (let ((match (re-search-forward etcs-term-beginend-re nil t)))
      (if (not match) pos
        (goto-char (match-beginning 0))
        (if (looking-at etcs-term-begin-re) pos
          (if (looking-at etcs-term-end-re) (match-end 0) pos))))))

(defun etcs-select-pattern-list-tactic (begin end)
  "Send current region (which must include the delimiting square
brackets) as argument to Q.SELECT_GOAL_LT, which list-tactic
takes a list of patterns to use to select the desired current
goal. If the region is not active, instead scan for a term in
the surrounding text (as done by ‘etcs-do-goal’ and
‘etcs-subgoal-tactic’)."
  (interactive "r")
  (let ((tosend
         (if (and begin (region-active-p))
             (buffer-substring-no-properties begin end)
           (format "[‘%s’]" (etcs-term-at-point)))))
    (send-raw-string-to-etcs
     (format "proofManagerLib.expand_list (Q.SELECT_GOAL_LT %s)" tosend)
     etcs-echo-commands-p)))

;;The key combinations
(define-key global-map "\M-h" 'etcs-map)
(define-key global-map (kbd "C-M-h") 'etcs-movement-map)
(define-prefix-command 'etcspp-map)


(define-key etcs-map "\C-c" 'etcs-interrupt)
(define-key etcs-map "\C-l" 'etcs-recentre)
(define-key etcs-map "\C-q" 'etcs-toggle-quietdec)
(define-key etcs-map "\C-s" 'etcs-toggle-simplifier-trace)
(define-key etcs-map "\C-v" 'etcs-scroll-up)
(define-key etcs-map "\M-r" 'copy-region-as-etcs-definition)
(define-key etcs-map "\C-r" 'copy-region-as-etcs-definition-quietly)
(define-key etcs-map "\M-p" 'etcs-select-pattern-list-tactic)
(define-key etcs-map "\M-P" 'etcspp-map)
(define-key etcs-map "\M-q" 'copy-region-as-etcs-definition-real-quietly)
(define-key etcs-map "\M-t" 'etcs-toggle-show-times)
(define-key etcs-map "\M-s" 'etcs-subgoal-tactic)
(define-key etcs-map "\M-v" 'etcs-scroll-down)
(define-key etcs-map "b"    'etcs-backup)
(define-key etcs-map "B"    'etcs-user-backup)
(define-key etcs-map "S"    'etcs-user-save-backup)
(define-key etcs-map "d"    'etcs-drop-goal)
(define-key etcs-map "D"    'etcs-drop-all-goals)
(define-key etcs-map "e"    'copy-region-as-etcs-tactic)
(define-key etcs-map "\M-e" 'etcs-find-eval-next-tactic)
(define-key etcs-map "E"    'copy-region-as-goaltree-tactic)
(define-key etcs-map "g"    'etcs-do-goal)
(define-key etcs-map "G"    'etcs-do-goaltree)
(define-key etcs-map "h"    'etcs)
(define-key etcs-map "H"    'etcs-with-region)
(define-key etcs-map "\M-m" 'etcsmake)
(define-key etcs-map "2"    'etcs-vertical)
(define-key etcs-map "3"    'etcs-horizontal)
(define-key etcs-map "4"    'etcs-display)
(define-key etcs-map "l"    'etcs-load-file)
(define-key etcs-map "m"    'etcs-db-match)
(define-key etcs-map "M"    'etcs-db-select)
(define-key etcs-map "f"    'etcs-db-find)
(define-key etcs-map "c" 'etcs-db-find-consts)
(define-key etcs-map "n"    'etcs-name-top-theorem)
(define-key etcs-map "o"    'etcs-open-string)
(define-key etcs-map "O"    'etcs-overload-info-for)
(define-key etcs-map "p"    'etcs-print-goal)
(define-key etcs-map "P"    'etcs-print-all-goals)
(define-key etcs-map "r"    'etcs-rotate)
(define-key etcs-map "R"    'etcs-restart-goal)
(define-key etcs-map "t"    'mark-etcs-tactic)
(define-key etcs-map "T"    'etcs-start-termination-proof)
(define-key etcs-map "i"    'etcs-type-info)
(define-key etcs-map "s"    'interactive-send-string-to-etcs)
(define-key etcs-map "u"    'etcs-use-file)
(define-key etcs-map "C"    'etcs-db-check-current)
(define-key etcs-map "a"    'etcs-remove-unicode)
(define-key etcs-map "*"    'etcs-template-comment-star)
(define-key etcs-map "-"    'etcs-template-comment-minus)
(define-key etcs-map "="    'etcs-template-comment-equal)
(define-key etcs-map "\M-c" 'etcs-template-etcs-coreln)
(define-key etcs-map "\M-d" 'etcs-template-define)
(define-key etcs-map "\M-i" 'etcs-template-etcs-reln)
(define-key etcs-map "\M-x" 'etcs-template-store-thm)


(define-key etcs-map   "\C-a" 'etcs-toggle-show-assums)
(define-key etcspp-map "a"    'etcs-toggle-show-assums)
(define-key etcs-map   "\C-t" 'etcs-toggle-show-types)
(define-key etcspp-map "\C-t" 'etcs-toggle-show-types)
(define-key etcs-map   "\C-n" 'etcs-toggle-show-numeral-types)
(define-key etcspp-map "n"    'etcs-toggle-show-numeral-types)
(define-key etcs-map   "\C-f" 'etcs-toggle-goalstack-fvs)
(define-key etcspp-map "f"    'etcs-toggle-goalstack-fvs)
(define-key etcs-map   "\C-o" 'etcs-toggle-goalstack-print-goal-at-top)
(define-key etcspp-map "o"    'etcs-toggle-goalstack-print-goal-at-top)
(define-key etcs-map   "\M-a" 'etcs-toggle-goalstack-num-assums)
(define-key etcspp-map "\M-a" 'etcs-toggle-goalstack-num-assums)
(define-key etcs-map   "\C-u" 'etcs-toggle-unicode)
(define-key etcspp-map "u"    'etcs-toggle-unicode)
(define-key etcs-map   "\C-p" 'etcs-toggle-ppbackend)
(define-key etcspp-map "p"    'etcs-toggle-ppbackend)
(define-key etcspp-map "b"    'etcs-toggle-emacs-tooltips)
(define-key etcspp-map "t"    'etcs-toggle-pp-annotations)
(define-key etcspp-map "s"    'etcs-toggle-pp-styles)
(define-key etcspp-map "c"    'etcs-toggle-pp-cases)

(define-key etcs-movement-map "u" 'etcs-movement-backward-up-list)





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The definition of the ETCS menu
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-key-after (lookup-key global-map [menu-bar])
  [etcs-menu]
  (cons "ETCS" (make-sparse-keymap "ETCS"))
  'tools)


;; ETCS misc
(define-key
  global-map
  [menu-bar etcs-menu etcs-misc]
  (cons "Misc" (make-sparse-keymap "Misc")))

(define-key global-map [menu-bar etcs-menu etcs-misc clean-up]
   '("Clean up (remove tab, white spaces at end of line, etc...)" .
     etcs-cleanup-buffer))

(define-key global-map [menu-bar etcs-menu etcs-misc remove-unicode]
   '("Replace common ETCS unicode symbols" .
     etcs-remove-unicode))

(define-key global-map [menu-bar etcs-menu etcs-misc check-names]
   '("Check names in store_thm, ..." . etcs-check-statement-eq-string))

(define-key global-map [menu-bar etcs-menu etcs-misc sep4]
   '(menu-item "--"))

(define-key global-map [menu-bar etcs-menu etcs-misc check-theory-current]
   '("Sanity check current theory" . etcs-db-check-current))

(define-key global-map [menu-bar etcs-menu etcs-misc check-theory]
   '("Sanity check theory" . etcs-db-check))

(define-key global-map [menu-bar etcs-menu etcs-misc sep3]
   '(menu-item "--"))

(define-key global-map [menu-bar etcs-menu etcs-misc mark-tactic]
   '("Mark tactic" . mark-etcs-tactic))

(define-key global-map [menu-bar etcs-menu etcs-misc backward-tactic]
   '("Move to previous tactic" . backward-etcs-tactic))

(define-key global-map [menu-bar etcs-menu etcs-misc forward-tactic]
   '("Move to next tactic" . forward-etcs-tactic))

(define-key global-map [menu-bar etcs-menu etcs-misc sep2]
   '(menu-item "--"))

(define-key global-map [menu-bar etcs-menu etcs-misc open-string]
   '("Load and open" . etcs-open-string))

(define-key global-map [menu-bar etcs-menu etcs-misc use-file]
   '("Use file" . etcs-use-file))

(define-key global-map [menu-bar etcs-menu etcs-misc load-file]
   '("Load file" . etcs-load-file))

(define-key global-map [menu-bar etcs-menu etcs-misc auto-load]
   '(menu-item "Automatic loading" etcs-toggle-auto-load
                     :button (:toggle
                              . (and (boundp 'etcs-auto-load-p)
                                     etcs-auto-load-p))))

(define-key global-map [menu-bar etcs-menu etcs-misc show-load-paths]
   '("Show load-paths" . etcs-show-current-load-paths))

(define-key global-map [menu-bar etcs-menu etcs-misc add-load-path]
   '("Add load-path ..." . etcs-add-load-path))

(define-key global-map [menu-bar etcs-menu etcs-misc sep1]
   '(menu-item "--"))

(define-key global-map [menu-bar etcs-menu etcs-misc etcs-overload-info-for]
  '("Overload info for string" . etcs-overload-info-for))

(define-key global-map [menu-bar etcs-menu etcs-misc etcs-type-info]
   '("Type info of marked term" . etcs-type-info))

(define-key global-map [menu-bar etcs-menu etcs-misc sep0]
   '(menu-item "--"))

(define-key global-map [menu-bar etcs-menu etcs-misc db-find]
   '("DB find" . etcs-db-find))

(define-key global-map [menu-bar etcs-menu etcs-misc db-match]
   '("DB match" . etcs-db-match))



;; templates
(define-key
  global-map
  [menu-bar etcs-menu etcs-template]
  (cons "Templates" (make-sparse-keymap "Templates")))

(define-key global-map [menu-bar etcs-menu etcs-template new-script]
   '("New theory" . etcs-template-new-script-file))

(define-key global-map [menu-bar etcs-menu etcs-template new-datatype]
   '("New datatype" . etcs-template-new-datatype))

(define-key global-map [menu-bar etcs-menu etcs-template etcs-coreln]
   '("Coinductive definition" . etcs-template-etcs-coreln))

(define-key global-map [menu-bar etcs-menu etcs-template etcs-reln]
   '("Inductive definition" . etcs-template-etcs-reln))

(define-key global-map [menu-bar etcs-menu etcs-template define]
   '("New definition" . etcs-template-define))

(define-key global-map [menu-bar etcs-menu etcs-template store-thm]
   '("Store theorem" . etcs-template-store-thm))

(define-key global-map [menu-bar etcs-menu etcs-template sep1]
   '(menu-item "--"))

(define-key global-map [menu-bar etcs-menu etcs-template comment-star]
   '("Comment *" . etcs-template-comment-star))

(define-key global-map [menu-bar etcs-menu etcs-template comment-equal]
   '("Comment =" . etcs-template-comment-equal))

(define-key global-map [menu-bar etcs-menu etcs-template comment-minus]
   '("Comment -" . etcs-template-comment-minus))


;; printing
(define-key
  global-map
  [menu-bar etcs-menu etcs-printing]
  (cons "Printing switches" (make-sparse-keymap "Printing switches")))

(define-key global-map [menu-bar etcs-menu etcs-printing simplifier-trace]
   '("Simplifier trace" . etcs-toggle-simplifier-trace))

(define-key global-map [menu-bar etcs-menu etcs-printing times]
   '("Show times" . etcs-toggle-show-times))

(define-key global-map [menu-bar etcs-menu etcs-printing echo]
   '("Echo commands" . etcs-toggle-echo-commands))

(define-key global-map [menu-bar etcs-menu etcs-printing quiet]
   '("Quiet (hide output except errors)" . etcs-toggle-quietdec))

(define-key
  global-map
  [menu-bar etcs-menu etcs-printing backends]
  (cons "Pretty-printing backends" (make-sparse-keymap "Pretty-printing backends")))

(define-key global-map [menu-bar etcs-menu etcs-printing backends ppreset]
  '("Reset etcs-mode pretty-printing (error recovery)" . etcspp-reset))

(define-key global-map [menu-bar etcs-menu etcs-printing backends sep1]
   '(menu-item "--"))

(define-key global-map [menu-bar etcs-menu etcs-printing backends ppstyles]
  '("Toggle use styles" . etcs-toggle-pp-styles))

(define-key global-map [menu-bar etcs-menu etcs-printing backends ppannotations]
  '("Toggle use annotations" . etcs-toggle-pp-annotations))

(define-key global-map [menu-bar etcs-menu etcs-printing backends pptooltip]
  '("Toggle show tooltips" . etcs-toggle-emacs-tooltips))

(define-key global-map [menu-bar etcs-menu etcs-printing backends sep2]
   '(menu-item "--"))

(define-key global-map [menu-bar etcs-menu etcs-printing backends ppbackend]
  '("Toggle pretty-printing backend" . etcs-toggle-ppbackend))

(define-key global-map [menu-bar etcs-menu etcs-printing unicode]
   '("Unicode" . etcs-toggle-unicode))

(define-key global-map [menu-bar etcs-menu etcs-printing ppcases]
  '("Toggle pretty-printing of cases" . etcs-toggle-pp-cases))

(define-key global-map [menu-bar etcs-menu etcs-printing sep2]
   '(menu-item "--"))


(define-key global-map [menu-bar etcs-menu etcs-printing num-subgoals]
   '("Set no. of shown subgoals" . etcs-toggle-goalstack-num-subgoals))

(define-key global-map [menu-bar etcs-menu etcs-printing num-assums]
   '("Set no. of shown assumptions" . etcs-toggle-goalstack-num-assums))

(define-key global-map [menu-bar etcs-menu etcs-printing print-goal-at-top]
   '("Print goal at top" . etcs-toggle-goalstack-print-goal-at-top))

(define-key global-map [menu-bar etcs-menu etcs-printing goal-fvs]
   '("Show free vars in goal" . etcs-toggle-goalstack-fvs))

(define-key global-map [menu-bar etcs-menu etcs-printing sep1]
   '(menu-item "--"))


(define-key global-map [menu-bar etcs-menu etcs-printing show-assums]
   '("Show assumptions" . etcs-toggle-show-assums))

(define-key global-map [menu-bar etcs-menu etcs-printing show-tags]
   '("Show tags" . etcs-toggle-show-tags))

(define-key global-map [menu-bar etcs-menu etcs-printing show-axioms]
   '("Show axioms" . etcs-toggle-show-axioms))

(define-key global-map [menu-bar etcs-menu etcs-printing show-num-types]
   '("Show numeral types" . etcs-toggle-show-numeral-types))

(define-key global-map [menu-bar etcs-menu etcs-printing show-types-verbosely]
   '("Show types verbosely" . etcs-toggle-show-types-verbosely))

(define-key global-map [menu-bar etcs-menu etcs-printing show-types]
   '("Show types" . etcs-toggle-show-types))





;; ETCS goals
(define-key
  global-map
  [menu-bar etcs-menu etcs-goalstack]
  (cons "Goalstack" (make-sparse-keymap "Goalstack")))


(define-key global-map [menu-bar etcs-menu etcs-goalstack apply-tactic-goaltree]
   '("Apply tactic (goaltree)" . copy-region-as-goaltree-tactic))

(define-key global-map [menu-bar etcs-menu etcs-goalstack new-goaltree]
   '("New goaltree" . etcs-do-goaltree))

(define-key global-map [menu-bar etcs-menu etcs-goalstack sep3]
   '(menu-item "--"))

(define-key global-map [menu-bar etcs-menu etcs-goalstack restart-goal]
   '("Restart goal" . etcs-restart-goal))

(define-key global-map [menu-bar etcs-menu etcs-goalstack drop-all]
   '("Drop all goals" . etcs-drop-all-goals))

(define-key global-map [menu-bar etcs-menu etcs-goalstack drop-goal]
   '("Drop goal" . etcs-drop-goal))

(define-key global-map [menu-bar etcs-menu etcs-goalstack sep1]
   '(menu-item "--"))

(define-key global-map [menu-bar etcs-menu etcs-goalstack print-all]
   '("Print all goals" . etcs-print-all-goals))

(define-key global-map [menu-bar etcs-menu etcs-goalstack print-top]
   '("Print goal" . etcs-print-goal))

(define-key global-map [menu-bar etcs-menu etcs-goalstack sep0]
   '(menu-item "--"))

(define-key global-map [menu-bar etcs-menu etcs-goalstack top-thm]
   '("Name top theorem" . etcs-name-top-theorem))

(define-key global-map [menu-bar etcs-menu etcs-goalstack subgoal-tac]
   '("Subgoal tactic" . etcs-subgoal-tactic))

(define-key global-map [menu-bar etcs-menu etcs-goalstack rotate]
   '("Rotate" . etcs-rotate))

(define-key global-map [menu-bar etcs-menu etcs-goalstack back-up-user]
   '("Restore" . etcs-user-backup))

(define-key global-map [menu-bar etcs-menu etcs-goalstack back-up-save-user]
   '("Save" . etcs-user-save-backup))

(define-key global-map [menu-bar etcs-menu etcs-goalstack back-up]
   '("Back up" . etcs-backup))

(define-key global-map [menu-bar etcs-menu etcs-goalstack apply-tactic]
   '("Apply tactic" . copy-region-as-etcs-tactic))

(define-key global-map [menu-bar etcs-menu etcs-goalstack new-termination-goal]
  '("New termination goal" . etcs-start-termination-proof))

(define-key global-map [menu-bar etcs-menu etcs-goalstack new-goal]
   '("New goal" . etcs-do-goal))



;;process
(define-key
  global-map
  [menu-bar etcs-menu etcs-process]
  (cons "Process" (make-sparse-keymap "Process")))

(define-key global-map [menu-bar etcs-menu etcs-process etcs-scroll-down]
   '("Scroll down" . etcs-scroll-down))

(define-key global-map [menu-bar etcs-menu etcs-process etcs-scroll-up]
   '("Scroll up" . etcs-scroll-up))

(define-key global-map [menu-bar etcs-menu etcs-process etcs-recentre]
   '("Recentre" . etcs-recentre))

(define-key global-map [menu-bar etcs-menu etcs-process sep2]
   '(menu-item "--"))

(define-key global-map [menu-bar etcs-menu etcs-process etcs-send-string]
   '("Send string to ETCS" . interactive-send-string-to-etcs))

(define-key global-map [menu-bar etcs-menu etcs-process etcs-send-region-quietly]
   '("Send region to ETCS - hide non-errors" . copy-region-as-etcs-definition-quietly))

(define-key global-map [menu-bar etcs-menu etcs-process etcs-send-region]
   '("Send region to ETCS" . copy-region-as-etcs-definition))

(define-key global-map [menu-bar etcs-menu etcs-process sep1]
   '(menu-item "--"))

(define-key global-map [menu-bar etcs-menu etcs-process toggle-etcs-bare]
   '(menu-item "Use bare" etcs-toggle-bare
                     :button (:toggle
                              . (and (boundp 'etcs-bare-p)
                                     etcs-bare-p))))

(define-key global-map [menu-bar etcs-menu etcs-process etcs-show-info]
   '("Show ETCS information" . etcs-print-info))

(define-key global-map [menu-bar etcs-menu etcs-process etcs-exe]
   '("Set ETCS executable" . etcs-set-executable))

(define-key global-map [menu-bar etcs-menu etcs-process etcs-kill]
   '("Kill ETCS" . etcs-kill))

(define-key global-map [menu-bar etcs-menu etcs-process etcs-interrupt]
   '("Interrupt ETCS" . etcs-interrupt))

(define-key global-map [menu-bar etcs-menu etcs-process sep02]
   '(menu-item "--"))

(define-key global-map [menu-bar etcs-menu etcs-process etcsmake]
   '("Run Etcsmake" . etcsmake))

(define-key global-map [menu-bar etcs-menu etcs-process sep01]
   '(menu-item "--"))

(define-key global-map [menu-bar etcs-menu etcs-process etcs-display]
   '("Display ETCS buffer" . etcs-display))

(define-key global-map [menu-bar etcs-menu etcs-process etcs-start-vertical]
   '("Start ETCS - vertical split" . etcs-vertical))

(define-key global-map [menu-bar etcs-menu etcs-process etcs-start-horizontal]
   '("Start ETCS - horizontal split" . etcs-horizontal))

(define-key global-map [menu-bar etcs-menu etcs-process etcs-start]
  '("Start ETCS" . etcs))

;; Support for snippet expansion, if yasnippet is installed.
(when (require 'yasnippet nil 'noerror)
  (let ((ETCSsnippets
         (concat
          (string-remove-suffix "/bin/etcs" etcs-executable)
          "/tools/yasnippets" "")))
    (setq yas-snippet-dirs (nconc yas-snippet-dirs (cons ETCSsnippets '())))
    (yas-reload-all)
    (define-key etcs-map (kbd "TAB") 'yas-expand)))

(when (locate-library "company-yasnippet")
  (load-library "company")
  (setq company-backends (cons 'company-yasnippet company-backends)))
