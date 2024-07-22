(defvar apollo-keywords nil "apollo keywords")
(setq xls-keywords '("fn" "if" "else" "return" "trait" "struct" "use" "static" "dyn"))

(defvar apollo-types nil "apollo types")
(setq xls-types '("f1" "f2" "f4" "f8" "i1" "i2" "i4" "i8" "string" "array"))

(defvar apollo-functions nil "apollo functions")
(setq xls-functions '("printf"))

(defvar apollo-fontlock nil "list for font-lock-defaults")
(setq xls-fontlock
      (let (xkeywords-regex xtypes-regex xconstants-regex xevents-regex)

        ;; generate regex for each category of keywords
        (setq xkeywords-regex (regexp-opt apollo-keywords 'words))
        (setq xtypes-regex (regexp-opt apollo-types 'words))
        (setq xfunctions-regex (regexp-opt xls-functions 'words))

        ;; note: order matters, because once colored, that part won't change. In general, put longer words first
        (list (cons xtypes-regex 'font-lock-type-face)
              (cons xfunctions-regex 'font-lock-function-name-face)
              (cons xkeywords-regex 'font-lock-keyword-face))))

;;;###autoload
(define-derived-mode apollo-mode c-mode "apollo mode"
  "Major mode for editing Linden Scripting Language"

  ;; code for syntax highlighting
  (setq font-lock-defaults '((apollo-fontlock))))

(add-to-list 'auto-mode-alist '("\\.apo\\'" . apollo-mode))

;; add the mode to the `features' list
(provide 'xls-mode)

;;; xls-mode.el ends here
