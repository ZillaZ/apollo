
(defvar apollo-varname nil "apollo varname")
(setq apollo-varname "\\(\\w\\|_\\)+[[:space:]]+\\(=\\|:\\)")

(defvar apollo-keywords nil "apollo keywords")
(setq apollo-keywords '("fn" "if" "else" "return" "trait" "struct" "use" "static" "dyn" "let"))

(defvar apollo-types nil "apollo types")
(setq apollo-types '("f1" "f2" "f4" "f8" "i1" "i2" "i4" "i8" "string" "array"))

(defvar apollo-functions nil "apollo functions")
(setq apollo-functions "\\w+[[:space:]]*\(\\|\)")

(defvar apollo-fontlock nil "list for font-lock-defaults")
(setq apollo-fontlock
      (let (xkeywords-regex xtypes-regex xfunctions-regex xvarname-regex)

        (setq xvarname-regex apollo-varname)
        (setq xkeywords-regex (regexp-opt apollo-keywords 'words))
        (setq xtypes-regex (regexp-opt apollo-types 'words))
        (setq xfunctions-regex apollo-functions)

        (list
         (cons xtypes-regex 'font-lock-type-face)
         (cons xfunctions-regex 'font-lock-function-name-face)
         (cons xkeywords-regex 'font-lock-keyword-face)
         (cons xvarname-regex 'font-lock-variable-name-face))))

;;;###autoload
(define-derived-mode apollo-mode c-mode "apollo-mode"
  "Major mode for editing the Apollo Programming Language"

  ;; code for syntax highlighting
  (setq font-lock-defaults '((apollo-fontlock))))

(add-to-list 'auto-mode-alist '("\\.apo\\'" . apollo-mode))

;; add the mode to the `features' list
(provide 'apollo-mode)
