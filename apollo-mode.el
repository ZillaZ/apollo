;; package --- apollo-mode
;;; Commentary:
;;; Nothing here
;;; Code:
(defvar apollo-varname nil "Apollo varname.")
(setq apollo-varname "\\(\\w\\|_\\)+[[:space:]]*\\(=\\|:\\)")

(defvar apollo-module nil "Apollo module name.")
(setq apollo-module "\\(static\\|dyn\\)[[:space:]]+\\(\\w\\|_\\)+")

(defvar apollo-import nil "Apollo import.")
(setq apollo-import "::\\(\\w\\|_\\)+")

(defvar cap-test nil "Test.")
(setq cap-test "[A-Z]")
(setq cap-test (capitalize cap-test))

(defvar apollo-imported nil "Apollo imported.")
(setq apollo-imported "::{\\([[:space:]]*\\(\\w\\|_\\)+\/\\(\\w\\|_\\)+[[:space:]]*\\)+}\\|\\(?:::\\)\\(\\w\\|_\\)+\n")

(defvar apollo-keywords nil "Apollo keywords.")
(setq apollo-keywords '("match" "impl" "as" "extern" "new" "link" "with" "fn" "if" "else" "return" "trait" "struct" "use" "let" "enum" "for" "while"))

(defvar apollo-types nil "Apollo types.")
(setq apollo-types '("f1" "f2" "f4" "f8" "i1" "i2" "i4" "i8" "ui1" "ui2" "ui4" "ui8" "ui16" "char" "string" "array" "bool"))

(defvar apollo-custom-types nil "Apollo return types.")
(setq apollo-custom-types (concat cap-test "\\w+"))

(defvar apollo-functions nil "Apollo functions.")
(setq apollo-functions "\\(\\w\\|_\\)+[[:space:]]*\(\\|\)")

(defvar apollo-fontlock nil "List for \"font-lock-defaults\".")
(setq apollo-fontlock
      (let (xmodule-regex xkeywords-regex xtypes-regex xfunctions-regex xvarname-regex xreturn-regex ximport-regex ximported-regex)

        (setq xmodule-regex apollo-module)
        (setq ximported-regex apollo-imported)
        (setq ximport-regex apollo-import)
        (setq xreturn-regex apollo-custom-types)
        (setq xvarname-regex apollo-varname)
        (setq xkeywords-regex (regexp-opt apollo-keywords 'words))
        (setq xtypes-regex (regexp-opt apollo-types 'words))
        (setq xfunctions-regex apollo-functions)

        (list
         (cons xmodule-regex 'font-lock-constant-face)
         (cons ximported-regex 'font-lock-builtin-face)
         (cons xtypes-regex 'font-lock-type-face)
         (cons xfunctions-regex 'font-lock-function-name-face)
         (cons xkeywords-regex 'font-lock-keyword-face)
         (cons xreturn-regex 'font-lock-type-face)
         (cons ximport-regex 'font-lock-constant-face)
         (cons xvarname-regex 'font-lock-variable-name-face))))

;;;###autoload
(define-derived-mode apollo-mode go-mode "apollo-mode"
  "Major mode for editing the Apollo Programming Language."

  ;; code for syntax highlighting
  (setq font-lock-defaults '((apollo-fontlock))))

(add-to-list 'auto-mode-alist '("\\.apo\\'" . apollo-mode))

;; add the mode to the `features' list
(provide 'apollo-mode)

;;; apollo-mode.el ends here
