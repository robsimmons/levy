(require 'generic-x) ;; we need this

(define-generic-mode
      'levy-mode                        ;; name of the mode to create
      '("#")                            ;; comments start with '!!'
      '("if" "then" "else"
        "fun")                          ;; some keywords
      '(("->" . 'font-lock-constant-face)
        (":" . 'font-lock-constant-face)
        ("return" . 'font-lock-builtin-face)
        ("thunk" . 'font-lock-builtin-face)
        ("force" . 'font-lock-builtin-face)
        ("do" . 'font-lock-function-name-face)
        ("let" . 'font-lock-function-name-face)
	)
      '("\\.levy$")                     ;; files for which to activate this mode
       nil                              ;; other functions to call
      "A mode for Levy files"           ;; doc string for this mode
    )
