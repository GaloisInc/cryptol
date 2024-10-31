;; -*- mode: Lisp; lexical-binding: t; -*-

(defvar cryptol-mode-hook nil)

(defvar cryptol-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\C-j" 'newline-and-indent)
    map)
  "Keymap for Cryptol major mode")

(defvar cryptol-keywords
  '("import" "include"
    "module" "private"
    "infixl" "infixr" "infix"
    "submodule" "interface" "foreign"
    "newtype" "type" "primitive" "parameter"
    "constraint" "property"
    "if" "then" "else"
    "where" "let"
    "pragma"
    "down"
    "by"
    ))

(defvar cryptol-types
  '("Prop"
    "Bit" "Bool" "Word" "Char" "String" "Integer" "Z" "Rational"
    "inf"
    "Literal" "FLiteral" "LiteralLessThan"
    "Zero" "Logic" "Ring" "Integral" "Field" "Round" "Eq" "Cmp" "SigneCmp"
    "fin" "prime" "width" "lg2"
    ))

(defvar cryptol-constants
  '("False" "True" "zero"
    ))

(defvar cryptol-builtins
  '("min" "max" "abs"
    "length"
    "complement" "negate"
    "fromInteger" "toInteger" "toSignedInteger" "fromZ"
    "recip"
    "error" "undefined" "assert"
    "ceiling" "floor" "trunc" "roundAway" "roundToEven"
    "carry" "scarry" "sborrow" "zext" "sext" "ratio"
    "splitAt" "join" "split" "groupBy"
    "reverse" "transpose" "take" "drop"
    "head" "tail" "last"
    "update" "updates" "updateEnd" "updatesEnd"
    "generate"
    "sort" "sortBy"
    "pmult" "pdiv" "pmod"
    "parmap"
    "deepseq" "rnf"
    "random" "trace" "traceVal"
    "and" "or" "all" "any"
    "map" "foldl" "foldr" "sum" "product" "scanl" "scanr" "elem"
    "repeat" "iterate"
    "zip" "zipWith"
    "curry" "uncurry"

    ;; "!" "!!" "@" "@@"
    ;; "+" "-" "*" "/" "%" "^" "/^" "/." "/$" "%$" "^^"
    ;; ">" "<" "!=" ">=" "<=" "<$" ">$" "<=$" ">=$" "!=="
    ;; ">>" ">>$" "<<" ">>>" "<<<"
    ;; "#"
    ;; "&&" "||" "\\/" "/\\"
    ;; "," "`" ".." "..." ":" "(" ")" "{" "}" "[" "|" "]" "=" "<-"
    ;; "==" "===" "==>"
    ))

(defvar cryptol-font-lock-defaults
  `(
    ( ,(regexp-opt cryptol-keywords 'words) . font-lock-keyword-face)
    ( ,(regexp-opt cryptol-types 'words) . font-lock-type-face)
    ( ,(regexp-opt cryptol-constants 'words) . font-lock-constant-face)
    ( ,(regexp-opt cryptol-builtins 'symbols) . font-lock-builtin-face)
    ;; n.b. haskell-mode might be a basis for specifying
    ;; font-lock-function-name-face and font-lock-variable-name-face matchers,
    ;; but those are quite complicated in haskell-mode!
    ))

(defvar cryptol-mode-syntax-table
  (let ((table (make-syntax-table)))
    ;; start of 2-char comment seq (/*), may also be second char of a two char
    ;; comment sequence (//), and may be the end of a 2-char comment seq (*/)
    (modify-syntax-entry ?/ ". 124b" table)
    ;; second char of 2-char comment sequence (/*), or start of a 2 char comment
    ;; end sequence (*/)
    (modify-syntax-entry ?* ". 23" table)
    ;; newline ends a b-style comment
    (modify-syntax-entry ?\n "> b" table)
    table)
  "Syntax table for cryptol mode.")

(define-derived-mode cryptol-mode prog-mode "cryptol"
  "Major mode for editing Cryptol specification files"
  :group 'cryptol-mode
  :syntax-table cryptol-mode-syntax-table
  :abbrev-table (make-abbrev-table)

  (setq font-lock-defaults '(cryptol-font-lock-defaults))

  ;; Indenting of comments
  (setq-local comment-start "// ")
  (setq-local comment-end "")
  ; (setq-local comment-start-skip "\\(^\\|\\s-\\);?#+  ")
  (setq-local comment-multi-line t)

  ;; Filling of comments
  (setq-local adaptive-fill-mode t)
  (setq-local paragraph-start "[ \t]*\\(//+\\|\\**\\)[ \t]*$\\|^^L")
  (setq-local paragraph-separate paragraph-start)
  )

(add-to-list 'auto-mode-alist '("\\.cry\\'" . cryptol-mode))

(provide 'cryptol-mode)
