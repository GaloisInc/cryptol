## Programming Cryptol README

The Programming Cryptol book source code is in `docs/ProgrammingCryptol/`.
It can be built using the `Makefile` in that directory.

There is a pre-built PDF version of the book in this directory. Any updates
to the source code must be accompanied by a corresponding update to the stored
PDF. Developers should build the PDF locally (the default build location
is `docs/ProgrammingCryptol/tmp/Cryptol.pdf`), copy it into this directory,
and rename it to `ProgrammingCryptol.pdf`.

### Other usage notes

To use the check-exercises tool, invoke via `cabal v2-exec
check-exercises --`. This requires the path to the LaTeX file to be
checked, and has options to specify paths to the cryptol executable
and log directories.

To annotate LaTeX files for the `check-exercises` program, we use the
following commands:

* `\begin{replinVerb}` and `\end{replinVerb}`

  This is the markup equivalent of the `Verbatim` environment.
  However, it has the added effect of adding every line of the block
  to a list of commands to be issued to the cryptol REPL.

* `\replin|...|`

  Inline equivalent of `replinVerb` environment. Markup equivalent of
  `\Verb|...|`.

* `\hidereplin|..|`

  Like `\replin|...|`, but is not rendered at all by LaTeX. This is
  for issuing "hidden" input to the REPL that will affect the output
  (like `:set base=10`, for example), but which we don't want to
  include in the PDF.

* `begin{reploutVerb}` and `\end{reploutVerb}`

  This is the markup equivalent of the `Verbatim` environment.
  However, it has the added effect of adding every line of the block
  to the expected output of the preceding `\replin` commands.

* \replout|...|`

  Inline equivalent of `reploutVerb` environment. Markup equivalent of
  `\Verb|...|`.

* `\begin{replPrompt}` and `\end{replPrompt}`

  This is the markup equivalent of the `Verbatim` environment. However, it has
  the added effect of adding every line of the block either to input or expected
  output. If the line starts with the `Cryptol` prompt, it is added to input;
  otherwise, it is added to output.

* `\hidereplout|..|`

  Like `\replout|...|`, but is not rendered at all by LaTeX. This is
  for recording "hidden" output from the REPL that we don't want to
  include in the PDF.

* `\restartrepl`

  This has the effect of terminating the current input/output REPL pair. If
  there is input but no output, then instead of checking the output, the tool
  checks that the input does not raise an error.

  This command is used to divide the REPL input/output pairs into distinct
  "blocks" that get submitted to the REPL independently. Therefore, this command
  should be called every time we are defining a new REPL pair; in particular, it
  should come before every exercise that uses REPL commands.

Other notes:

* I tried to do reasonable things with % comments, but I can't guarantee it will
  work as expected in all cases (particularly with the inline commands). It's
  probably best to avoid using LaTeX comments that are on the same line as any
  of the above commands.

* Lines starting with "Loading module" are silently ignored from the output.

* It would be nice to support writing code to a file, then loading that file
  into the REPL. We don't support this, but it will probably be necessary for
  handling some of the more involved examples (for instance, those that define
  functions).

