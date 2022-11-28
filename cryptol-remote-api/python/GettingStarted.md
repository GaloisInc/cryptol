1. Run the Cryptol remote API server:

       > cryptol-remote-api http /cryptol

   This starts an HTTP server with the default settings, which means that
   the server can be accessed at `http://localhost:8080/cryptol`


2. Start a Python shell:

       > poetry run python

   This runs a Python shell within an environment set up by
   [poetry](https://python-poetry.org/)


3. Load the `cryptol` library:

       >>> import cryptol

4. Connect to the remote server:

       >>> cry = cryptol.connect(url="http://localhost:8080/cryptol", reset_server=True)

   The URL is the one where we started the server in step 1.
   The second parameter resets the state of the server.
   See `help("cryptol.connect")` for other options.
   At this point, `cry` is an object that we can use to interact with Cryptol.

5. Load the standard library:

       >>> cry.load_module("Cryptol")

   The `load_module` method is similar to the `:module` command of the
   Cryptol REPL---it loads a module to the server's state.
   The module `Cryptol` is the standard library for Cryptol.

6. Evaluate an expression:

       >>> it = cry.evaluate_expression("1+1")

   This command sends the expression `1 + 1` to the server,
   and the value `it` contains the response.   Use the `result` method
   to get the result, if the expression was evaluated successfully:

       >>> it.result()
       2

7. Get information about the functions and values loaded in the serer:

       >>> names = cry.names().result()

   The result is a list of all loaded names.  Here is an example of getting
   information about the first name that was returned:

       >>> first = names[0]
       >>> first["name"]
       '(!)'
       >>> first["type string"]
       '{n, a, ix} (fin n, Integral ix) => [n]a -> ix -> a'
       >>> print(first["documentation"])
       Reverse index operator.  The first argument is a finite sequence.  The second
       argument is the zero-based index of the element to select, starting from the
       end of the sequence.


