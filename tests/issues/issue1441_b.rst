This is an RTS document.  Here is some code:

.. code-block:: cryptol

  f1 = 0x01

Now we are back to text.  Here is some more code, this one with options:

.. code-block:: cryptol
  :linenos:

  f2 = 0x02

Back to text.  Now two code blocks together:

.. code-block:: cryptol

  f3 = 0x03
.. code-block:: cryptol
  :linenos:

  f4 = 0x4

Now we are going to make an error and we want to get the correct location:

.. code-block:: cryptol

  f5 = 0x1 + 0x02
