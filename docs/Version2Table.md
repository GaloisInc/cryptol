
<!---
Run this through pandoc, then use your favorite PDF editor to "crop" the pdf down to just the table.
This is wacky, but seems to be the best way to get the table to fit in the document margins.
-->

Summary of Changes
------------------

 **Cryptol version 2**        | **Cryptol version 1**            | **Summary**
 ---------------------------- | -------------------------------- |--------
`[ False, True, True ] (==3)` |`[ False True True ] (== 6)`      | Big-endian word representation
`[ 1, 1, 2, 3, 5 ]`           |`[ 1 1 2 3 5 ]`                   | Commas separate sequence entries
`x = 1`                       |`x = 1;`                          | Uses _layout_ instead of `;`'s and `{`'s
`[ x | x <- [1 .. 10] ]`      |`[| x || x <- [ 1 .. 10] |]`      | Cleaner sequence constructor syntax
`f : {a,b} a -> b`            |`f : {a b} a -> b`                | Commas separate type variables
``take`{1} xs``               |`take(1, xs)`                     | First-class type parameters
`x ^^ 2`                      |`x ** 2`                          | `^^` for exponentiation
`<| x^^2 + 1 |>`              |`<| x^2 + 1 |>`                   | Polynomial exponentiation now uniform
`[0 ..]:[_][8]`               |`take(255, [0 ..]:[inf][8])`      | Both produce `[0 .. 255]`
`[0 ...]:[inf][8]`            |`[0 ..]:[inf][8]`                 | Both produce `[0 .. 255]`(repeated)
`[9, 8 .. 0]`                 |`[9 -- 0]`                        | Step defines decreasing sequences
`&&, ||, ^`                   |`&, |, ^`                         | Boolean operator syntax
`(1,2,3).0 (== 1)`            |`project(1,3,(1,2,3)) (==1)`      | Tuple projection syntax (and 0-based)
`property foo xs=...`         |`theorem foo: {xs}. xs==`...      | Properties replace theorems (see below)

