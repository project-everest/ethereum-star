This document sets some sensible coding conventions for F* files in
this project. The goal is to make the code easier to read, browse, and
in line with established F* practices. 


* General editing

- Use Unix LF line endings as opposed to Windows CRLF.

- Don't use Unicode symbols. Restrict symbols to the ASCII subset an
rely on editor support (e.g. Emacs fstar-mode) for prettifying input.

- Try to wrap lines at 80 characters.

- Do not use TAB, use spaces. 
The `ws-butler` Emacs package is your friend:
```
(require 'ws-butler)
(add-hook 'fstar-mode-hook 'ws-butler-mode)
```

- Indent 2 spaces.


* Module names, namespaces, abbreviations

- Use upper CamelCase for module names: `TypeChecker`, not `Type_checker`.
This avoids confusion when extracting code to OCaml, where a dot in a
compound module name is extracted to an underscore.

- Use namespaces: modules in this project should use the `Tezos.`
prefix to avoid name clashes with modules from other projects. Use
second-level namespaces when appropriate.

- Choose names that accurately describe the contents of a
module. E.g. `Tezos.Definitions` is probably too general,
`Tezos.Types` is more precise, but the module could probably be split
in two: `Tezos.Types` and `Tezos.Prims` for things like `compare_int`.

- Try not to open and abbreviate a module at the same time. 
This is sometimes unavoidable when opening a pervasively used module that
contains an identifier that clashes with an existing identifier. Consider
renaming one of the clashing identifiers if this happens.


* Identifier names

- When it makes sense, try to match names in Tezos' codebase.

- Use underscores to separate words, e.g. `parse_instr`.

- Only capitalize the first word in constructors, e.g. `Const_int`.


* Declarations and definitions

- When possible, write a `val` declaration for every top-level definition.

- Write all arguments to declarations after `:`, e.g. 
`val f : x:a -> y:b{p x y}` vs. `val f (x:a) : y:b{p x y}`

- Do not add unnecessary parentheses, effect annotations or argument
names in declarations. E.g. `val f : a -> y:b -> z:c{p y z}` vs.  
`val f : (x:a) -> (y:b) -> Tot (z:c{p y z})`.  

- The default effect is `Tot`, so unless a `decreases` clause is
needed do not explicitly write it.

- Do not leave a space between a name and `:`.

- Do not add an unnecessary result `Type` in type definitions

- Do not repeat type annotations in definitions when there is a `val`
declaration.

- Do match argument names given in declarations and definitions.

- Choose meaningful names for constructor arguments in inductive
definitions; F* names the generated projector functions after them.


* Pattern-matching

- Use the wildcard pattern `_` as much as possible. Do not introduce
pattern variables if they aren't used.

- Do not use `when` clauses; they aren't supported in verification;
use explicit conditionals.

- Align pipes `|` with the `m` in `match`.

- When a case spans more than one line, break the line after `->`

- For readability, consider adding blank lines between cases in
complex `match` expressions.


* Blocks

- Prefer `begin`, `end` to parentheses.


* Comments

- Use fsdoc-style comments (beginning with `(**` and preceeding the
construct they apply to). For standalone comments, use
reStructuredText comments (`///`), which typeset nicely in Emacs mode.

- Do add a top-level fsdoc comment before the `module` keyword to 
summarize the module contents.

- Document design choices forced upon you by limitations of F*.

- Enclose code in comments between `[`, `]`

- Prefix technical, transient comments with initials.


* Code structure

- Do not intersperse code and examples. Put examples in separate files
and in a different namespace, e.g. `Tezos.Example.`.

- Keep modules small and focused. Try not to implement two conceptually
separate functionalities in the same module.

- Open all modules at the beginning of a file, before any declaration
or definition.

- Do not open modules that aren't used.


* Proofs

- Prefer a focused assume clause `assume p` to a blanket `admit()`.

- Try not to leave `~>` arrows in checked-in files. These are hard to
distinguish from `->`.

- The `val` discipline also applies to `Lemmas`: write declarations
for lemmas and write all arguments after `:`.

- Try to set `fuel` and `ifuel` aggresively on a per-module basis.
Remember that F* will re-try queries with differnt `ifuel, fuel`
parameters before failing, so setting tighter parameters makes failing
proof attempts fail faster (and successful proofs succeed faster).

- Do not set `--z3rlimit` so aggresively that proofs fail randomly,

- Do check in hint files for stable proofs (hints are recorded with
`--record_hints`).

