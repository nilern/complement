# Complement

Complement is an implementation of Complot, a simple dynamically typed
functional language. Complot is a simplified version of
[Piecewise](https://github.com/nilern/piecewise).

Complement is the subject of my Bachelor's thesis and also exists to get the
Piecewise project unstuck. The idea is to take a simple AST interpreter in the
form of a [CEK machine](http://matt.might.net/articles/cek-machines/) and
replace its features with preprocessing passes, thus gradually turning the
interpreter into a compiler.

At the moment there is a compiler written in Racket (and the
[Nanopass Framework](http://nanopass.org/)) that emits bytecode and a virtual
machine written in Rust that can run the bytecode.

# Syntax Example

(Does not run yet.)

```
@require complot.core._

factorial = {
  n => factorial 1 n;
  acc n | n == 0 => acc;
  acc n => factorial (n * acc) (n - 1)
};

writeln (factorial 5)
```

# Plans

* First it needs to be usable. Various syntax and primitive operations are
  missing and the FFI needs to be finished so that we can get IO and such.
  Error handling and debug info also need a lot of work.
* Self-hosting compiler
* Full Piecewise language with pattern matching, delimited continuations etc.
* Emit native binaries, replace VM with a runtime library.
