# About

This is the repo of the tool for static resource bound verification.

# Usage

## Annotate `*.java` files

Annotate `*.java` files with resource variables that track the amount of resource increments and decrements

1. Initialize resource variables with statement `int R = 0`.
    - Note that resource variables' names must start with `R`.
2. Use statement `R = R + e` to denote that the amount of resource consumption is the value of expression `e` when reaching this control location.
    - Note that these increments/decrements must be at the end of a basic block (as opposed to being in the middle).

Annotate the bound expressions to verify

- Use statement `assert(e) : "bound"` to denote that the bound expression to verify is `e`.
    - E.g. we may use `assert(R<n) : "bound"` to denote that the bound expression to verify is `R<n`.
- Each program may have more than 1 bound expressions to be verified.

A user may provide additional global invariants that can help the tool to verify bounds. The tool will not check the validity of these extra invariants.

- Use statement `assert(e): "global"`.

### Notes

- Please do not use any method calls in `*.java` files.
    - Otherwise the generated control flow graphs will have edges pointing to exception handling blocks, causing the tool to crash.
- Please do not use prefix or post increment/decrement statements such as `i++` or `--i`.

## Run

Directly run `./scripts/run.sh YourJavaFile.java` from the root directory of this project.

# Debug tips

- To debug the semantic correctness of the generate predicates, check if for all variables, the guessed invariant can imply the inferred pre-conditions. If not, then either the guessed invariant is wrong, or the inferrence of pre-conditions is wrong. E.g.
```
(assert
  (forall ((i Int) (n Int) (b Bool))
    (=>
      true
      true
  )
)
(check-sat)
; (get-model)

```
- To debug the semantic correctness of the generated predicates, analyze the WLPs in the form of high-level predicates, as opposed to SMTLIB2 outputs (which are extremely hard to read). E.g. think about what loop invariants might be needed to verify a predicate is valid.