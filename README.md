# Run

Directly run `./scripts/run.sh YourJavaFile.java` from the root directory of this project.

## Debug tips

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