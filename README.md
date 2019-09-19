# Run

Directly run `./scripts/run.sh YourJavaFile.java` from the root directory of this project.

## Debug tips

- To debug the semantic correctness of the generate predicates, check if for all variables, the guessed invariant can imply the inferred pre-conditions. If not, then either the guessed invariant is wrong, or the inferrence of pre-conditions is wrong.
