#!/bin/sh

# set -x
# ./scripts/run.sh src/test/java/benchmarks/Zuleger2011bound.java
# ./scripts/run.sh src/test/java/benchmarks/BreakParagraphs.java

FILES="$1/*.java"
for f in $FILES
do
  echo "Processing $f ..."
  ./scripts/run.sh "$f"
  echo "\n"
  # take action on each file. $f store current file name
done
