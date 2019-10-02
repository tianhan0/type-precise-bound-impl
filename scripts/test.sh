#!/bin/sh

set -x
./scripts/run.sh src/test/java/benchmarks/Zuleger2011bound.java
./scripts/run.sh src/test/java/benchmarks/BreakParagraphs.java
