#!/bin/sh

# Usage: org.checkerframework.dataflow.cfg.JavaSource2CFGDOT
# - Parameters: <inputfile> <outputdir> [-method <name>] [-class <name>] [-pdf]

java -cp ./lib/checker-framework-2.11.0/checker/dist/checker.jar -Xbootclasspath/p:./lib/checker-framework-2.11.0/checker/distjavac.jar org.checkerframework.dataflow.cfg.JavaSource2CFGDOT $1 $2 -method $3 -class $4 -pdf

# Reference: https://www.bountysource.com/issues/41607324-location-should-use-runtime-path-when-used-in-jvm_flags-attribute