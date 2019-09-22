#!/bin/sh

# Pre-condition before running this script
# - Using javac to compile the target project will not have compiler errors
# - This script is executed from the root directory of this project via `./scripts/run.sh`

PWD=$(pwd)

lib="$PWD/lib"

# ==========================Please configure the following paths============================
# scala_lib="$HOME/.sbt/preloaded/org.scala-lang/scala-library/2.12.7/jars/scala-library.jar"
scala_lib="$HOME/.ivy2/cache/org.scala-lang/scala-library/jars/scala-library-2.12.8.jar"
scala_reflect="$HOME/.ivy2/cache/org.scala-lang/scala-reflect/jars/scala-reflect-2.12.8.jar"
jgrapht_core_lib="$HOME/.ivy2/cache/org.jgrapht/jgrapht-core/jars/jgrapht-core-1.3.1.jar"
jheap_lib="$HOME/.ivy2/cache/org.jheaps/jheaps/jars/jheaps-0.10.jar"
jgrapht_io_lib="$HOME/.ivy2/cache/org.jgrapht/jgrapht-io/jars/jgrapht-io-1.3.1.jar"
# ==========================================================================================

tool_jar="$HOME/Desktop/bc.jar"
# target_project_lib=`python $PWD/scripts/findlibs.py "$1"` # absolute path
src_dir="$1" # absolute path

checker_framework_bin="$lib/checker-framework-2.11.0/checker/bin"
export PATH=$checker_framework_bin:$PATH # To override the default `javac` with file `javac` in the above directory
export LD_LIBRARY_PATH=$lib:$LD_LIBRARY_PATH
export DYLD_LIBRARY_PATH=$lib:$DYLD_LIBRARY_PATH

rm -rf output/
mkdir output/

# set -x
classpath=".:$lib/com.microsoft.z3.jar:$scala_lib:$tool_jar:$jgrapht_core_lib:$jgrapht_io_lib:$jheap_lib"
time javac -Xmaxwarns 10000 -Xmaxerrs 10000 -cp $classpath -processor boundchecker.BoundChecker `find $src_dir -name "*.java"` -d output/