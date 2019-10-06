#!/bin/sh

sbt compile
cd target/scala-2.12/classes
jar -cvf $HOME/Desktop/bc.jar ./
