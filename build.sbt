name := "type-precise-bound-impl"

version := "0.1"

scalaVersion := "2.12.8"

// https://mvnrepository.com/artifact/org.checkerframework/checker
libraryDependencies += "org.checkerframework" % "checker" % "2.11.0"

libraryDependencies += "org.scalactic" %% "scalactic" % "3.0.8"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.8" % "test"

// https://mvnrepository.com/artifact/org.jgrapht/jgrapht-core
libraryDependencies += "org.jgrapht" % "jgrapht-core" % "1.3.1"

// https://mvnrepository.com/artifact/org.jgrapht/jgrapht-io
libraryDependencies += "org.jgrapht" % "jgrapht-io" % "1.3.1"
