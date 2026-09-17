scalaVersion := "3.6.4"

name    := "joern-sdg-exporter"
version := "0.1.0"

val joernVersion = "4.0.131"

libraryDependencies ++= Seq(
  "io.joern" %% "joern-cli"      % joernVersion,
  "io.joern" %% "javasrc2cpg"    % joernVersion,
)

resolvers += "Gradle Libs" at "https://repo.gradle.org/gradle/libs-releases"

// Avoid duplicate-class issues from Joern's fat dependency tree
assembly / assemblyMergeStrategy := {
  case PathList("META-INF", _*) => MergeStrategy.discard
  case _                        => MergeStrategy.first
}
