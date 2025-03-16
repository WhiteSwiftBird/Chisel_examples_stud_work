name := "Mux4Task1p1"    
version := "0.1"    
scalaVersion := "2.13.10"    
val chiselVersion = "3.6.0"    
addCompilerPlugin("edu.berkeley.cs" % "chisel3-plugin" % chiselVersion cross CrossVersion.full)    
libraryDependencies += "edu.berkeley.cs" %% "chisel3" % chiselVersion