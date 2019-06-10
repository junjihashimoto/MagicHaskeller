#!/usr/bin/runhaskell

Compile with
ghc -O CGI.lhs -o MagicHaskeller-exp.cgi -package cgi -package mueval -package hint --make -DGHC7

Also, timeout has to be implemented!

\begin{code}
module Main(main) where
import MagicHaskeller.CGI
import Network.CGI
import MagicHaskeller.VersionInfo

main = main' versionInfo runCGI
\end{code}
