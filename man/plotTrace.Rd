\name{plotTrace}
\alias{plotTrace}

\title{Plot Trace Histories}
\description{
  Displays the trace histories for the specified
     parameter(s).
}
\usage{
plotTrace(haplo.object, all = TRUE, name.var = " ", 
          keep.rares.trace = FALSE)
}

\arguments{
  \item{haplo.object}{An object of class \code{reg} or \code{freq}.}
  \item{all}{Logical. The default value TRUE implies to plot the trace for all the parameters. If FALSE, the vector of names of the desired parameters to plot must be specified in \code{name.var}.}
  \item{name.var}{If all=FALSE, specify here a vector containing the names of the chosen parameters to plot their trace.}
  \item{keep.rares.trace}{Logical. Indicates if the trace for rare category must be shown.}
}

\value{
Graphs of trace histories.
}

\author{Original version by Brian J. Smith in package Boa. 

Adapted version by Raquel Iniesta \email{riniesta@pssjd.org}}

