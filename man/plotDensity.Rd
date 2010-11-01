\name{plotDensity}
\alias{plotDensity}
\title{Plot Density Functions}
\description{
 Estimates and displays the density function(s) for the  specified parameter(s).
}
\usage{
plotDensity(haplo.object, all = TRUE, name.var = " ", 
            keep.rares.density = FALSE)
}
\arguments{
  \item{haplo.object}{An object of class \code{reg} or \code{freq}.}
  \item{all}{Logical.The default value TRUE implies to plot the density function for all the parameters in the haplo.object.  
   If FALSE, the vector of names of the desired parameters to plot must be specified in name.var.}
  \item{name.var}{If all=FALSE, this must be a vector containing the names of the chosen parameters to plot their density.}
  \item{keep.rares.density}{Logical. Indicates if the density for rare category must be plotted.}
}
\value{
  Graphs of density function.
}

\author{Original version by Brian J. Smith.

Adapted version by Raquel Iniesta \email{riniesta@pssjd.org}}

