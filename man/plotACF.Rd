\name{plotACF}
\alias{plotACF}

\title{Plot autocorrelation function}
\description{
  Creates a single plot of the lag autocorrelations for a specified
     parameter.
}
\usage{
plotACF(x, all = TRUE, name.var = " ", keep.rares.acf = FALSE)
}

\arguments{
  \item{x}{An object of class \code{reg} or \code{freq}.}
  \item{all}{Logical.The default value TRUE implies to plot autocorrelation function for all the parameters. If FALSE, the vector of names of the desired parameters to plot must be specified in name.var.}
  \item{name.var}{If all=FALSE, this must be a vector containing the names of the chosen parameters to plot their acf.}
  \item{keep.rares.acf}{Logical. Indicates if acf for estimates of rares category must be shown. }
}
\value{
 Graphs of autocorelation function.
}
\author{Original version by  Brian J. Smith in Boa package. 

Adapted version by Raquel Iniesta \email{riniesta@pssjd.org}}

