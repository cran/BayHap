\name{plotRmean}
\alias{plotRmean}
\title{Plot Running Mean of the Parameter Estimation }
\description{
 Computes and displays the running mean(s) for
     the  specified parameter(s).

}
\usage{
plotRmean(haplo.object, all = TRUE, name.var = " ", 
          keep.rares.rmean = FALSE)
}

\arguments{
  \item{haplo.object}{An object of class \code{reg} or \code{freq}.}
  \item{all}{Logical.The default value TRUE implies to plot the running mean for all the parameters. If FALSE, the vector of names of the desired parameters to plot must be specified in name.var.}
  \item{name.var}{If all=FALSE, this must be a vector containing the names of the chosen parameters to plot their running mean.}
  \item{keep.rares.rmean}{Logical. Indicates if the running mean for rare category must be shown.}
}

\value{
 Graphs of running mean(s).
}

\author{Original version by Brian J. Smith in package Boa. 

Adapted version by Raquel Iniesta \email{riniesta@pssjd.org}.}

