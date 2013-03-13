\name{plotFreq}
\alias{plotFreq}


\title{Plot acf, running mean, density functions and trace histories }
\description{
 Displays plots of the autocorrelation function, the running mean, the density functions and the trace histories for the parameter(s) in the MCMC sequence. This function is suitable to plot objects of class \code{freq}.
}
\usage{
plotFreq(res, acf = NULL, d = NULL, rmean = NULL, tr = NULL)
}

\arguments{
  \item{res}{An object of class \code{freq}.}
  \item{acf,d,rmean,tr}{If all these arguments are set to the default NULL, \code{plotFreq} will plot all the graphs (auctocorrelation, density, running mean and trace). To plot only one, two or three graphs, set one, two or three of these arguments as TRUE.}
}
\details{
To plot only one type of graph, you can also use the functions \code{plotACF}, \code{plotRmean}, \code{plotTrace} and \code{plotDensity}.
}


\value{
 Plots of autocorrelation functions, density functions, running mean and trace histories.
}

\author{Original version by  Brian J. Smith. Adapted version by Raquel Iniesta. \email{riniesta@pssjd.org}}
\seealso{\code{\link{plotACF}}, \code{\link{plotTrace}}, \code{\link{plotRmean}}, \code{\link{plotDensity}}}
