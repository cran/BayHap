\name{autocorr}
\alias{autocorr}

\title{Autocorrelation Function}
\description{
  Computes lag autocorrelations for the parameters in an MCMC
  sequence.

}
\usage{
autocorr(x, lag, keep.rares.autocorr = FALSE)
}

\arguments{
  \item{x}{An object of class \code{reg} or \code{freq}.}
  \item{lag}{Numerical vector of lags where autocorrelation must be estimated.}
  \item{keep.rares.autocorr}{Logical TRUE or FALSE indicating whether autocorrelation for rares category must be shown or not.}
}

\value{
   A matrix whose columns and rows contain the estimated
   autocorrelation functions at the specified lags and the monitored
   parameters, respectively.

}

\author{Original version by Brian J. Smith in package Boa. 

Adapted version by Raquel Iniesta \email{riniesta@pssjd.org}}

\seealso{\code{\link{correl}}, \code{\link{plotACF}}}


