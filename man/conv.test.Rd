\name{conv.test}
\alias{conv.test}
\title{Heidelberger and Welch Convergence Diagnostics
}
\description{
   Computes the Heidleberger and Welch convergence diagnostics for
   the parameters in an MCMC sequence.
}
\usage{
conv.test(x, alpha = 0.05, error = 1e-05, keep.rares.conv = FALSE)
}
\arguments{
  \item{x}{An object of class \code{reg} or class \code{freq}.}
  \item{alpha}{Alpha level for the confidence in the sample mean of the
          retained iterations.}
  \item{error}{Accuracy of the posterior estimates for the parameters.}
  \item{keep.rares.conv}{Logical. TRUE or FALSE indicating whether the diagnostic of convergence must be carried out also for the rares category.}
}
\details{Take care when setting keep.rares.conv as TRUE. The chain for this parameter tends to be unstable and could lead to an error.}
\value{
  A matrix whose columns and rows are the Heidleberger and Welch
     convergence diagnostics (i.e. stationarity test, number of
     iterations to keep and to drop, Cramer-von-Mises statistic,
     halfwidth test, mean, and halfwidth) and the monitored parameters,
     respectively.
}
\references{ Heidelberger, P. and Welch, P. (1983). Simulation run length
     control in the presence of an initial transient. Operations
     Research, 31, 1109-44.
}
\author{Original version by Brian J. Smith, Nicky Best, Kate Cowles in Boa Package. Adapted version by Raquel Iniesta \email{riniesta@pssjd.org}}


