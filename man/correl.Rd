\name{correl}
\alias{correl}

\title{Correlation Matrix}
\description{
     Computes and displays the correlation matrix for the
     parameters  in the MCMC sequence.
}
\usage{
correl(x, keep.rares.correl = FALSE)
}

\arguments{
  \item{x}{An object of class \code{reg} or class \code{freq}.}
  \item{keep.rares.correl}{Logical. TRUE or FALSE indicating whether the correlation must be carried out also for the rares category.}
}

\value{
 The correlation matrix for the parameters in the MCMC sequence.
}

\author{Original version by  Brian J. Smith. Adapted version by Raquel Iniesta \email{riniesta@pssjd.org}}


