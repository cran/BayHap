\name{BIC}
\alias{BIC}

\title{Bayesian Information Criterion}
\description{
 This function computes the Bayesian Information Criterion of a model.
}
\usage{
BIC(res)
}

\arguments{
  \item{res}{An object of class \code{reg} returned by the function \code{bayhapReg}.}
}
\details{
 The Bayesian information criterion (BIC) is a criterion for model selection among a class of parametric models with different numbers of parameters. BIC value is computed through the formula 
 -2 log(L)+klog(n) 
 where L is the maximized value of the likelihood function for the estimated model, k is the number of terms of the markov chain, i.e. the number of free parameters to be estimated (if the estimated model is a linear regression, k is the number of regressors, including the constant) and n is the sample size.
If several models are runned, you can compare them by using the BIC criterion. The lower the BIC value, the better the model fit. 
}
\value{
 The value returned is the BIC value.
}
\author{Raquel Iniesta \email{riniesta@pssjd.org}}


