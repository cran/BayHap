\name{haplo.prior}
\alias{haplo.prior}

\title{Prior values for model parameters}
\description{
  Function only to be called inside bayhapReg
}
\usage{
haplo.prior(res.freq=NULL,haplos.name=NULL,coeff=NULL,sd.coeff=NULL,
OR=NULL,CI.OR=NULL,sign.OR=NULL)
}

\arguments{
  \item{res.freq}{An object of class \code{freq} returned by \code{bayhapFreq}}
  \item{haplos.name}{Vector containing the name of the haplotypes for which prior values of model coefficient and standard deviation are given by the user.}
  \item{coeff}{Prior values for each model coefficient of the chosen haplotypes. These values must be specified for each haplotype respectively in the same order stated in \code{haplos.name}. An analysis without prior information or with only some haplotypes with prior information is allowed.}
  \item{sd.coeff}{Prior values for each sd of each model coefficient of the chosen haplotypes. These values must be specified for each haplotype respectively in the same order stated in \code{haplos.name}. An analysis without prior information or with only some haplotypes with prior information is allowed.}
  \item{OR}{If the family model is the binomial, this must be a vector of prior OR's for each haplotype name. The order must be the same as in \code{haplos.name}}  
  \item{CI.OR}{If the family model is the binomial and you have prior information for OR values, this must be a matrix with two columns and so many rows as the number of haplotypes with prior information. Each row represents a haplotype. For each haplotype the first column is the lower limit of the confidence interval, and the second column is the upper limit.}
  \item{sign.OR}{In case of a binomial model with \code{OR} and \code{CI.OR} informed, this must be a vector containning each significance used in the computation of each CI.OR.}  
}
\details{
  In order to get the internal haplotype labels assigned by the package, first run \code{bayhapFreq}. This object is also needed in haplo.prior. It is not necessary to put prior values for all haplotypes in the sample, only choose the ones for which you have prior information. For them, the model coefficient and the standard deviaton for the coefficient must be given.
If the family model is the binomial, there are two possible options. You can put prior information for model coefficients (mean and standard deviation) or you can put prior information for the OR, for the confidence interval and significance of each interval, instead of inform about the coefficients.

For a complet example see the help of \code{bayhapReg}.

}
\value{
Internal values only used as a parameter information by the function \code{bayhapReg}.
}

\author{Raquel Iniesta \email{riniesta@pssjd.org}}




