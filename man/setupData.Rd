\name{setupData}
\alias{setupData}

\title{Check and prepares original data to be analyzed}
\description{
 This function checks if the data set is suitable for the analysis (type and format) and creates a new data frame including some internal variables.
}
\usage{
setupData(data, col.snps = NULL, snps.name = NULL, sep)
}

\arguments{
  \item{data}{A data.frame in which each row represents an individual and columns are the variables 
   ocurring in the formula (response, SNPs information and covariates, see bayhapReg documentation for more details). All  
   columns must be non factors. Each SNP have to be a character string holding both alleles with the
   separator specified by the argument \code{sep}. Data must contain one column for each SNP. No variable in the original data.frame should be called \code{haplotypes} by the 
   user.}
  \item{col.snps}{A numerical vector indicating the position of each SNP in data. This is an optional parameter, instead of this the name of each SNP can be informed in \code{snps.name}.}
  \item{snps.name}{A vector containing the names of each SNP in the data. This is an optional parameter, instead of this the column position of each SNP can be informed in \code{col.snps}.}
  \item{sep}{Character separator to divide alleles.}
}
\details{
  This function must be executed before running \code{bayhapReg}. The resulting data.frame must be the object to pass to \code{bayhapReg} as a data parameter. Original data must not contain any variable named \code{haplotypes} because this is an specific word for this package.
}
\value{
 A data.frame ready to be inserted in \code{bayhapReg}.
}

\author{Raquel Iniesta \email{riniesta@pssjd.org}}

\seealso{\code{\link{bayhapReg}}}

