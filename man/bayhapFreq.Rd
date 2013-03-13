\name{bayhapFreq}
\alias{bayhapFreq}
\alias{print.freq}
\title{Estimation of haplotype frequencies}
\description{
             This function performs the estimation of uncertain haplotype 
             frequencies. Bayesian statistics and Markov Chain Monte Carlo techniques 
             are the theoretical framework for the method implemented in this function. 
             A random walk sampling draws the posterior distribution for haplotype frequencies. 
             Convergence diagnostics and statistical and graphical analysis of the sampling 
             output must be carried out.
             
             This function calls an external .c function named \code{mcmc}.
             
             
             \code{print} displays tables showing the resulting estimation for the parameters in the MCMC 
             sequence with their standard deviation and credibility interval. The argument of this function 
             is an object of class \code{freq}.
}
\usage{
bayhapFreq(data, na.snp.action = "omit", snps.name = NULL, 
           col.snps = NULL, sep = "/", total.iter.haplo = 10000, 
           devhaplo = 0.1, dist = 1, lag.number = 10, 
           sign = 0.05, file = FALSE, verbose = 2)
}
\arguments{
  \item{data}{A data.frame in which rows represent each individual and each SNP is represented by a column. For each   
   individual, SNPs have to be a character string holding both alleles with the
   separator specified by the argument \code{sep}.}
  \item{na.snp.action}{Action to do with genotype missing data. The default value \code{omit} will exclude of the analysis individuals with missing value in at least one SNP.}
  \item{snps.name}{A character vector with data columns names for SNPs. If this value is the default NULL, col.snps must be reported.}
  \item{col.snps}{A numerical vector indicating the positions of the columns in data where SNPs are stored. If this value is the default NULL, snps.name must be reported.}
  \item{sep}{Character separator to divide alleles.}
  \item{total.iter.haplo}{Total number of iterations used to compute the total avarage of the chain. The default should be modified when convergence fails.}
  \item{devhaplo}{Deviation used in random walk sampling during the generation of the markov chain for haplotype frequency.
   This value have to be increased when convergence to local minima.}
  \item{dist}{The distribution to sample from to have the value which determines the next step of the random walk sampling. 
   Default value 1 represents the uniform distribution. For normal distribution choose 0.}
  \item{lag.number}{Periodical number of iterations discarded during the avarage period.}
  \item{sign}{Probability used to compute credibility intervals.}
  \item{file}{During the sampling period, a file called "outhaplo*.txt" is generated containing all values of each      
   parameter chain to let the user make the posterior diagnose. If file=TRUE this file will be keept on your working directory after the use of this function. Otherwise if file is set as FALSE the file will be removed when execution finishes.}
  \item{verbose}{There are three levels of showing messages during the function execution: 0 (any message), 1 (some messages) and the default 2 (all possible messages). }
 
}
\details{
 Run \code{bayhapFreq} to compute frequencies for all possible haplotypes in the sample without collapsing in rare category. This could be useful to decide the value for \code{freq.min} needed as an argument in \code{bayhapReg}.

The execution of this function can take several minutes depending on the number of individuals and the number of loci, so it is recommended setting the verbose argument as 2. 

Further diagnose analysis must be done to evaluate the convergence of the method and so, the validity of the results. Plot running mean with \code{plotRmean} to test the stability of the running mean of chain values regards to the burnin and total number of iteration chosen, plot autocorrelation with \code{plotACF} to check how it decreases as the chain go forward, plot the density with \code{plotDensity} to check the posterior distribution, plot the trace histories \code{plotTrace} and run \code{conv.test} to check different test of convergence.
}
\value{
  The object of class \code{freq} returned is used for print methods. Print shows a table with lables for each haplotype, the estimated frequency, the standard error of these estimations and the credibility interval with the signification specified in sign.
}
\references{Iniesta R and Moreno V (2008) Assessment of Genetic Association using Haplotypes Inferred with Uncertainty via Markov Chain Monte Carlo. Monte Carlo and Quasi-Monte Carlo Methods, Springer Berlin Heidelberg 529-535.}
\author{Raquel Iniesta \email{riniesta@pssjd.org}}

\examples{
snp1<-c("C/C", "C/C", "C/C", "C/C", "C/C", "C/C", "C/C", "C/C",
"C/C","C/T", "C/C", "C/C", "C/C", "C/C", "C/C", "C/C", "C/C", 
"C/C","C/C", "C/C", "C/C", "C/T", "C/C", "C/C", "C/C", "C/C", 
"C/C","C/C", "C/C", "C/C", "C/C", "C/C", "C/C", "C/C", "C/C", 
"C/C","C/C", "C/C", "C/C", "C/C", "C/C", "C/C", "C/C", "C/C", 
"C/C","C/C", "C/C", "C/C", "C/C", "C/C")

snp2<-c("G/G", "G/G", "G/G", "G/G", "G/G", "G/G", "G/G", "G/G",
"G/G","G/G", "G/G", "G/G", "G/G", "A/G", "G/G", "G/G", "G/G", 
"G/G","G/G", "G/G", "G/G", "G/G", "G/G", "G/G", "A/G", "G/G", 
"G/G","G/G", "G/G", "G/G", "G/G", "G/G", "A/G", "G/G", "G/G", 
"G/G","G/G", "G/G", "G/G", "G/G", "G/G", "G/G", "G/G", "G/G", 
"G/G","G/G", "G/G", "G/G", "G/G", "G/G")

data<-data.frame(snp1,snp2)

res.freq<-bayhapFreq(data=data,na.snp.action="keep",col.snps=1:2,
                     sep="/",total.iter.haplo=5000)

print(res.freq)
}

