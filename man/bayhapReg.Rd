\name{bayhapReg}
\alias{bayhapReg}
\alias{print.reg}
\title{Bayesian analysis of haplotype association using Markov Chain Monte Carlo}
\description{
             This is the main function of this pachage. This function implements the simultaneous estimation of uncertain haplotype 
             frequencies and the association between haplotypes and quantitative, binary and survival
             traits based on generalized linear models. Prior values for model parameters can be specified by the user. 
             Convergence diagnostics and statistical and graphical analysis of the sampling 
             output must be carried out to ensure the convergence of the chain.

             This function calls an external .c function named \code{mcmc}.

             \code{print} displays tables showing the resulting estimation for the parameters in the MCMC sequence with their standard deviation and probability interval. The argument is an object of class \code{reg}. 

}
            

\usage{
bayhapReg(formula = formula, data, family = "gaussian", 
          t.model = "additive", sep = "/", 
          na.snp.action = "omit", freqmin = 0.01, 
          burn.in.haplo = 10000, burn.in.pheno = 10000, 
          total.iter = 10000, devhaplo = 0.1, dist = 1, 
          lag.number = 10, sign = 0.05, file = FALSE, 
          prior.val = haplo.prior(), verbose = 2)
}

\arguments{
  \item{formula}{An expression of the form response~predictors. Terms of interaction have to be expressed as in the 
   formula style of other regression models (see documentation for \code{\link{formula}}). Variables interacting with      
   haplotypes must be also main effects in the model. Hence, if you use 'haplotypes:a' notation, you are bound to make  
   appear the variable \code{a} in formula as 'response~haplotypes+a+haplotypes:a'. Otherwise you can use the compact form 
   'response~haplotypes+haplotypes*a'. 
   The reference category for all categorical variables in the model is the first value in alphabetical order for 
   character strings and the minor value in case of numerical variables.}
  \item{data}{The data.frame returned from setupData in which rows represent each individual and columns are the variables 
   ocurring in the formula (response, SNPs information and covariates) plus an internal variable called 
\code{haplotypes}.   
   Each SNP in the original data.frame has to be a character string holding both alleles with the
   separator specified by the argument \code{sep}. The word \code{haplotypes} is an internal word, so no variable in the original 
   data.frame can bear this name.}
  \item{family}{One of the three possible models to perform: "gaussian", "binomial" or "survival".}
  \item{t.model}{The type of inheritance model to follow. There are three options: 
  \code{additive}(default), \code{dominant} or \code{recessive}.}
  \item{sep}{Character separator to divide alleles.}
  \item{na.snp.action}{Action to do with genotype missing data. The default value \code{omit} will exclude of the analysis 
   individuals with missing value in at least one SNP.}
  \item{freqmin}{Minimum treshold for the frequency of haplotype which have to be included in the model. Haplotyes with 
   frequency below \code{freqmin} will be collapsed in a new category called \code{rares}. The default value of 0.01 is the 
   minimum accepted.}
  \item{burn.in.haplo}{Number of initial oscilating iterations to be discarded of the markov chain of haplotype 
   frequencies. The default should be modified when convergence fails in the chain.}
  \item{burn.in.pheno}{Number of initial iterations to be discarded of the markov chain for the coefficients of the model.  
   The default should be modified when convergence fails in the chain.}
  \item{total.iter}{Total number of iterations added to burn.in.haplo and burn.in.pheno to compute the total avarage of 
   both chains. The default should be modified when convergence fails for one or both chains.}
  \item{devhaplo}{Deviation used in Random Walk sampling during the generation of the markov chain for haplotype frequency. 
   This value have to be increased when convergence to local minima.}
  \item{dist}{The distribution to sample from to have the value which determines the next step of the random walk sampling. 
   Default value 1 represents the uniform distribution. For normal distribution choose 0.}
  \item{lag.number}{Periodical number of iterations discarded during the avarage period.}
  \item{sign}{Signification used to compute intervals of probability.}
  \item{file}{During the sampling period, a file called "outhaplo.txt" is generated containing all the values of each      
   parameter chain to make the posterior diagnose. If \code{file=TRUE} this file will be keept on your working 
   directory after the execution of the function. Otherwise if file is set as FALSE the file will be removed.}
  \item{prior.val}{ The value returned by haplo.prior. Use it when you want to consider a Bayesian approach. See the help 
   of haplo.prior for more details.}
  \item{verbose}{The three possible levels of showing messages during the function execution: 0 (any message), 1 (some  
   messages) and the default 2 (all possible messages).}
}
\details{To compute frequencies for all possible haplotypes in the sample without collapsing in rare category, run 
\code{bayhapFreq}. This also could be useful to decide the value for \code{freq.min} before running \code{bayhapReg}.

The execution of this function can take several minutes depending on the number of individuals, number of loci and the number of covariates and interactions, so it is recommended setting the verbose argument as 2.

Further diagnose analysis must be done to evaluate the convergence of the method and so, the validity of the results. Plot running mean with \code{plotRmean} to test the stability of the running mean of chain values regards to the burnin and total number of iteration chosen, plot autocorrelations with \code{plotACF} to check the decrease as the chain go forward, plot the density with \code{plotDensity} to check the posterior distribution and plot the trace histories with 
\code{plotTrace} (\code{plotReg} also do all these plots) Finally run \code{conv.test} to check different test of convergence.

The density function for a possible parametrization of the Weibull distribution with 'shape' parameter r and 'scale'
parameter k is given by:

f(t) = kr[(rt)^(k-1)] exp(- (rt)^k) 

For our purposes, these functions have been parametrized. The cumulative distribution function is: 

F(t) = 1 - exp(-(t/b)^a) 

where t is a non-negative value, the mean is E(t) = b Gamma(1 + 1/a), and the Var(t) = b^2 * (Gamma(1 + 2/a) - (Gamma(1 + 1/a))^2). 

If covariates are considered, the density function could be parametrized as follows. Let be z the covariate, and \code{beta}the vector of the regression coefficients. We take $r^k=exp(beta*z)$ and so the density function is:

               f(t)= k exp(zbeta) [t^(k-1)] exp(-(t^k) exp(zbeta))

For this parametrization, the hazard function is:

               h(t)=k exp(zbeta)t^(k-1)

and the survival function is:

               s(t)=exp(-(t^k) exp(zbeta))


Note that before include prior information is necessary to run the \code{bayhapFreq} function to get the labels for each haplotype that occurred in the genotypes sample. From this resulting object of class \code{freq} the haplotype names needed in \code{haplo.prior} function can be extracted. Then, the prior values of the mean of the coefficients for the haplotypes chosen by the user and its standard deviation must be also introduced in \code{haplo.prior} function in the same order of the corresponding haplotype name. It is, for each prior-informated haplotype, its coefficient in the regression model follows a normal distribution: 

               beta_haplotype~N(mean_haplotype,var_haplotype)

If family model is binomial, there are two possible options. You can put prior information for model coefficients (mean and standard deviation) or you can put prior information for the OR, and for the confidence interval and significance of each interval, instead of inform about the coefficients. See the help of \code{haplo.prior} for more specifications about the arguments.

Take care of not put prior information to haplotypes with frequency below the treshold specified in \code{freqmin}. This is not allowed by the program since rares category do not accept prior information.

}  

\value{
  An object of class \code{reg} is returned for print methods. There are some fixed tables and values generated with \code{print.reg} for all models and other tables and values only given for an specific family model or case. 
The next tables and values are always shown by print method:
  \item{Haplotype Frequencies}{Table showing haplotypes, their estimated frequency, the standard error for the estimation and the probability interval.}
  \item{Coefficients}{Table showing estimations of the regression coefficients. For linear and weibull models, estimates of variance and scale parameters are also returned.}
  \item{Formula}{The considered formula.}
  \item{Model}{The function link.}
  \item{BIC}{Bayesian Information Criterion. The lower the value, the better the model fits.}  
In case of binomial family model, one table showing Odds Ratios is added.


If there are interactions in formula and the family is gaussian or binomial then three tables are also added to the output: the cross classification interaction table, the table for haplotypes within covariate, and the table for covariate within haplotypes.
}
\references{Iniesta R and Moreno V (2008) Assessment of Genetic Association using Haplotypes Inferred with Uncertainty via Markov Chain Monte Carlo. Monte Carlo and Quasi-Monte Carlo Methods, Springer Berlin Heidelberg 529-535.}
\author{Raquel Iniesta \email{riniesta@pssjd.org}}

\seealso{\code{\link{setupData}}, \code{\link{bayhapFreq}}, \code{\link{haplo.prior}}, \code{\link{plotReg}}}
\examples{

##quantitative response (linear regression model) with prior values 
##for some haplotype frequencies:

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

covariate<-c(1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1,
1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1,
1, 1, 1, 0, 0, 0, 0, 0, 0)


response.q<-c(-0.3566, 0.4999, 0.9204, 0.8139, 1.8662, -0.4734, -0.7104,
-1.5904, -0.4367, 1.4043, 0.2683, 0.2324, 0.0217, 0.527, -2.2662,
0.1757, 0.378, 0.5139, -0.5167, -0.6913, 0.3385, -0.1095, -1.293,
1.7752, -1.4137, -0.502, -0.2889, -0.9809, -1.2051, -0.4104,
0.1964, -0.5435, 1.7636, 0.6596, 0.767, -0.4716, 1.1389, 0.8475,
-0.0428, 0.5691, 1.4069, -0.7324, 1.8495, -1.4328, 0.8782, -0.2168,
-0.006, 0.0517, 0.5135, 0.7965)                                    

data.orig<-data.frame(snp1,snp2,covariate,response.q)

data<-setupData(data.orig,snps.name=c("snp1","snp2"),sep="/")

#before the execution of bayhapReg, execute bayhapFreq to have labels for each 
#haplotype in the genotypes sample.

res.freq<-bayhapFreq(data=data,na.snp.action="keep",col.snps=1:2,sep="/",
                     total.iter.haplo=10000)

#res.freq, do not execute this!

# Haplotypes snp1 snp2    Freq Std.error     ICL     ICU
#    haplo.1    T    G 0.02473   0.01282 0.00297 0.05328
#    haplo.2    C    A 0.03602   0.01437 0.00624 0.06949
#    haplo.3    T    A 0.00000   0.00001 0.00000 0.00582
#    haplo.4    C    G 0.93924   0.02010 0.89985 0.98457

#From this object of class "freq" haplotype labels can be extracted for hap.prior, 
#and then the prior values of the coefficients for the haplotypes chosen by the user 
#and its standard deviation must be introduced.


#Put the word "haplotypes" in the formula. Model with interaction and with prior 
#information.


res.q<-bayhapReg(formula=response.q~haplotypes+haplotypes*covariate,data=data,
                 family="gaussian",t.model="additive",na.snp.action="keep",
                 freqmin=0.01,burn.in.haplo=5000,burn.in.pheno=5000,
                 total.iter=5000,devhaplo=0.1,dist=1,lag.number=10,
                 sign=0.05,file=TRUE,prior.val=haplo.prior(res=res.freq,
                 haplos.name=c("haplo.1","haplo.2"),coeff=c(1.1,0.8),
                 sd.coeff=c(0.9,0.5)),verbose=2)

}

