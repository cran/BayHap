\name{BayHap-package}
\alias{BayHap-package}
\alias{BayHap}
\docType{package}
\title{Bayesian analysis of haplotype association using MCMC}
\description{
             The package BayHap implements the simultaneous estimation of uncertain 
             haplotype frequencies and the association with haplotypes based on 
             generalized linear models for quantitative, binary and survival
             traits. Bayesian statistics and Markov Chain Monte Carlo techniques 
             are the theoretical framework for the methods of estimation included 
             in this package. Prior values for model parameters can be specified by 
             the user. Convergence diagnostics and statistical and graphical analysis 
             of the sampling output can be also carried out.
}
\details{

Package: BayHap
Type: Package
Version: 1.0
Date: 2010-11-01
License: GPL (>= 2)

The main function of this package is the \code{bayhapReg} function. Given a sample of genotypes, this function carries out simultaneous estimations of haplotype frequences and estimations of the parameters of a chosen generalized linear model with the haplotype variable as a risk factor. Quantitative, binary and survival traits are handled by this function and modeled through linear regression, logistic regression and weibull regression models. Terms of interaction can be included in these models. Three different inheritance models are alowed in the analysis: \code{additive},\code{dominant} or \code{recessive}.
Bayesian statistics and Markov Chain Monte Carlo techniques are the theoretical framework for the methods of estimation included in this package. Samples of posterior distributions for parameters are generated through Random Walk, Slice Sampler and Gibbs Sampler techniques. To capture the uncertainty of the haplotypical sample, frequencies and model parameters are estimated simultaneously, so at each step of the sampling of model parameters, one pair of haplotypes is also sampled for every individual with uncertain haplotypes using the previous frequencies in the chain. Prior values for these parameters can be also included by the user. Once samples are drawn, convergence diagnostics and statistical and graphical analysis of the sampling output must be carried out to ensure the convergence of the chain.
First of all, users have to run the \code{setupData} function to have the data.frame object prepared to be inserted in \code{bayhapReg}. Look at the examples below, where are considered two snps, one covariate and a quantitative response. In the example is shown a linear regression with an interaction term, with and without prior information. Note that in case of include prior information, before the execution of \code{bayhapReg} is necessary to run the \code{bayhapFreq} function in order to get the labels for each haplotype that occurred in the genotypes sample. From this resulting object of class \code{freq} the haplotype names needed in \code{haplo.prior} function can be extracted. Then, the names of the haplotypes chosen by the user to have prior information, prior values of their model coefficients and its standard deviation must be also introduced in \code{haplo.prior} function, all of them respectively in the same order. Take care of not put prior information to haplotypes with frequency below the treshold specified in \code{freq.min}. This is not allowed by the program since rares category do not accept prior information. 
Beyond all of this, the analysis can be done without prior information. 

Once bayhapReg has been executed use the print method to see the resulting estimations. To evaluate the convergence of the method and so, the validity of the results, further diagnose analysis must be done. Plot running mean \code{plotRmean} to test the stability of the running mean of chain values regards to the burnin and total number of iterations chosen, plot autocorrelations \code{plotACF} to check the decrease as the chain go forward, plot the density \code{plotDensity} to check the posterior distribution, plot the trace histories \code{plotTrace} and execute \code{conv.test} to check different test of convergence. If the chain does not converge, is recommended to perform some tunning as modifying the burnins values and the total number of iterations.
If several models are adjusted, you can choose the better by using the BIC criterion. The lower the BIC value, the better the model fit.  
}
\author{
Raquel Iniesta and Victor Moreno
Maintainer: Raquel Iniesta \email{riniesta@pssjd.org}
}
\references{
Iniesta R and Moreno V (2008) Assessment of Genetic Association using Haplotypes Inferred with Uncertainty via Markov Chain Monte Carlo. Monte Carlo and Quasi-Monte Carlo Methods, Springer Berlin Heidelberg 529-535.
}
\seealso{\code{\link{setupData}}, \code{\link{bayhapFreq}}, \code{\link{bayhapReg}}, \code{\link{haplo.prior}}, \code{\link{print.reg}}, \code{\link{print.freq}}, 
\code{\link{plotACF}}, \code{\link{plotTrace}}, \code{\link{plotDensity}}, \code{\link{plotRmean}}}

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


res.q<-bayhapReg(formula=response.q~haplotypes+haplotypes*covariate,data=data,
                 family="gaussian",t.model="additive",na.snp.action="keep",
                 freqmin=0.01,burn.in.haplo=5000,burn.in.pheno=5000,
                 total.iter=5000,devhaplo=0.1,dist=1,lag.number=10,
                 sign=0.05,file=TRUE,prior.val=haplo.prior(),verbose=2)

print(res.q)

#In case of having prior information, first run bayhapFreq 

res.freq<-bayhapFreq(data=data,na.snp.action="keep",col.snps=1:2,sep="/",
                     total.iter.haplo=5000)

#The next table is the result of bayhapFreq:

#Haplotypes snp1 snp2    Freq Std.error     ICL     ICU
#    haplo.1    T    G 0.02473   0.01282 0.00297 0.05328
#    haplo.2    C    A 0.03602   0.01437 0.00624 0.06949
#    haplo.3    T    A 0.00000   0.00001 0.00000 0.00582
#    haplo.4    C    G 0.93924   0.02010 0.89985 0.98457

#if the user has prior information for haplotypes TG and CA 
#(in a linear model, these are prior values for the differences 
#and the standard deviation), then haplos.names must be "haplo.1" and "haplo.2", 
#as shown in the next call: 

res.q.prior<-bayhapReg(formula=response.q~haplotypes+haplotypes*covariate,data=data,
                       family="gaussian",t.model="additive",na.snp.action="keep",
                       freqmin=0.01,burn.in.haplo=5000,burn.in.pheno=5000,
                       total.iter=5000,devhaplo=0.1,dist=1,lag.number=10,sign=0.05,
                       file=TRUE,prior.val=haplo.prior(res=res.freq,
                       haplos.name=c("haplo.1","haplo.2"), 
                       coeff=c(1.1,0.8),sd.coeff=c(0.9,0.5)),verbose=2)

print(res.q.prior)

#To check the results, run plot functions and:

correl(res.q)
conv.test(res.q)

#To have an indicator of how well the model fits the data

BIC(res.q)

}
