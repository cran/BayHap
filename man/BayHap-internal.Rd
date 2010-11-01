
\name{BayHap-internal}
\alias{allele}
\alias{allele.names}
\alias{chain.import}
\alias{boa.plot.acf.ad}
\alias{genotype}
\alias{expectedGenotypes}
\alias{haplo.list}
\alias{haplo.list.all}
\alias{haplo.pairs}
\alias{import}
\alias{is.genotype}
\alias{is.locus}
\alias{is.snp}
\alias{make.dummies}
\alias{survival}
\alias{permutations}
\alias{combinations}


\title{Internal BayHap functions}
\description{ 
allele: function from package genetics. Extract the specified allele(s) as a character vector or a 2 column matrix. Author: Gregory R. Warnes
allele.names: function from package genetics: extract the set of allele names. Author: Gregory R. Warnes
chain.import: Read an MCMC sequence from an external file and add it to the session lists of sequences. The original function belongs to the boa package and is named 'boa.chain.import'.
Original version by Brian J. Smith. Adapted version by Raquel Iniesta
boa.plot.acf.ad:Creates a single plot of the lag autocorrelations for a specified parameter. The original function belongs to the boa package and is named 'boa.plot.acf'. Original version by Brian J. Smith. Adapted version by Raquel Iniesta
genotype: function from package genetics: creates a genotype object.
Authors: Gregory R. Warnes and Friedrich Leisch.
expectedGenotypes:from package genetics: constructs expected genotypes according to known allele variants, which can be quite tedious with large number of allele variants. It can handle different level o ploidy.
Author: Gregor Gorjanc
haplo.list: List all the haplotypes compatible with a given genotype.
Author: Raquel Iniesta
haplo.list.all: Lists all the possible haplotypes for a given number of biallelic loci. 
Author: Raquel Iniesta
haplo.pairs: List haplotypes pairs compatible with each genotype of a given sample. Author: Raquel Iniesta
import: Import data from an ASCII text file. The variables and iterations
should appear in the columns and rows, respectively, of the file.
The variable names must be given in the first row. The iteration
numbers are taken from the the column entitled "iter"
(case-sensitive), if it exists; otherwise, the numbers  1..n are
used, where n is the number of rows. The columns may be separated
by white space or tabs. The original function belongs to the boa package and is named 'boa.importASCII'. Original version by Brian J. Smith. Adapted version by Raquel Iniesta
is.genotype: from package genetics: return 'TRUE' if 'x' is of class 'genotype'.    
Authors: Gregory R. Warnes and Friedrich Leisch.
is.locus: from package genetics : test whether an object is a
member of the class 'locus'. Authors: Gregory R. Warnes and Friedrich Leisch.
is.snp: Test if data entered as SNP are adequate to be analized.
Author: Raquel Iniesta
make.dummies: Makes dummies variables for each categorical covariate of the selected model. Author: Raquel Iniesta
survival: Creates the response object needed in formula for the survival model. Author: Raquel Iniesta
permutations and combinations:from package genetics and gtools respectively: Enumerate the possible permutations and combinations of a specified size from the elements of a vector. Original version in the package gtools by Bill Venables. Permutations extended to handle 'repeats.allowed' by Gregory R. Warnes in the package genetics.
}
\usage{
 allele(x, which = c(1, 2))
 allele.names(x)
 chain.import(x, type = "ASCII",keep.rares.chain=FALSE) 
 boa.plot.acf.ad(x, pname, annotate = boa.par("legend")) 
 genotype(a1, a2 = NULL, alleles = NULL, sep = "/", remove.spaces = TRUE, 
    reorder = c("yes", "no", "default", "ascii", "freq"), allow.partial.missing = FALSE, 
    locus = NULL) 
 expectedGenotypes(x, alleles = allele.names(x), ploidy = 2, sort = TRUE, haplotype = FALSE)  
 haplo.list(nlocus,haplo1,haplo2,hetero,nhetero,rows,cols)
 haplo.list.all(nlocus) 
 haplo.pairs(geno)
 import(filename, path = NULL) 
 is.genotype(x)
 is.locus(x)
 make.dummies(covariate)
 survival(time, status)
 permutations(n, r, v = 1:n, set = TRUE, repeats.allowed = FALSE) 
  
}

\details{These functions are not to be called by the user.}
\keyword{internal}
