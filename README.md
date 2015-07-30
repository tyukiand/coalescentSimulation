# Coalescent simulation

This simulation demonstrates that the Kingman's coalescent 
(a basic model used in population genetics) is applicable
to situations where the pedigree is fixed, and the 
randomness is present only in the mechanism of Mendelian
inheritance. The program generates random pedigrees, and
then samples multiple coalescents in those fixed pedigrees.

Multiple genome and family structures are supported
(monogamous families of haploid individuals, monogamous 
families of diploid individuals, polygynous families of
diploid individuals, eusocial insect colonies).

The software is implemented as a stand-alone script in 
Scala, and can be started as follows:

    scala coalescentSimulation.scala --help

Consult the comments and the help to find out how to 
run experiments and what options are available.
