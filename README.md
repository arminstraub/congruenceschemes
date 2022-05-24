# congruenceschemes

A [SageMath](https://www.sagemath.org/) package for computing congruence schemes

This package accompanies the paper *On congruence schemes for constant terms and their applications* by Armin Straub [[S22]](#S22).

The basic usage of this package is indicated in Section 4 of that paper.


## Author

- Armin Straub (2021/10): Initial implementation


## Contributions

- The underlying ideas and algorithms for computing congruence schemes were first described by Eric Rowland and Reem Yassawi [[RY15]](#RY15) and extended by Eric Rowland and Doron Zeilberger [[RZ14]](#RZ14).
- As part of his 2019 master's thesis, Joel Henningsen (under the guidance of Armin Straub) implemented a subset of these algorithms in Sage.  The performance and design lessons learned from Joel's work have benefitted the present code.


## References

<a id="RY15">[RY15]</a>
Eric Rowland and Reem Yassawi (2015).
Automatic congruences for diagonals of rational functions.
*Journal de Théorie des Nombres de Bordeaux*, 27(1), 245–288.
[DOI](https://doi.org/10.5802/jtnb.901)

<a id="RZ14">[RZ14]</a>
Eric Rowland and Doron Zeilberger (2014).
A case study in meta-automation: automatic generation of congruence automata for combinatorial sequences.
*Journal of Difference Equations and Applications*, 20(7), 973–988.
[DOI](https://doi.org/10.1080/10236198.2013.876422)

<a id="S22">[S22]</a>
Armin Straub (2022).
On congruence schemes for constant terms and their applications.
*Research in Number Theory*, to appear.
[arXiv:2205.09902](https://arxiv.org/abs/2205.09902)
