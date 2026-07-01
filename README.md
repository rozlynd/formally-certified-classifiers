# Formally Certified Classifier Explainers

This is a certified program producing explanations for the decisions of AI classifiers.  The algorithms are implemented in the Coq proof assistant and then extracted to OCaml.

### Features

The program takes as input an _explanation problem_ and can output _abductive_ or _contrastive explanations_ (AXp, CXp).

An explanation problem is a certain classifier with a certain input, leading to a particular decision. Roughly speaking, an _AXp_ is a set of features that determines the decision if the corresponding values are fixed in the input. A _CXp_ is a set of features that can be acted upon to change the decision. The formal definitions for AXp and CXp can be found at the end of this document.

_This project is a work in progress._ We support the following models of classifiers and kinds of explanation extraction:

| Classifier | Extract One _AXp_ | Extract One _CXp_ | Extract All |
|:-----------|:-----------------:|:-----------------:|:-----------:|
| Decision Trees | ✅ | ✅ | ❌ |
| Random Forests | ❌ | ❌ | ❌ |
| _Monotonic_* | ❌ | ❌ | ❌ |

(*Monotonic classifiers are classifiers whose underlying function is monotonic; they do not correspond to a particular model and can be black-boxes.)

## Usage

The project has been tested with Coq 8.20 and Dune 3.19.  The Dune project is set up in the subdirectory `ocaml/`.  You can run the commands `dune build` and `dune exec rfxp` from that subdirectory.

You may have to link the Dune project with Coq's kernel, as the extraction to OCaml's primitive `float` type requires it.  Look for the directory `coq-core/` in your installation and check that it contains a `dune` or `dune-package` file.  The easiest way to link this to the project is to set up a symbolic link:
```bash
ln -s -T ~/.opam/myswitch/lib/coq-core ocaml/coq-core
```
You may need to edit the name of the dependency in `ocaml/lib/dune` from `coq-core.kernel` to the library name that is used in the Dune file in `coq-core/`.

The OCaml files extracted from the Coq sources are already present in the Dune project.  If you wish to extract the files again, you can run `make coq-extract` from the root directory.

### Using the Extracted Modules

The extracted code can be found in `ocaml/lib/extracted/`. The intended way to use it is to instantiate various OCaml modules in order to derive an explainer. We describe the important modules.

`Features.mli` contains the following important types:
-   `featureSig` for lists of features---the predefined types `boolean_feature`, `float_feature`, `string_enum_feature` and `enum_feature` can be used to build feature signatures;
-   `featureVec` for vectors, which are list of values with each value living in the domain of the corresponding feature.

`Xp.mli` contains the module type `InputProblem` encapsulating the parameters for an explanation problem:
-   `n` is the number of features;
-   `fs` is the list of all features;
-   `K` is a module encapsulating the type of the classifier's output---_for classifiers that return strings, the implementation `Utils.StringOT` will work;_
-   `t` is the type of classifiers;
-   `eval` is the evaluation function for classifiers;
-   `k` is the particular classifier to consider;
-   `v` is the particular instance to explain;
-   `S` is a implementation of sets over feature indexes---_the simplest is to instantiate this field using the `MakeFinSet` functor on a module containing the parameter `n`._

`Explainers.mli` contains generic signatures for explainers and useful functors:
-   `AXpFinder` contains an `InputProblem` and an AXp-extractor for that problem;
-   `CXpFinder` contains an `InputProblem` and a CXp-extractor for that problem;
-   `WCXpChecker` contains an `InputProblem` and a function deciding for any potential explanation if it is a WCXp or the complement of a WAXp;
-   `AXpIterativeFinder` is a functor for building an `AXpFinder` from a `WCXpChecker`;
-   `CXpIterativeFinder` is a functor for building an `CXpFinder` from a `WCXpChecker`.

`DT.mli` contains the generic type for decision trees and a functor `MakeDT` for building the part of an `InputProblem` corresponding to the feature signature, classifier's output, type and evaluation function.

`DTXp.mli` instantiates/implements some explainer signatures for decision trees:
-   `DTInputProblem` is a specialization of `InputProblem` for decision trees;
-   `DtWCXpChecker` implements a `WCXpChecker` for decision trees;
-   `DtAXpFinder` implements an `AXpFinder` for decision trees;
-   `DtCXpFinder` implements a `CXpFinder` for decision trees.

## Formal Explanability

The following definitions are based on the work of Joao Marques-Silva around abductive and contrastive explanations (see for instance [Logic-Based Explainability: Past, Present & Future](https://arxiv.org/abs/2406.11873)).

Given some _features_ with their specific domains (Boolean, floating-point numbers, enumerations...), the _feature space_ is the product of all domains. A _classifier_ takes as input vectors from the feature space to compute a result.

Given some classifier $k$ and an input vector $x$, we want to derive explanations for the particular decision $k(x)$. An explanation is a set of features $E$ that satisfies a certain logical property. Here are the definitions for _weak abductive explanations_ and _weak contrastive explanation_:

$$
\mathit{weak-}AXp(E) \triangleq \forall y. x \equiv_E y \Rightarrow k(x) = k(y)
$$

$$
\mathit{weak-}CXp(E) \triangleq \exists y. x \equiv_{E^\complement} y \wedge k(x) \neq k(y)
$$

Where $x \equiv_E y$ means the vectors agree on $E$, and $E^\complement$ is the complement of $E$ in the set of all features.

Intuitively, $E$ is a weak AXp if any vector that agrees with $x$ on $E$ leads to the same output. $E$ is a weak CXp if it is possible to change the output only by changing features of $E$ in $x$.

_An AXp is defined as a subset-minimal weak AXp and a CXp is defined as a subset-minimal weak CXp._

By definition, the set of all features is a weak AXp. If $k$ is not constant, the set of all features is a weak CXp. If $k$ is constant then the only AXp is the empty set and there are no CXps.

