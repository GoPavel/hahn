# Experiment with KAT

Try to simplify proofs using [relation-algebra](http://perso.ens-lyon.fr/damien.pous/ra/).

## What's new?

Introduced tactics:
- `hahn_kat` - solve KAT
- `hahn_hkat` - solve KAT with Hoare hypotheses

Added utility module:
- [HahnKat.v](https://github.com/GoPavel/hahn/blob/experiments-with-kat/HahnKat.v) contains:
  - instances of Canonical Structures and Typeclasses
  - redefinition of original tactics `kat`/`hkat` from relation-algebra
  - lemmas for lifting hahn's definitions to KAT

TODOs:
- [ ] Examine using `prop_ext` axioms 
- [ ] Examine problem with canonical structures deducing 
- [ ] Code review
- [ ] Add PR to relation-algebra about a bug with excluding alone `pc_c`/`cp_c`.

# Hahn : A Coq library for lists and relations

[![Build Status](https://travis-ci.com/vafeiadis/hahn.svg?branch=master)](https://travis-ci.com/vafeiadis/hahn)

Hahn is a Coq library that contains a useful collection of lemmas and tactics
about lists and binary relations.

- Hahn.v : exports all other files except HahnExtraNotation.v
- HahnAcyclic.v : proving acyclicity of relations
- HahnBase.v : basic tactics used throughout the development
- HahnDom.v : (co)domain of a relation
- HahnEquational.v : relational equivalences
- HahnExtraNotation.v : notation for decidable equality.
- HahnFun.v : functional update
- HahnFuneq.v : functional preservation properties of relations
- HahnList.v : lemmas about lists
- HahnMaxElt.v : maximal elements of a relation
- HahnMinElt.v : minimum elements of a relation
- HahnWf.v : well-founded and finitely supported relations
- HahnMinPath.v : minimal paths/cycles over relations
- HahnPath.v : paths over relations
- HahnRelationsBasic.v : binary relations
- HahnRewrite.v : support for rewriting equivalent relations
- HahnSets.v : lemmas about sets (i.e., unary relations)
- HahnSegment.v : lemmas about segments of total orders
- HahnSorted.v : lemmas about sortedness of lists 
- HahnTotalExt.v : extension of a partial order to a total order.
- HahnTotalList.v : building finite relations for program order.
- Zorn.v : A mechanization of Zorn's lemma (thanks to Johannes Kloos)

## Build

- Install [Coq](http://coq.inria.fr) 8.8 or above
- make

## Use

- In a Coq file, write "Require Import Hahn".
- Optionally, also "Require Import HahnExtraNotation".

