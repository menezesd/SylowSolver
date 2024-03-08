# Automating Sylow's Theorems

This project is an attempt to automate the process of proving that there are no simple groups of a given order by leveraging Sylow's theorems and related techniques from finite group theory.

## Overview

Nearly every introductory group theory course has a problem set with a series of problems of the form "prove that there are no simple groups of order n," for various values of n. While the specific details vary, nearly all of these problems can be solved by applying a relatively small set of techniques based on Sylow's theorems and some related arguments involving counting, embeddings into alternating groups, and normalizers of intersections of Sylow subgroups.

Since computers are excellent at applying logical rules systematically, it is natural to attempt to automate the process of solving these types of problems. This project represents an initial proof of concept in this direction.

## Implementation

The core idea is to encode various Sylow techniques as "theorem" objects that can be applied to a collection of established facts to derive new facts. For example, one theorem object directly applies Sylow's theorems to list out the possible numbers of Sylow p-subgroups for a given group order. Another theorem handles the counting argument based on the fact that Sylow p-subgroups of prime order must have trivial intersection.

These theorem objects are composed into a simple theorem prover that maintains a collection of established facts and repeatedly applies the theorems to derive new facts. If a contradiction is ever derived (encoded as the "false" fact), then the theorem prover has successfully shown there are no simple groups of the given order.

While the current implementation is fairly basic, combining just a handful of standard Sylow techniques, it demonstrates the potential for further automating arguments in finite group theory by encoding more sophisticated techniques as theorem objects.

## Usage

python auto2.py

