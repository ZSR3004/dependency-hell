# Formalized Problem

## Actual Problem
### Input:
    - Current status of packages on the system
    - A *universe* of all available packages
    - User request (such as `apt install package` or `apt upgrade package`)
    - User prefrences (certain package managers allow users to make contraints such as minimizing the number of packages installed)

### Output:
    - Upgrade plan: Partially ordered list of instructions to acheive the new desired state.
            - Managers either store the steps to upgrade the package, then walk thorugh it or return an error saying it is not possible.

## Simplified Problem for Implementation

## Notes on How I Simplified the Problem

Based on what I have read, updating a package and installing it have a similar process. Naively, upgrading a package to version 3 
is the same as installing version 3 of the package. So, we will focus on updating packages, since that will require fewer operations (leading
to smaller CNFs because there are fewer packages for Alloy to model the installation of).
Further, we will restrict upgrading to a single package because while upgrading all packages is a similar problem to upgrading all packages, 
exploring optimization of single package upgrading is more interesting than modeling multi-package upgrades.

We also will not include the ENTIRE universe of packages, instead only including the ones that will be installed or upgraded.

This simplification restricts user input to one command type: `update package`. User preferences will act as the optimization, so that will
also not be an input, but rather assertions for optimized outputs.

### Input

    - Current status of packages on the system (graph, described below)
    - Only relevant packages, depending on the user request
    - The package to be upgraded

## Output
    - Upgrade plan execution: Using Alloy's state module. Either it resturns an instance of a valid upgrade or finds no instances.

## Assertions Related to Ensuring Correct Encoding
We will assert the following to ensure that our implementation is valid and consistent with how package managers like Debian's 
apt works.
    - A package can have zero or more packages (with or without specifying a version) as dependencies
    - To install a package all dependencies must be installed
    - Each version can have different dependencies
    - Two different versions of a package cannot be installed at once

## Assertions of Optimization 

We want to find the optimal solution with respect to a number of criteria. I will begin those listed below, and if they are not
deemed sufficiently complex or if I have time, I will implement more.
    - Maximize the version number of the package
    - Minimize the number of packages to be installed (memory optimization)
    - Minimize the number of packages that need to be updated (time optimization)

## Implementation

We generate a graph for which each vertex has two sets of edges, compatible and
incompatible edges.

```alloy
// This is the general package type. For instance, this might represent
// Git, but not a particular git version. This representation allows us
// to group all versions of Git together.
sig Package {}

// This holds a "Concrete Package", which is a specfic instance of a
// package. Namely, this one has a version (ie. Git v1). 
//
// pkg: The abstract package that this is concrete form of.
// ver: The particular version of this concrete package.
// install: True if installed on the user's system.
// locked: True if we do not let the package manager upgrade this version.
// dependencies: The set of versions that must be installed for this package
//               to work.
// incompatible: The set of versions that cannot be installed at the same time as
//               this package.
sig Version {
    pkg:          one Package,
    ver:          Int,

    installed:    Bool,
    locked:       Bool,

    dependencies: set Version,
    incompatible: set Version 
}
```
