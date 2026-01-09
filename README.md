# Dependency Hell

**NOTE**: This project was me chasing a curiosity. I wasn't originally intending to share this with others, but I 
figured that Alloy Tools (more on it below) was an interesting tool that not enough people know about.

I was introduced to [Alloy Tools](https://alloytools.org) in a University class. The tool itself is a little niche, so 
I'll briefly explain what it is. In short, Alloy Tools allows is a code editor and programming language that let's you
formalize (logic) problems and verify solutions to them.

An easy example to give is for the [Bridge and Torch Problem](https://en.wikipedia.org/wiki/Bridge_and_torch_problem).
Alloy Tools let's you define the problem, then write a strategy. The strength of the program is that it lets you test
various strategies and once you've found what you think is the optimal one, it can help you prove that it is.

Under the hood, Alloy Tools takes your formalization and uses a [SAT Solver](https://en.wikipedia.org/wiki/SAT_solver)
to test your hypothesis. If you don't know a SAT Solver is just a computer program used to solve logical puzzles.
Basically, SAT Solvers already allow computers to solve logic puzzles. Alloy Tools enters the picture to help 
scientists and engineers turn the problem at hand to a computer readable logical puzzle.

For this project, I modeled package manager, much like `apt-get` or `pacman` found on various Linux distributions. You
can read more about my motivation and how I formalized and verified by model in the
[`dependency_hell.pdf`]() file.

The core project is in 
[`dependency_hell.als`](https://github.com/ZSR3004/dependency-hell/blob/main/dependency_hell.als) which is the Alloy Tools plain-text file. I have also included 
Alloy 
themes which will help you visualize what the package manager is doing. The themes you can create in Alloy aren't super
complex, so these themes work best on very simple inputs to build an intuition of what's happening.

Check out the [Alloy Tools Website](https://alloytools.org/download.html) for information on how to install the 
program and the [Alloy Tools Documentation](https://alloytools.org/documentation.html) on how to actually run it! The 
docs do a fairly good job explaining the basics, but Alloy Tools is still pretty young, so might want to supplement 
them with some Googling.
